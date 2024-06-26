(* solve LP and MILP using glpk *)
open! Core
module C = Ctypes
module T = Lp_glpk_types.M
module B = Lp_glpk_ffi.M
open Lp

let make_pmap vars f =
  List.fold_left
    ~f:(fun m (k, v) -> Lp.PMap.add k v m)
    ~init:Lp.PMap.empty
    (List.mapi ~f:(fun i v -> (Poly.of_var v, f i)) vars)

(* NOTE on array indexing
 * glpk's API treats Carray as 1-origin! Conventions in C are:
 * - declare a[n+1] instead of a[n] for an array of length n.
 * - ignore zero-th element a[0]. *)

(* get 1-origin index of v in vars (Var.t list) *)
let idx_var (v : Var.t) l =
  let indx = List.findi l ~f:(fun _ v' -> Stdlib.( = ) v' v) in
  match indx with
  | None ->
      failwith (Printf.sprintf "cannot find %s in vars" v.name)
  | Some (indx, _) ->
      indx + 1

let set_obj prob vars obj =
  if Objective.is_max obj then B.set_obj_dir prob T.Dir.MAX
  else B.set_obj_dir prob T.Dir.MIN ;
  Poly.iter_linear_exn
    (fun c v -> B.set_obj_coef prob (idx_var v vars) c)
    (Objective.to_poly obj)

let set_cnstr prob vars i cnstr =
  let ri = i + 1 in
  let coeff poly =
    let aindices = C.CArray.make C.int (1 + Poly.length poly) in
    let acoeffs = C.CArray.make C.double (1 + Poly.length poly) in
    let () =
      List.iteri
        ~f:(fun i v -> C.CArray.set aindices i v)
        (0 :: Poly.map_linear (fun _ v -> idx_var v vars) poly)
      (* 0-th element is dummy *)
    in
    let () =
      List.iteri
        ~f:(fun i v -> C.CArray.set acoeffs i v)
        (0.0 :: Poly.take_linear_coeffs poly)
      (* 0-th element is dummy *)
    in
    B.set_mat_row prob ri (Poly.length poly)
      (C.to_voidp (C.CArray.start aindices))
      (C.to_voidp (C.CArray.start acoeffs))
  in
  let lhs, rhs = Cnstr.sides cnstr in
  if Cnstr.is_eq cnstr then B.set_row_bnds prob ri T.Bnd.FX rhs 0.0
  else B.set_row_bnds prob ri T.Bnd.UP 0.0 rhs ;
  coeff lhs

let set_cnstrs prob vars = List.iteri ~f:(set_cnstr prob vars)

let ( =. ) = Float.equal

let ( <>. ) = Float.( <> )

module Simplex = struct
  let set_cols prob =
    List.iteri ~f:(fun j var ->
        let cj = 1 + j in
        match var with
        | {Var.attr= Var.Continuous (lb, ub); _} ->
            if lb =. Float.neg_infinity && ub =. Float.infinity then
              B.set_col_bnds prob cj T.Bnd.FR 0.0 0.0
            else if ub =. Float.infinity then
              B.set_col_bnds prob cj T.Bnd.LO lb 0.0
            else if lb =. Float.neg_infinity then
              B.set_col_bnds prob cj T.Bnd.UP 0.0 ub
            else if lb <>. ub then B.set_col_bnds prob cj T.Bnd.DB lb ub
            else B.set_col_bnds prob cj T.Bnd.FX lb ub
        | _ ->
            failwith "set_cols: integer variable found" )

  let solve_main p =
    let obj, cnstrs = Problem.obj_cnstrs p in
    let vars = Problem.uniq_vars p in
    let nrows = List.length cnstrs in
    let ncols = List.length vars in
    let prob = B.create_prob () in
    ignore @@ B.add_rows prob nrows ;
    ignore @@ B.add_cols prob ncols ;
    let smcp = C.make T.Smcp.t in
    try
      B.init_smcp (C.addr smcp) ;
      (* TODO set solver parameters *)
      set_obj prob vars obj ;
      set_cnstrs prob vars cnstrs ;
      set_cols prob vars ;
      let ret = B.simplex prob (C.addr smcp) in
      (* TODO handle some of non-zero return values *)
      if ret <> 0 then failwith "non-zero return value from simplex"
      else
        match B.get_status prob with
        | T.Stat.OPT ->
            let obj = B.get_obj_val prob in
            let xs = make_pmap vars (fun i -> B.get_col_prim prob (i + 1)) in
            B.delete_prob prob ;
            Ok (obj, xs)
        | status ->
            failwith ("Problem is " ^ T.Stat.to_string status)
    with Failure msg -> B.delete_prob prob ; Error msg

  let solve ?(term_output = true) p =
    match Problem.classify p with
    | Pclass.LP ->
        B.set_term_out term_output ; solve_main p
    | _ ->
        Error "Lp_glpk.Simplex is only for LP"
end

module Milp = struct
  let set_cols prob =
    let set_bounds cj lb ub =
      if lb =. Float.neg_infinity && ub =. Float.infinity then
        B.set_col_bnds prob cj T.Bnd.FR 0.0 0.0
      else if ub =. Float.infinity then B.set_col_bnds prob cj T.Bnd.LO lb 0.0
      else if lb =. Float.neg_infinity then
        B.set_col_bnds prob cj T.Bnd.UP 0.0 ub
      else if lb <>. ub then B.set_col_bnds prob cj T.Bnd.DB lb ub
      else B.set_col_bnds prob cj T.Bnd.FX lb ub
    in
    List.iteri ~f:(fun j var ->
        let cj = 1 + j in
        match var with
        | {Var.attr= Var.Continuous (lb, ub); _} ->
            set_bounds cj lb ub
        | {Var.attr= Var.General (lb, ub); _} ->
            set_bounds cj lb ub ;
            B.set_col_kind prob cj T.Vt.IV
        | {Var.attr= Var.Binary; _} ->
            set_bounds cj Float.zero Float.one ;
            B.set_col_kind prob cj T.Vt.BV )

  let solve_main p =
    let obj, cnstrs = Problem.obj_cnstrs p in
    let vars = Problem.uniq_vars p in
    let nrows = List.length cnstrs in
    let ncols = List.length vars in
    let prob = B.create_prob () in
    ignore @@ B.add_rows prob nrows ;
    ignore @@ B.add_cols prob ncols ;
    let smcp = C.make T.Smcp.t in
    let iocp = C.make T.Iocp.t in
    try
      B.init_smcp (C.addr smcp) ;
      B.init_iocp (C.addr iocp) ;
      (* TODO set solver parameters *)
      set_obj prob vars obj ;
      set_cnstrs prob vars cnstrs ;
      set_cols prob vars ;
      let ret = B.simplex prob (C.addr smcp) in
      (* TODO handle some of non-zero return values *)
      if ret <> 0 then failwith "non-zero return value from simplex"
      else
        match B.get_status prob with
        | T.Stat.OPT -> (
            let ret = B.intopt prob (C.addr iocp) in
            (* TODO handle some of non-zero return values *)
            if ret <> 0 then failwith "non-zero return value from intopt"
            else
              match B.mip_status prob with
              | T.Stat.OPT ->
                  let obj = B.mip_obj_val prob in
                  let xs =
                    make_pmap vars (fun i -> B.mip_col_val prob (i + 1))
                  in
                  B.delete_prob prob ;
                  Ok (obj, xs)
              | status ->
                  failwith ("MILP is " ^ T.Stat.to_string status) )
        | status ->
            failwith ("LP relaxation is " ^ T.Stat.to_string status)
    with Failure msg -> B.delete_prob prob ; Error msg

  let solve ?(term_output = true) p =
    match Problem.classify p with
    | Pclass.MILP ->
        B.set_term_out term_output ; solve_main p
    | _ ->
        Error "Lp_glpk.Milp is only for MILP"
end

let solve ?(term_output = true) p =
  match Problem.classify p with
  | Pclass.LP ->
      Simplex.solve ~term_output p
  | Pclass.MILP ->
      Milp.solve ~term_output p
  | _ ->
      Error "glpk is only for LP or MILP"
