module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsClasses
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.QuasithinUnique.A6Facts.Core

@[expose] def ordC (c : List Nat) : Nat :=
  if c == cid then 1 else if cmul c c == cid then 2 else if cpow c 4 == cid then 4 else 8

@[expose] def masksOf : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masksOf n).flatMap fun m => [false :: m, true :: m]

@[expose] def maskU (m : List Bool) : List (List Nat) :=
  (List.range 11).flatMap fun k => if m.getD k false then p0Classes.getD k [] else []

@[expose] def maskClosed (m : List Bool) : Bool :=
  m.getD 0 false &&
    (List.range 11).all fun i => !(m.getD i false) || (List.range 32).all fun j =>
      !(m.getD (p0ClsIdx.getD j 0) false) || m.getD ((p0ProdTab.getD i []).getD j 0) false

@[expose] def maskType (m : List Bool) : Nat × Nat × Nat × Nat :=
  ((maskU m).length, ((maskU m).filter fun c => ordC c == 2).length,
    ((maskU m).filter fun c => ordC c == 4).length, ((maskU m).filter fun c => ordC c == 8).length)

theorem p0Classes_length : p0Classes.length = 11 := by decide +kernel

theorem cls_idx_spec : (List.range 32).all (fun j => decide (p0ClsIdx.getD j 0 < 11) &&
    (p0Classes.getD (p0ClsIdx.getD j 0) []).contains (p0Lit.getD j [])) = true := by
  decide +kernel

theorem prod_tab_spec : (List.range 11).all (fun i => (List.range 32).all (fun j =>
    decide ((p0ProdTab.getD i []).getD j 0 < 11) &&
      (p0Classes.getD ((p0ProdTab.getD i []).getD j 0) []).contains
        (cmul ((p0Classes.getD i []).headD []) (p0Lit.getD j [])))) = true := by
  decide +kernel

theorem cls_orbit : p0Classes.all (fun cl => cl.all (fun c => cl.all (fun c' =>
    p0Lit.any (fun g => cmul g c == cmul c' g)))) = true := by
  decide +kernel

theorem cls_sub : p0Classes.all (fun cl => cl.all (fun c => p0Lit.contains c)) = true := by
  decide +kernel

theorem cls_zero : (p0Classes.getD 0 []).contains cid = true := by decide +kernel

theorem cls_head : p0Classes.all (fun cl => cl.contains (cl.headD [])) = true := by
  decide +kernel

theorem mask_types : (masksOf 11).all (fun m =>
    !maskClosed m || ((maskU m).Nodup && p0Types.contains (maskType m))) = true := by
  decide +kernel

@[expose] def arithBad (t : Nat × Nat × Nat × Nat) (p b f2 f4 : Nat) : Bool :=
  decide (2 ^ b < t.1 ∧ 1 + f2 + f4 ≤ 2 ^ b ∧ f2 ≤ t.2.1 ∧ f4 ≤ t.2.2.1 ∧ (t.1 - 2 ^ b) % p = 0 ∧
    t.2.1 % p = f2 % p ∧ t.2.2.1 % p = f4 % p ∧ t.2.2.2 % p = (2 ^ b - 1 - f2 - f4) % p ∧
    2 ^ b - 1 - f2 - f4 ≤ t.2.2.2 ∧ (2 ^ b = 1 ∨ 1 ≤ f2) ∧
    (2 ^ b - 1 - f2 - f4 = 0 ∨ 8 ≤ 2 ^ b) ∧ (f4 = 0 ∨ 4 ≤ 2 ^ b))

theorem p0Types_bound : p0Types.all (fun t => decide (t.1 ≤ 32) && decide (t.2.1 < 17) &&
    decide (t.2.2.1 < 9) && decide (t.2.2.2 < 9)) = true := by
  decide +kernel

theorem arith_excl : p0Types.all (fun t => [5, 7, 11, 13, 17, 19, 23, 29, 31].all (fun p =>
    (List.range 6).all (fun b => (List.range 17).all (fun f2 => (List.range 9).all (fun f4 =>
      !arithBad t p b f2 f4))))) = true := by
  decide +kernel

end CFSG.QuasithinUnique.A6Facts.Core
