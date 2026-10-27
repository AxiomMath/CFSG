module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.QuasithinUnique.A6Facts.Core

@[expose] def zbC : List Nat := [9, 1, 2, 6, 5, 4, 3, 8, 7, 0]

@[expose] def e4Lit : List (List Nat) :=
  p0Lit.filter fun c => dLit.all fun d => cmul c d == cmul d c

@[expose] def kleinOf (r : List Nat) : List (List Nat) := [cid, zbC, r, cmul r zbC]

@[expose] def isRefl (r : List Nat) : Bool :=
  dLit.contains r && r != cid && r != zbC && cmul r r == cid

@[expose] def kleinCent (r : List Nat) : List (List Nat) :=
  p0Lit.filter fun q => cmul q r == cmul r q && cmul q zbC == cmul zbC q

theorem zb_central : p0Lit.contains zbC = true ∧ (zbC != cid) = true ∧
    p0Lit.all (fun p => cmul zbC p == cmul p zbC) = true := by
  decide +kernel

theorem center_p0 : p0Lit.all (fun a => !(p0Lit.all fun p => cmul a p == cmul p a) || a == cid ||
    a == zbC) = true := by
  decide +kernel

theorem zb_mem_d : dLit.contains zbC = true := by decide +kernel

theorem zb_sq : cmul zbC zbC = cid := by decide +kernel

theorem squares_in_d : p0Lit.all (fun p => dLit.contains (cmul p p)) = true := by decide +kernel

theorem fourth_powers : p0Lit.all (fun p => cpow p 4 == cid || cpow p 4 == zbC) = true := by
  decide +kernel

theorem fourth_exists : p0Lit.any (fun p => cpow p 4 == zbC) = true := by decide +kernel

theorem e4_inter_d : e4Lit.all (fun c => !dLit.contains c || c == cid || c == zbC) = true := by
  decide +kernel

theorem e4_not_d : e4Lit.any (fun b => !dLit.contains b) = true := by decide +kernel

theorem e4_shape : e4Lit.all (fun b => dLit.contains b || e4Lit.all fun c =>
    c == cid || c == zbC || c == b || c == cmul b zbC) = true := by
  decide +kernel

theorem klein_cent_aut : dLit.all (fun r => !isRefl r || e4Lit.all (fun b => dLit.contains b ||
    autL.all (fun q => !(cmul q r == cmul r q && cmul q zbC == cmul zbC q) ||
      (p0Lit.contains q && ((kleinOf r).contains q || (kleinOf r).any fun e => cmul e b == q))))) =
      true := by
  decide +kernel

theorem conj_zb : dLit.all (fun a => a == cid || !(cmul a a == cid) ||
    pslLit.any fun g => cmul g zbC == cmul a g) = true := by
  decide +kernel

theorem d_klein_zb : dLit.all (fun a => a == cid || !(cmul a a == cid) || dLit.all fun b =>
    b == cid || b == a || !(cmul b b == cid) || !(cmul a b == cmul b a) || a == zbC || b == zbC ||
      cmul a b == zbC) = true := by
  decide +kernel

theorem klein_cent_comm : dLit.all (fun r => !isRefl r || (kleinCent r).all fun q =>
    (kleinCent r).all fun q' => cmul q q' == cmul q' q) = true := by
  decide +kernel

theorem d_nonabelian : dLit.any (fun d => dLit.any fun d' => !(cmul d d' == cmul d' d)) = true := by
  decide +kernel

theorem refl_of_good : p0Lit.all (fun g => g == cid || !(cmul g g == cid) ||
    !(pslLit.contains g || inS6 g) || e4Lit.contains g ||
    dLit.any fun r => isRefl r && p0Lit.all fun q => !(cmul q g == cmul g q) ||
      cmul q r == cmul r q) = true := by
  decide +kernel

end CFSG.QuasithinUnique.A6Facts.Core
