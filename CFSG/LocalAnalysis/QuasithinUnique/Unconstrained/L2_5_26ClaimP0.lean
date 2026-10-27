module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

namespace Core

theorem sq_invol_zb : p0Lit.all (fun p => !(cmul (cmul p p) (cmul p p) == cid) || cmul p p == cid ||
    cmul p p == zbC) = true := by
  decide +kernel

end Core

theorem P0_sq_eq_one_or_zb {p : P10} (hp : p ∈ P0) (h : (p * p) * (p * p) = 1) :
    p * p = 1 ∨ p * p = zb := by
  have hall := Core.sq_invol_zb
  rw [List.all_eq_true] at hall
  have h1 := hall (code p) ((mem_P0_iff p).1 hp)
  have hc : (Core.cmul (Core.cmul (code p) (code p)) (Core.cmul (code p) (code p)) == Core.cid) =
      true := by
    rw [beq_iff_eq, ← code_mul, ← code_mul, h, code_one]
  simp only [hc, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h2 | h2
  · left
    apply code_injective
    rw [code_mul, code_one]
    exact h2
  · right
    apply code_injective
    rw [code_mul, zb_code]
    exact h2

end CFSG.QuasithinUnique.A6Facts
