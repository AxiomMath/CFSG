module

public import CFSG.FeitThompson.OddOrder.PrimeFieldScalarNormOneUnits

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {p q : ℕ} {F : Type*} [Field F]

theorem eq_top_of_mul_mem_of_pow_eq_one (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {V : Submodule (⊥ : Subfield F) F} (hV : V ≠ ⊥)
    (hU : ∀ u : F, u ≠ 0 → u ^ ((p ^ q - 1) / (p - 1)) = 1 → ∀ x ∈ V, u * x ∈ V) :
    V = ⊤ := by
  obtain ⟨v, hvV, hv0⟩ := (Submodule.ne_bot_iff V).1 hV
  refine Submodule.eq_top_iff'.2 fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · exact V.zero_mem
  obtain ⟨⟨c, u⟩, ⟨⟨hc, -⟩, ⟨hu0, hu⟩, hcu⟩, -⟩ :=
    existsUnique_mul_eq hp h hcop (z := z / v) (div_ne_zero hz hv0)
  have hmem : (⟨c, hc⟩ : (⊥ : Subfield F)) • (u * v) ∈ V := V.smul_mem _ (hU u hu0 hu v hvV)
  have hz' : c * (u * v) = z := by rw [← mul_assoc, hcu]; field_simp
  rwa [show ((⟨c, hc⟩ : (⊥ : Subfield F)) • (u * v)) = c * (u * v) from rfl, hz'] at hmem

theorem eq_top_of_smul_eq_self (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {V : Submodule (⊥ : Subfield F) F} (hV : V ≠ ⊥)
    (hU : ∀ u : Fˣ, u ∈ normOneUnits F → (u : F) • V = V) :
    V = ⊤ :=
  eq_top_of_mul_mem_of_pow_eq_one hp h hcop hV fun u hu0 hu x hx => by
    rw [← hU (Units.mk0 u hu0) ((mem_normOneUnits_iff_pow_eq_one hp h _).2 hu)]
    exact Submodule.smul_mem_pointwise_smul x _ V hx

theorem eq_bot_or_eq_top_of_smul_eq_self (hp : p.Prime) (h : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    {V : Submodule (⊥ : Subfield F) F}
    (hU : ∀ u : Fˣ, u ∈ normOneUnits F → (u : F) • V = V) :
    V = ⊥ ∨ V = ⊤ :=
  (eq_or_ne V ⊥).imp id fun hV => eq_top_of_smul_eq_self hp h hcop hV hU

end

end CFSG.FeitThompson
