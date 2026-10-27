module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6NI
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Four

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section Pairs

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_pair_of_klein_not_inn (hF : L2Field F) (e : K ≃* L2 F) {E : Subgroup (MulAut K)}
    (hE4 : Nat.card ↥E = 4) (hEsq : ∀ a ∈ E, a ^ 2 = 1) (hnI : ¬ E ≤ innAut K) :
    (∃ z ∈ E, ∃ w ∈ E, z ≠ 1 ∧ z ∈ innAut K ∧ w ∈ innDiagSub e ∧ w ∉ innAut K) ∨
    (∃ f₁ ∈ E, ∃ f₂ ∈ E, f₁ ∉ innDiagSub e ∧ f₂ ∉ innDiagSub e ∧ f₁ ≠ f₂) := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := CFSG.QuasithinUnique.Unc25Small.exists_two_nonid hE4
  have hmul : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → x ≠ y → x * y ≠ 1 := by
    intro x hx y hy hx1 hy1 hxy h
    apply hxy
    have h1 : y * y = 1 := by rw [← pow_two]; exact hEsq y hy
    exact mul_right_cancel (h.trans h1.symm)
  by_cases hX : E ≤ innDiagSub e
  · left
    obtain ⟨c, hcE, hcI⟩ := IsConcreteLE.not_le_iff_exists.1 hnI
    have hc1 : c ≠ 1 := fun h => hcI (by rw [h]; exact one_mem _)
    obtain ⟨d, hdE, hd1, hdc⟩ : ∃ d ∈ E, d ≠ 1 ∧ c ≠ d := by
      by_cases hac : a = c
      · exact ⟨b, hb, hb1, fun h => hab (hac.trans h)⟩
      · exact ⟨a, ha, ha1, fun h => hac h.symm⟩
    by_cases hdI : d ∈ innAut K
    · exact ⟨d, hdE, c, hcE, hd1, hdI, hX hcE, hcI⟩
    · refine ⟨c * d, E.mul_mem hcE hdE, c, hcE, hmul c hcE d hdE hc1 hd1 hdc,
        mul_mem_innAut_of_not_mem hF e (hX hcE) (hX hdE) hcI hdI, hX hcE, hcI⟩
  · right
    obtain ⟨f₁, hf₁E, hf₁X⟩ := IsConcreteLE.not_le_iff_exists.1 hX
    have hf₁1 : f₁ ≠ 1 := fun h => hf₁X (by rw [h]; exact one_mem _)
    obtain ⟨d, hdE, hd1, hdf⟩ : ∃ d ∈ E, d ≠ 1 ∧ f₁ ≠ d := by
      by_cases hac : a = f₁
      · exact ⟨b, hb, hb1, fun h => hab (hac.trans h)⟩
      · exact ⟨a, ha, ha1, fun h => hac h.symm⟩
    by_cases hdX : d ∈ innDiagSub e
    · refine ⟨f₁, hf₁E, f₁ * d, E.mul_mem hf₁E hdE, hf₁X, fun h => hf₁X ?_, ?_⟩
      · have : f₁ = (f₁ * d) * d⁻¹ := by group
        rw [this]
        exact (innDiagSub e).mul_mem h ((innDiagSub e).inv_mem hdX)
      · intro h
        apply hd1
        have : f₁ * d = f₁ * 1 := by rw [mul_one]; exact h.symm
        exact mul_left_cancel this
    · exact ⟨f₁, hf₁E, d, hdE, hf₁X, hdX, hdf⟩

end Pairs

end CFSG.GH74.GLS.IVK.Proofs2
