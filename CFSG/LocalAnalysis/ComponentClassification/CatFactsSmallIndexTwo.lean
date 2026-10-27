module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup

variable {K G : Type*} [Group K] [Group G] (M : AutModel K G) (hPA : M.P ≤ M.A)
  (hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1)
include hPA hcent

theorem conj_injective_of_model : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  have h1 : (M.Φ (MulAut.conj z) : G) = 1 := by rw [hz]; exact M.Φ_one
  rw [Φ_conj M hPA hcent] at h1
  exact (mem_bot).2 (modelEmb_injective M (by rw [h1, map_one]))

theorem index_range_conj_eq_two [Finite K] (hcard : Nat.card M.A = 2 * Nat.card M.P) :
    (MulAut.conj : K →* MulAut K).range.index = 2 := by
  have hinn : Nat.card (MulAut.conj : K →* MulAut K).range = Nat.card K :=
    Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_model M hPA hcent)).symm.toEquiv
  have hP : Nat.card M.P = Nat.card K := Nat.card_congr M.e.symm.toEquiv
  have hpos : 0 < Nat.card K := Nat.card_pos
  have : Finite M.A := Nat.finite_of_card_ne_zero (by rw [hcard, hP]; omega)
  have : Finite (MulAut K) := Finite.of_equiv _ M.Φ.symm.toEquiv
  have h := index_mul_card (MulAut.conj : K →* MulAut K).range
  rw [M.card_mulAut, hcard, hinn, hP] at h
  nlinarith

theorem sup_zpowers_eq_top_of_not_mem [Finite K] (hcard : Nat.card M.A = 2 * Nat.card M.P)
    (α : MulAut K) (hα : α ∉ (MulAut.conj : K →* MulAut K).range) :
    (MulAut.conj : K →* MulAut K).range ⊔ zpowers α = ⊤ := by
  have h2 := index_range_conj_eq_two M hPA hcent hcard
  have hP : Nat.card M.P = Nat.card K := Nat.card_congr M.e.symm.toEquiv
  have hpos : 0 < Nat.card K := Nat.card_pos
  have : Finite M.A := Nat.finite_of_card_ne_zero (by rw [hcard, hP]; omega)
  have : Finite (MulAut K) := Finite.of_equiv _ M.Φ.symm.toEquiv
  set H := (MulAut.conj : K →* MulAut K).range
  have hle : H ≤ H ⊔ zpowers α := le_sup_left
  have hdvd : (H ⊔ zpowers α).index ∣ 2 := h2 ▸ index_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact index_eq_one.1 h
  · exfalso
    have heq : H = H ⊔ zpowers α :=
      eq_of_le_of_card_ge hle (by
        have h1 := index_mul_card H
        have h3 := index_mul_card (H ⊔ zpowers α)
        rw [h2] at h1
        rw [h] at h3
        omega)
    have hmem : α ∈ H ⊔ zpowers α := (le_sup_right : zpowers α ≤ H ⊔ zpowers α) (mem_zpowers α)
    rw [← heq] at hmem
    exact hα hmem

end CFSG.ComponentClassification.CatFactsSmall
