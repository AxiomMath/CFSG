module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X}

theorem L210_normal_two_subgroup (S : Sylow 2 X) (hSN : (S : Subgroup X) ≤ normalizer (A : Set X))
    (hirr : ∀ B : Subgroup X, B ≤ A →
      (∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) → B = ⊥ ∨ B = A)
    (hcent : ∀ x ∈ normalizer (A : Set X), (∀ a ∈ A, x * a = a * x) → x ∈ A)
    (hO2 : ∀ P : Subgroup X, A ≤ P → P ≤ normalizer (A : Set X) →
      (∀ n ∈ normalizer (A : Set X), ∀ p ∈ P, n * p * n⁻¹ ∈ P) → IsPGroup 2 P → P = A)
    {P : Subgroup X} [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ ∨ P = A := by
  have hPS : P ≤ (S : Subgroup X) := IsPGroup.le_sylow_of_normal hP S
  have hPN : P ≤ normalizer (A : Set X) := hPS.trans hSN
  have hinvP : ∀ n ∈ normalizer (A : Set X), ∀ p ∈ P, n * p * n⁻¹ ∈ P :=
    fun n _ p hp => (inferInstance : P.Normal).conj_mem p hp n
  by_cases hAP : A ≤ P
  · exact Or.inr (hO2 P hAP hPN hinvP hP)
  · refine Or.inl ((Subgroup.eq_bot_iff_forall (H := P)).mpr fun p hp => ?_)
    have hinvPA : ∀ n ∈ normalizer (A : Set X), ∀ b ∈ P ⊓ A, n * b * n⁻¹ ∈ P ⊓ A := by
      intro n hn b hb
      exact Subgroup.mem_inf.mpr
        ⟨(inferInstance : P.Normal).conj_mem b hb.1 n,
          (Subgroup.mem_normalizer_iff.mp hn b).mp hb.2⟩
    rcases hirr (P ⊓ A) inf_le_right hinvPA with hbot | htop
    · have hpN : p ∈ normalizer (A : Set X) := hPN hp
      have hcomm : ∀ a ∈ A, p * a = a * p := by
        intro a ha
        have hcP : p * a * p⁻¹ * a⁻¹ ∈ P := by
          convert mul_mem hp ((inferInstance : P.Normal).conj_mem p⁻¹ (inv_mem hp) a) using 1
          group
        have hcA : p * a * p⁻¹ * a⁻¹ ∈ A :=
          mul_mem ((Subgroup.mem_normalizer_iff.mp hpN a).mp ha) (inv_mem ha)
        have hc1 : p * a * p⁻¹ * a⁻¹ = 1 :=
          Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hcP, hcA⟩)
        exact mul_inv_eq_one.mp (by convert hc1 using 1; group)
      have hpmem : p ∈ P ⊓ A := Subgroup.mem_inf.mpr ⟨hp, hcent p hpN hcomm⟩
      exact Subgroup.mem_bot.mp (hbot ▸ hpmem)
    · exact absurd (htop ▸ inf_le_left) hAP

end CFSG.EvenSporadicStandard.HNRecog.Harada
