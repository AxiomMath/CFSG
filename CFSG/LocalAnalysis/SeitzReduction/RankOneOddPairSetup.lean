module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneDegreeEight

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX

section GMS

variable {D : Type} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem card_gmsPermStabilizer_eq_mul_card_pairStabilizer [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (β : gmsRootConjugates (U ⊔ R) R) (hβ : (β : Subgroup D) ≠ R) :
    Nat.card (gmsPermStabilizer U R) = (2 ^ n - 1) * Nat.card (gmsPairStabilizer U R β) := by
  rw [card_gmsPermStabilizer h h3, (gms_pairStabilizer_structure h h3 β hβ (X := X)).2.2.1]

theorem odd_card_gmsPermStabilizer_of_odd [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (β : gmsRootConjugates (U ⊔ R) R) (hβ : (β : Subgroup D) ≠ R)
    (hodd : Odd (Nat.card (gmsPairStabilizer U R β))) :
    Odd (Nat.card (gmsPermStabilizer U R)) ∧
      Nat.card (gmsPermStabilizer U R) ∣ (2 ^ n - 1) * n := by
  have hn : 1 ≤ n := le_trans (by norm_num) h.1
  have hq : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  rw [card_gmsPermStabilizer_eq_mul_card_pairStabilizer h h3 β hβ]
  exact ⟨hq.mul hodd,
    Nat.mul_dvd_mul_left _ (gms_pairStabilizer_structure h h3 β hβ (X := X)).2.2.2.2⟩

end GMS

end CFSG.SeitzReduction.RankOne
