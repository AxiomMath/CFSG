module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStage

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV

variable {D : Type*} [Group D] [Finite D] {R X U P : Subgroup D} {n : ℕ}

theorem smallRoot_sylow_alternative (h : SmallRootStage R X U P n) :
    (∀ g : D, CFSG.conjugate (U ⊔ R) g ≤ P → CFSG.conjugate (U ⊔ R) g = U ⊔ R) ∧
    (((∃ S : Sylow 2 D, (S : Subgroup D) = P) ∧
        IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D)) ∨
      ((¬ ∃ S : Sylow 2 D, (S : Subgroup D) = P) ∧
        3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)) := by
  obtain ⟨hweak, halt, -⟩ :=
    SteinbergBV.gms_normal_root_at_most_two_conjugates_sylow_alternatives h.1
  refine ⟨hweak, ?_⟩
  rcases halt with h1 | ⟨P₁, -, -, -, -, -, ⟨y, -, hyU, -⟩, -⟩ | h3
  · exact Or.inl h1
  · exfalso
    have hUcard : Nat.card U = 2 ^ n := h.1.2.2.2.2.1.2.2.2
    have hRU : Nat.card R = 2 ^ n := by
      rw [← hyU, card_map_of_injective (f := (MulAut.conj y).toMonoidHom)
        (MulAut.conj y).injective, hUcard]
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.three_le
    rw [h.card_eq_two] at hRU
    omega
  · exact Or.inr h3

theorem SmallRootStage.three_le_of_not_sylow (h : SmallRootStage R X U P n)
    (hP : ¬ ∃ S : Sylow 2 D, (S : Subgroup D) = P) :
    3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard := by
  rcases (smallRoot_sylow_alternative h).2 with h1 | h1
  · exact absurd h1.1 hP
  · exact h1.2

end CFSG.SeitzReduction.RankOne
