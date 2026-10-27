module

public import CFSG.GH74.E2.KTables

public section

namespace CFSG.GH74.E2

structure Sz8Facts : Prop where
  autRank_ge5 : ∀ (K : Type) [Group K] [Finite K], ShapeSz8 K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup (MulAut K), ElemAb p B → Nat.card B ≤ p
  autRank3_le_two : ∀ (K : Type) [Group K] [Finite K], ShapeSz8 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 9
  autRank3_le_one : ∀ (K : Type) [Group K] [Finite K], ShapeSz8 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 3
  fixed_solvable : ∀ (K : Type) [Group K] [Finite K], ShapeSz8 K → ∀ α : MulAut K, α ^ 2 = 1 →
    α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → Group.IsSolvable ↥L

structure TwoM12Facts : Prop where
  autRank_ge5 : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup (MulAut K), ElemAb p B → Nat.card B ≤ p
  autRank3_le_two : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 9
  autCentralizer : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R = 9 → ∀ ψ : MulAut K, ψ ^ 2 = 1 →
      (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1
  pumpUp : ∀ (K : Type) [Group K] [Finite K], Shape2M12 K → ∀ α : MulAut K, α ^ 2 = 1 →
    α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → IsQuasisimple ↥L →
      Nat.card ↥L = 60 ∨ Nat.card ↥L = 120

structure TwoSz8Facts : Prop where
  autRank_ge5 : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ B : Subgroup (MulAut K), ElemAb p B → Nat.card B ≤ p
  autRank3_le_two : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 9
  autRank3_le_one : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K →
    ∀ R : Subgroup (MulAut K), ElemAb 3 R → Nat.card R ≤ 3
  rank_ge4_sz : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K →
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U
  fixed_false : ∀ (K : Type) [Group K] [Finite K], Shape2Sz8 K → ∀ α : MulAut K, α ^ 2 = 1 →
    α ≠ 1 → ∀ L : Subgroup K, (∀ x ∈ L, α x = x) → IsQuasisimple ↥L → False

theorem k0Rest2_of (h1 : Sz8Facts) (h2 : TwoM12Facts) (h3 : TwoSz8Facts) : K0Rest2 where
  autRank_ge5 := by
    intro K _ _ hK p hp h5 B hB
    rcases hK with hK | hK | hK
    · exact h1.autRank_ge5 K hK p hp h5 B hB
    · exact h2.autRank_ge5 K hK p hp h5 B hB
    · exact h3.autRank_ge5 K hK p hp h5 B hB
  autRank3_le_two := by
    intro K _ _ hK R hR
    rcases hK with hK | hK | hK
    · exact h1.autRank3_le_two K hK R hR
    · exact h2.autRank3_le_two K hK R hR
    · exact h3.autRank3_le_two K hK R hR
  autRank3_le_one := by
    intro K _ _ hK R hR
    rcases hK with hK | hK
    · exact h1.autRank3_le_one K hK R hR
    · exact h3.autRank3_le_one K hK R hR
  rank_ge4_sz := h3.rank_ge4_sz
  autCentralizer := h2.autCentralizer
  pumpUp := by
    intro K _ _ hK α hα2 hα1 L hL hq
    rcases hK with hK | hK | hK
    · exact absurd (h1.fixed_solvable K hK α hα2 hα1 L hL)
        (CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq)
    · exact ⟨h2.pumpUp K hK α hα2 hα1 L hL hq, hK⟩
    · exact (h3.fixed_false K hK α hα2 hα1 L hL hq).elim

end CFSG.GH74.E2
