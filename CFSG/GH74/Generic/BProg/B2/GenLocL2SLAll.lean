module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2Fam

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint
open scoped MatrixGroups

theorem gammaAct_sl2_of_ge11
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h11 : 11 ≤ p ^ f) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (SL(2, K))) (hA : IsRank23 A) : gammaAct α = ⊤ := by
  have hq : ¬ (p ^ f ∈ ({5, 7, 9} : Finset ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  rcases hA.2 with hk | hk
  · exact gammaAct_sl2_rank2 hp hp2 hK (by omega) α hA hk (fun h => hq h.1)
  · by_cases h25 : 25 ≤ p ^ f
    · exact gammaAct_sl2_rank3 hp hp2 hK h25 α hA hk
    · exact gammaAct_sl2_rank3_lt25 hp hp2 hK h11 (by omega) α hA hk

end CFSG.GH74.Generic.BProg.B2
