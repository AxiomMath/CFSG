module

public import CFSG.LieType.SeitzGeneration.SpF2.ConfigPair

public section

namespace CFSG.LieType.SeitzGeneration.SpF2

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LieType.SeitzGeneration.RootPair

variable {r : ℕ} {K : Type} [Field K]

theorem exists_config [CharP K 2] [Finite K] [NeZero r] {k : Subfield K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hr : 2 ≤ r) (A : gsp r K)
    (hne : (spSub r k).map (conjSp r K A).toMonoidHom ≠ spSub r k) :
    ∃ (a₀ a₀'' : Fin r ⊕ Fin r → k) (b : Fin r ⊕ Fin r → K),
      spForm r K (ratVec a₀) (ratVec a₀'') = 0 ∧ spForm r K (ratVec a₀) b ≠ 0 ∧
      spForm r K (ratVec a₀'') b / spForm r K (ratVec a₀) b ∉ k ∧
      spTransvection b 1 ∈ (spSub r k).map (conjSp r K A).toMonoidHom := by
  obtain ⟨ν, hν⟩ : ∃ ν : K, ν * ν = (((multiplier r K A)⁻¹ : Kˣ) : K) := by
    obtain ⟨ν, h⟩ := isSquare_of_charTwo' (((multiplier r K A)⁻¹ : Kˣ) : K)
    exact ⟨ν, h.symm⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : Fin r ⊕ Fin r → k, ¬∃ (c : K) (u₀ : Fin r ⊕ Fin r → k),
      ν • (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        ratVec w₀) = c • ratVec u₀ := by
    by_contra hall
    push Not at hall
    apply hne
    refine Subgroup.eq_of_le_of_card_ge (conj_spSub_le hp hp2 hK A (sq_entry_mem A hν hall)) ?_
    rw [Subgroup.card_map_of_injective (conjSp r K A).injective]
  obtain ⟨i, j, hi, hj⟩ := exists_ratio_not_mem hw₀
  obtain ⟨a₀, a₀'', h0, h1, h2⟩ := exists_orth_pair hr hi hj
  exact ⟨a₀, a₀'', _, h0, h1, h2, spTransvection_mem_conj A hν w₀⟩

end CFSG.LieType.SeitzGeneration.SpF2
