module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOEmbed
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOSplit
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPOBlock

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open

theorem two_ne_zero_of_natCard_eq_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) :
    (2 : K) ≠ 0 :=
  CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K (by rw [hK]; decide)

theorem hasPOmegaMember_of_lieModel_pomegaOdd {Q : Type} [Group Q] [IsSimpleGroup Q] {n : ℕ}
    (hn : 4 ≤ n) (h : CFSG.Blueprint.LieModel Q .POmegaOdd n 3 1) : HasPOmegaMember Q := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := (h.statedClassicalModel (by decide)).2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hK3 : Nat.card K = 3 := by rwa [pow_one] at hK
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd (m + 4) K))) :=
    MulEquiv.isSimpleGroup e.symm
  exact HasPOmegaMember.of_mulEquiv e.symm (hasPOmegaMember_statedProj_of_split
    (two_ne_zero_of_natCard_eq_three hK3) (poSplitD m Unit) (pullQ_poSplitOdd m)
    (neg_one_mem_statedOmega_quadPlus_four hK3) (pomegaBlock_statedOmega_quadPlus_four hK3))

theorem hasPOmegaMember_of_lieModel_pomegaPlus {Q : Type} [Group Q] [IsSimpleGroup Q] {n : ℕ}
    (hn : 5 ≤ n) (h : CFSG.Blueprint.LieModel Q .POmegaPlus n 3 1) : HasPOmegaMember Q := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := (h.statedClassicalModel (by decide)).2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have hK3 : Nat.card K = 3 := by rwa [pow_one] at hK
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus (m + 4) K))) :=
    MulEquiv.isSimpleGroup e.symm
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  exact HasPOmegaMember.of_mulEquiv e.symm (hasPOmegaMember_statedProj_of_split
    (two_ne_zero_of_natCard_eq_three hK3) (poSplitPlus m) (pullQ_poSplitPlus m)
    (neg_one_mem_statedOmega_quadPlus_four hK3) (pomegaBlock_statedOmega_quadPlus_four hK3))

theorem hasPOmegaMember_of_lieModel_pomegaMinus {Q : Type} [Group Q] [IsSimpleGroup Q] {n : ℕ}
    (hn : 5 ≤ n) (h : CFSG.Blueprint.LieModel Q .POmegaMinus n 3 1) : HasPOmegaMember Q := by
  obtain ⟨K, hF, hfin, hK, b, c, -, ⟨e⟩⟩ := (h.statedClassicalModel (by decide)).2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hK3 : Nat.card K = 3 := by rwa [pow_one] at hK
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus (m + 5) K b c))) :=
    MulEquiv.isSimpleGroup e.symm
  exact HasPOmegaMember.of_mulEquiv e.symm (hasPOmegaMember_statedProj_of_split
    (two_ne_zero_of_natCard_eq_three hK3) (poSplitMinus m) (pullQ_poSplitMinus m b c)
    (neg_one_mem_statedOmega_quadPlus_four hK3) (pomegaBlock_statedOmega_quadPlus_four hK3))

theorem hasPOmegaMember_of_lieModel_pomega {Q : Type} [Group Q] [IsSimpleGroup Q]
    {τ : StatedLieTag} {n : ℕ}
    (hτ : (τ = .POmegaOdd ∧ 4 ≤ n) ∨ (τ = .POmegaPlus ∧ 5 ≤ n) ∨ (τ = .POmegaMinus ∧ 5 ≤ n))
    (h : CFSG.Blueprint.LieModel Q τ n 3 1) : HasPOmegaMember Q := by
  rcases hτ with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · exact hasPOmegaMember_of_lieModel_pomegaOdd hn h
  · exact hasPOmegaMember_of_lieModel_pomegaPlus hn h
  · exact hasPOmegaMember_of_lieModel_pomegaMinus hn h

end CFSG.OddStandard.HigherRank.F3
