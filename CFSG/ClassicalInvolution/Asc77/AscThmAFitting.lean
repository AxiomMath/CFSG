module

public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace AscThmA

open CFSG CFSG.Open CFSG.LocalCores

variable {G : Type} [Group G]

theorem fittingSubgroup_eq_bot_of_oddCore_of_pGroup [Finite G]
    (hO : classicalInvolutionOddCore G = ⊥)
    (h2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) : fittingSubgroup G = ⊥ := by
  rw [fittingSubgroup_eq_iSup_pCore, iSup_eq_bot]
  intro p
  have hpp : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  by_cases hp2 : (p : ℕ) = 2
  · have hP : IsPGroup 2 (pCore (p : ℕ) G) := hp2 ▸ pCore_isPGroup
    exact h2 _ pCore_normal hP
  · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := (p : ℕ)) (G := G)).exists_card_eq
    have hodd : Odd (Nat.card (pCore (p : ℕ) G)) := by
      rw [hn]
      exact (hpp.out.odd_of_ne_two hp2).pow
    have hle : pCore (p : ℕ) G ≤ classicalInvolutionOddCore G :=
      CFSG.ComponentClassification.OddCore.maximal G _ pCore_normal hodd
    rw [hO] at hle
    exact le_bot_iff.mp hle

theorem eq_bot_of_normal_of_isSolvable_of_fitting_eq_bot [Finite G]
    (hF : fittingSubgroup G = ⊥) (N : Subgroup G) [N.Normal] (hN : Group.IsSolvable ↥N) :
    N = ⊥ := by
  have h := fitting_normal_intersection N
  rw [hF, inf_bot_eq] at h
  have hF' : fittingSubgroup ↥N = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h
  have hcard : Nat.card ↥N = 1 := (fitting_eq_bot_iff_card_eq_one_of_solvable ↥N).mp hF'
  exact Subgroup.eq_bot_of_card_eq N hcard

theorem solvable_normal_eq_bot_of_oddCore [Finite G] (hO : classicalInvolutionOddCore G = ⊥)
    (h2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥ := fun N hN hs =>
  have := hN
  eq_bot_of_normal_of_isSolvable_of_fitting_eq_bot
    (fittingSubgroup_eq_bot_of_oddCore_of_pGroup hO h2) N hs

end AscThmA

end CFSG.ClassicalInvolution.Asc77
