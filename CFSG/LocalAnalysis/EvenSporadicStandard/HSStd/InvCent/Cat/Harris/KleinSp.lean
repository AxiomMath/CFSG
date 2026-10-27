module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.KleinBasic
import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallClass
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallOrder
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem not_outerKlein_PSp_two_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (σ : MulAut (StatedProj (StatedSp 2 K))) : ¬ OuterKlein σ := by
  have h2 : (2 : K) ≠ 0 :=
    Ring.two_ne_zero
      (CFSG.ComponentClassification.CatFC.OmegaSmall.ringChar_ne_two_of_card_three hK)
  rintro ⟨α, β, -, -, -, -, -, hα, hβ, hαβ⟩
  obtain ⟨-, hgen⟩ := CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two
    (K := K) h2
  have hDtop : spLinearAutGroup 2 K = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    obtain ⟨A, τ, rfl⟩ := hgen γ
    rw [CFSG.ComponentClassification.CatFC.PSLSmall.eq_one_of_card_three hK τ, map_one, mul_one]
    exact conjAut_mem_spLinearAutGroup A
  have hdvd := relIndex_inner_spLinearAutGroup_dvd (r := 2) (K := K) Nat.prime_three le_rfl
    (by simpa using hK : Nat.card K = 3 ^ 1)
  rw [hDtop, Subgroup.relIndex_top_right] at hdvd
  have hidx : (inner (StatedProj (StatedSp 2 K))).index ∣ 2 := hdvd.trans (by decide)
  have hα' : α ∉ inner (StatedProj (StatedSp 2 K)) := hα
  have hβ' : β ∉ inner (StatedProj (StatedSp 2 K)) := hβ
  rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h1
  · exact hα' (by rw [Subgroup.index_eq_one.1 h1]; exact Subgroup.mem_top _)
  · exact hαβ ((Subgroup.mul_mem_iff_of_index_two h1).2 (iff_of_false hα' hβ'))

theorem harrisKleinFree_PSp_two_three_one : HarrisKleinFree .PSp 2 3 1 := by
  refine harrisKleinFree_of_concrete fun S _ _ hm => ?_
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)
  have hK3 : Nat.card K = 3 := by simpa using hK
  exact ⟨StatedProj (StatedSp 2 K), inferInstance, e,
    fun σ => not_outerKlein_PSp_two_three hK3 σ⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
