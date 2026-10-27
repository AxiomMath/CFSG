module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3Outer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3Inner
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender

theorem hypothesisOneStar_of_statedPSU3 {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSU 3 2 f) : HypothesisOneStar D := by
  obtain ⟨e⟩ := GMS78.nonempty_mulEquiv_psu3_of_stated hf hD
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
      CFSG.Models.benderPSU3Model_eq_psu3 f
  have hB := BenderType.unitary (K := D) f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  intro x u hx hu E _ hEodd hEu hE
  by_cases hinn : ∃ z : D, x = MulAut.conj z
  · obtain ⟨z, hz⟩ := hinn
    exact hypOneStar_u3_inner hf e hx hu hz hEodd hEu
  · exact hypOneStar_u3_outer hf hB hx hu hinn hEodd hEu hE

end CFSG.SeitzReduction.RankOne
