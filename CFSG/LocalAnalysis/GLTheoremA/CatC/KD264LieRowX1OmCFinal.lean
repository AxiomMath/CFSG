module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCShape
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmParts
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.Open.StatedZModTwo
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairSepAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import Certificates.Certificate19800

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin

section Transport

open CFSG.Adapters.RankTwoModelTransports (glCongr statedProjCongr glCongr_statedScalars)

noncomputable def omStatedProjEquivOfCardTwo {K : Type} [Field K] (hK : Nat.card K = 2) {ι : Type}
    [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι K)) : H ≃* StatedProj H :=
  (QuotientGroup.quotientBot).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK ι]
      exact (Subgroup.bot_subgroupOf H).symm))

theorem kd264OmPlusCore_holds : KD264OmPlusCore := by
  intro n hn K _ _ hK
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  let e1 : StatedProj (StatedOmega (StatedQuadPlus n K)) ≃*
      StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadPlus_comp σ))
      (glCongr_statedScalars σ)
  let e2 := (omStatedProjEquivOfCardTwo hZ2 (StatedOmega (StatedQuadPlus n (ZMod 2)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadPlus n (ZMod 2)) (coe_quadPlus n (ZMod 2))
  refine omCoreShape_of_mulEquiv ((e1.trans e2).trans e3) ?_
  exact omCoreShape_derived (Q := quadPlus n (ZMod 2))
    (nondegenerate_polarBilin_quadPlus n (ZMod 2)) (finrank_quadPlus_space n) (Or.inl hn)

theorem kd264OmMinusCore_holds : KD264OmMinusCore := by
  intro n hn K _ _ hK b c hirr
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let σ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hZ2 : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hirr' : ∀ s : ZMod 2, s ^ 2 + σ b * s + σ c ≠ 0 := by
    intro s hs
    apply hirr (σ.symm s)
    apply σ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  let e1 : StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus n (ZMod 2) (σ b) (σ c))) :=
    statedProjCongr (glCongr σ)
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl v))
      (glCongr_statedScalars σ)
  let e2 := (omStatedProjEquivOfCardTwo hZ2
    (StatedOmega (StatedQuadMinus n (ZMod 2) (σ b) (σ c)))).symm
  let e3 := CFSG.ComponentClassification.RankTwoClassical.statedOmegaEquivCommutator
    (quadMinus n (ZMod 2) (σ b) (σ c)) (coe_quadMinus n (ZMod 2) (σ b) (σ c))
  refine omCoreShape_of_mulEquiv ((e1.trans e2).trans e3) ?_
  have hn1 : 1 ≤ n := by omega
  refine omCoreShape_derived (Q := quadMinus n (ZMod 2) (σ b) (σ c))
    (nondegenerate_polarBilin_quadMinus_of_finite n (ZMod 2) hirr')
    (finrank_quadMinus_space hn1) ?_
  rcases Nat.lt_or_ge n 5 with hlt | hge
  · exact Or.inr ⟨by omega, not_isPlusType_quadMinus hn1 hirr'⟩
  · exact Or.inl hge

theorem kd264X1OmPlusPart_holds : KD264X1OmPlusPart :=
  kd264X1OmPlusPart_of_core kd264OmPlusCore_holds

theorem kd264X1OmMinusPart_holds : KD264X1OmMinusPart :=
  kd264X1OmMinusPart_of_core kd264OmMinusCore_holds

end Transport

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
