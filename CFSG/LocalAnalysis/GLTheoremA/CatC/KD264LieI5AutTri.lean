module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5AutGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

section Triality


theorem kd264I5Aut_triality (e : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie e).Group]
    (q : TauCeti.PrimePower) (he : e.1 = .trialityD4 q) (hq3 : q.p ≠ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 3 := by
  obtain ⟨d, hd⟩ := e
  change d = _ at he
  subst he
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, σ, -, -, ⟨Θ, hker⟩, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hd
  haveI := Finite.of_equiv _ e.toEquiv
  have hinjCat := CFSG.HardMathSupport.Timmesfeld.CrossChar.conj_injective_cat_trialityD4 q hd
  have hinjC := CFSG.LieType.SeitzGeneration.conj_injective_of_mulEquiv e.symm hinjCat
  have hR := CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hd hq3)
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun f : K ≃+* K => (f : K → K)) DFunLike.coe_injective
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have h := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Aut.pRank_mulAut_le_three_of_hom Θ hker hinjC
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Aut.pRank_le_two_of_rankLE2 hR)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr e)]
  exact h

end Triality

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
