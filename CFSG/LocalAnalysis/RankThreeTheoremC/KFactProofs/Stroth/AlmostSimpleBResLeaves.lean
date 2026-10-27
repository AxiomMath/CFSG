module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOuterAssembly
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerLinearOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2274
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)

@[expose] def LieIndexSp : TauCeti.LieTypeIndex → Prop
  | .B _ _ => True
  | .C _ _ => True
  | _ => False

@[expose] def LieIndexOmegaPlus : TauCeti.LieTypeIndex → Prop
  | .D _ _ => True
  | _ => False

@[expose] def LieIndexOmegaMinus : TauCeti.LieTypeIndex → Prop
  | .twistedD _ _ => True
  | _ => False

@[expose] def LieIndexE6 : TauCeti.LieTypeIndex → Prop
  | .E6 _ => True
  | _ => False

@[expose] def LieIndexTwistedE6 : TauCeti.LieTypeIndex → Prop
  | .twistedE6 _ => True
  | _ => False

@[expose] def LieIndexE7 : TauCeti.LieTypeIndex → Prop
  | .E7 _ => True
  | _ => False

@[expose] def LieIndexE8 : TauCeti.LieTypeIndex → Prop
  | .E8 _ => True
  | _ => False

@[expose] def LieIndexF4 : TauCeti.LieTypeIndex → Prop
  | .F4 _ => True
  | _ => False

@[expose] def LieIndexG2 : TauCeti.LieTypeIndex → Prop
  | .G2 _ => True
  | _ => False

@[expose] def LieIndexTrialityD4 : TauCeti.LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

@[expose] def LieIndexSuzuki : TauCeti.LieTypeIndex → Prop
  | .suzuki _ => True
  | _ => False

@[expose] def LieIndexReeF4 : TauCeti.LieTypeIndex → Prop
  | .reeF4 _ => True
  | _ => False

@[expose] def LieIndexTits : TauCeti.LieTypeIndex → Prop
  | .tits => True
  | _ => False

theorem ChevTwoOuterFixesPair.of_cover {F F₁ F₂ : TauCeti.LieTypeIndex → Prop}
    (hcover : ∀ i, F i → F₁ i ∨ F₂ i) (h₁ : ChevTwoOuterFixesPair F₁)
    (h₂ : ChevTwoOuterFixesPair F₂) : ChevTwoOuterFixesPair F := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, e⟩ hne α hα hαp
  rcases hcover d.1 hF with h | h
  · exact h₁ p hp hp2 L hrk ⟨d, hchar, h, e⟩ hne α hα hαp
  · exact h₂ p hp hp2 L hrk ⟨d, hchar, h, e⟩ hne α hα hαp

theorem chevTwoOuterFixesPair_classical (hSp : ChevTwoOuterFixesPair LieIndexSp)
    (hD : ChevTwoOuterFixesPair LieIndexOmegaPlus)
    (hD2 : ChevTwoOuterFixesPair LieIndexOmegaMinus) :
    ChevTwoOuterFixesPair LieFamilyClassical :=
  ChevTwoOuterFixesPair.of_cover
    (F₁ := LieIndexSp) (F₂ := fun i => LieIndexOmegaPlus i ∨ LieIndexOmegaMinus i)
    (fun i hi => by cases i <;> simp_all [LieFamilyClassical, LieIndexSp, LieIndexOmegaPlus,
      LieIndexOmegaMinus]) hSp
    (ChevTwoOuterFixesPair.of_cover (fun i hi => hi) hD hD2)

theorem chevTwoOuterFixesPair_exceptional (hE6 : ChevTwoOuterFixesPair LieIndexE6)
    (hE6t : ChevTwoOuterFixesPair LieIndexTwistedE6) (hE7 : ChevTwoOuterFixesPair LieIndexE7)
    (hE8 : ChevTwoOuterFixesPair LieIndexE8) (hF4 : ChevTwoOuterFixesPair LieIndexF4)
    (hG2 : ChevTwoOuterFixesPair LieIndexG2)
    (hD4 : ChevTwoOuterFixesPair LieIndexTrialityD4) :
    ChevTwoOuterFixesPair LieFamilyExceptional := by
  refine ChevTwoOuterFixesPair.of_cover (F₁ := LieIndexE6)
    (F₂ := fun i => LieIndexTwistedE6 i ∨ LieIndexE7 i ∨ LieIndexE8 i ∨ LieIndexF4 i ∨
      LieIndexG2 i ∨ LieIndexTrialityD4 i)
    (fun i hi => by cases i <;> simp_all [LieFamilyExceptional, LieIndexE6, LieIndexTwistedE6,
      LieIndexE7, LieIndexE8, LieIndexF4, LieIndexG2, LieIndexTrialityD4]) hE6 ?_
  refine ChevTwoOuterFixesPair.of_cover (F₁ := LieIndexTwistedE6)
    (F₂ := fun i => LieIndexE7 i ∨ LieIndexE8 i ∨ LieIndexF4 i ∨ LieIndexG2 i ∨
      LieIndexTrialityD4 i) (fun i hi => hi) hE6t ?_
  refine ChevTwoOuterFixesPair.of_cover (F₁ := LieIndexE7)
    (F₂ := fun i => LieIndexE8 i ∨ LieIndexF4 i ∨ LieIndexG2 i ∨ LieIndexTrialityD4 i)
    (fun i hi => hi) hE7 ?_
  refine ChevTwoOuterFixesPair.of_cover (F₁ := LieIndexE8)
    (F₂ := fun i => LieIndexF4 i ∨ LieIndexG2 i ∨ LieIndexTrialityD4 i)
    (fun i hi => hi) hE8 ?_
  refine ChevTwoOuterFixesPair.of_cover (F₁ := LieIndexF4)
    (F₂ := fun i => LieIndexG2 i ∨ LieIndexTrialityD4 i) (fun i hi => hi) hF4 ?_
  exact ChevTwoOuterFixesPair.of_cover (fun i hi => hi) hG2 hD4

theorem chevTwoOuterFixesPair_half (hSz : ChevTwoOuterFixesPair LieIndexSuzuki)
    (hRee : ChevTwoOuterFixesPair LieIndexReeF4) (hTits : ChevTwoOuterFixesPair LieIndexTits) :
    ChevTwoOuterFixesPair LieFamilyHalf := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, e⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | suzuki m => exact hSz p hp hp2 L hrk ⟨⟨_, hv⟩, hchar, trivial, e⟩ hne α hα hαp
  | reeF4 m => exact hRee p hp hp2 L hrk ⟨⟨_, hv⟩, hchar, trivial, e⟩ hne α hα hαp
  | tits => exact hTits p hp hp2 L hrk ⟨⟨_, hv⟩, hchar, trivial, e⟩ hne α hα hαp
  | reeG2 m => exact absurd hchar (by simp [IsChevIndexTwo])
  | A _ _ => exact absurd hF (by simp [LieFamilyHalf])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyHalf])
  | B _ _ => exact absurd hF (by simp [LieFamilyHalf])
  | C _ _ => exact absurd hF (by simp [LieFamilyHalf])
  | D _ _ => exact absurd hF (by simp [LieFamilyHalf])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyHalf])
  | E6 _ => exact absurd hF (by simp [LieFamilyHalf])
  | E7 _ => exact absurd hF (by simp [LieFamilyHalf])
  | E8 _ => exact absurd hF (by simp [LieFamilyHalf])
  | F4 _ => exact absurd hF (by simp [LieFamilyHalf])
  | G2 _ => exact absurd hF (by simp [LieFamilyHalf])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyHalf])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyHalf])

theorem chevTwoOuterFixesPair_suzuki : ChevTwoOuterFixesPair LieIndexSuzuki := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  exfalso
  obtain ⟨d, hv⟩ := d
  cases d with
  | suzuki m =>
    haveI : Fact p.Prime := ⟨hp⟩
    have hm : 0 < m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    let eL : L ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
      e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)
    obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sq_of_pRank_eq_two hp hrk
    haveI : Finite (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      Finite.of_equiv L eL.toEquiv
    set E' := E.map eL.toMonoidHom with hE'
    haveI := isElementaryAbelian_of_isElemAbelian (CFSG.Open.IsElemAbelian.map hE eL.toMonoidHom)
    have hE'c : Nat.card E' = p ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective eL.injective]
      exact hEc
    obtain ⟨R, hR⟩ := (IsPGroup.of_card hE'c).exists_le_sylow
    have hcyc := CFSG.SectionRank.suzuki_sylow_isCyclic m hm hp2 R
    have : IsCyclic E' := isCyclic_of_injective (Subgroup.inclusion hR)
      (Subgroup.inclusion_injective hR)
    exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hE'c this
  | A _ _ => exact absurd hF (by simp [LieIndexSuzuki])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexSuzuki])
  | B _ _ => exact absurd hF (by simp [LieIndexSuzuki])
  | C _ _ => exact absurd hF (by simp [LieIndexSuzuki])
  | D _ _ => exact absurd hF (by simp [LieIndexSuzuki])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexSuzuki])
  | E6 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | E7 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | E8 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | F4 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | G2 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | reeG2 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | reeF4 _ => exact absurd hF (by simp [LieIndexSuzuki])
  | tits => exact absurd hF (by simp [LieIndexSuzuki])

theorem chevTwoOuterPElementIsLThree_of_leaves (hSp : ChevTwoOuterFixesPair LieIndexSp)
    (hD : ChevTwoOuterFixesPair LieIndexOmegaPlus)
    (hD2 : ChevTwoOuterFixesPair LieIndexOmegaMinus) (hE6 : ChevTwoOuterFixesPair LieIndexE6)
    (hE6t : ChevTwoOuterFixesPair LieIndexTwistedE6) (hE7 : ChevTwoOuterFixesPair LieIndexE7)
    (hE8 : ChevTwoOuterFixesPair LieIndexE8) (hF4 : ChevTwoOuterFixesPair LieIndexF4)
    (hG2 : ChevTwoOuterFixesPair LieIndexG2) (hD4 : ChevTwoOuterFixesPair LieIndexTrialityD4)
    (hSz : ChevTwoOuterFixesPair LieIndexSuzuki) (hRee : ChevTwoOuterFixesPair LieIndexReeF4)
    (hTits : ChevTwoOuterFixesPair LieIndexTits) : ChevTwoOuterPElementIsLThree :=
  chevTwoOuterPElementIsLThree_of_fixesPair (chevTwoOuterFixesPair_classical hSp hD hD2)
    (chevTwoOuterFixesPair_exceptional hE6 hE6t hE7 hE8 hF4 hG2 hD4)
    (chevTwoOuterFixesPair_half hSz hRee hTits)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
