module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIA9
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Balance.LocalBalance
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
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

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt CFSG.Quasithin.SteinbergCB

theorem altFiveCaseI_of_lemmas
    (h32 : Lemma32) (h332 : Lemma33Two)
    (hGen5 : AltGenerationFive) : AltFiveCaseI := by
  intro G _ _ A hH hO hA5 hodd R hR hx
  obtain ⟨x, hx⟩ := hx
  obtain ⟨e⟩ := hA5
  have hZ : center ↥A = ⊥ := center_eq_bot_of_odd_five hH.standard.1.1 e hodd
  set eA := mulEquivOfCenter hZ e with heA
  have hc := sec3_of_le (hyp31_of hH hO le_rfl e) eA hR hx
  have hp := caseIPair_of h32 h332 hc eA hx
  obtain ⟨c⟩ := hp.nonempty_coords
  obtain ⟨Φ, hΦ, hrange, hlift⟩ : ∃ Φ : alternatingGroup (Fin 9) →* G, Function.Injective Φ ∧
      Φ.range = A ⊔ rightConjugate A x ∧ (Φ.comp (liftNat 5)).range = A := by
    by_cases hw : c.w ∈ c.D
    ·
      have hv : c.symm.w ∉ c.symm.D := fun hv =>
        caseIDoubleBad G A hH hO R (rightConjugate R x) x c hw hv
      obtain ⟨Φ, hΦ, hr, -, hB⟩ := c.symm.exists_alt9 hv
      refine ⟨Φ.comp (conjPerm 9 tauB).toMonoidHom, hΦ.comp (conjPerm 9 tauB).injective, ?_, hB⟩
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective (conjPerm 9 tauB).toMonoidHom
        (conjPerm 9 tauB).surjective, ← MonoidHom.range_eq_map, hr, sup_comm]
    · obtain ⟨Φ, hΦ, hr, hA, -⟩ := c.exists_alt9 hw
      exact ⟨Φ, hΦ, hr, hA⟩
  have hX := hGen5 G A R (rightConjugate R x) x Φ
    { five_le := le_rfl
      hyp := hH.toNF
      oddCore_eq_bot := hO
      sec3 := hc
      T_le := hx
      R_le := hp.R_le
      injective := hΦ
      range_eq := hrange
      range_liftNat := hlift }
  exact ⟨((MonoidHom.ofInjective hΦ).trans
    (MulEquiv.subgroupCongr (hrange.trans hX.symm))).symm⟩

theorem altFiveCaseI_of
    (hGen5 : AltGenerationFive) : AltFiveCaseI :=
  altFiveCaseI_of_lemmas RankTwoFoundation.lemma32 RankTwoFoundation.lemma33Two hGen5

end CFSG.ComponentClassification.RankTwoAltFive
