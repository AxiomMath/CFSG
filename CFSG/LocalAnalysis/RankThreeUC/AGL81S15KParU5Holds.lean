module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KParU5SU
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs
public import CFSG.LieType.Simplicity.Basic
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutatorFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FixedPointsTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRAssemble
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightSep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltBigVector
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactE9U33
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.QuasithinUnique
  CFSG.LocalAnalysis.RankThreeUC.S15.KParU5Proof

theorem exists_minOver_of_twistedA_even {m : ℕ} (hm4 : 4 ≤ m) (hm : Even m)
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : CFSG.Open.IsComponentOf Ls ⊤)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQ2 : Q.p = 2)
    (hd : d.1 = .twistedA m Q)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    ∃ P : Subgroup (X ⧸ gnC T), IsMinOverBorel Ls (gnImg T T ⊓ Ls) P ∧
      ∀ q : ℕ, q.Prime → q ∣ Q.card + 1 → 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P) := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨e⟩ := e
  dsimp only at hd
  subst hd
  have hnm : ¬ Even (m + 1) := by
    obtain ⟨k, rfl⟩ := hm
    rintro ⟨r, hr⟩
    omega
  have hS : IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
      hX.sylow hL.2.1
  have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv e
  rw [hQ2] at hmodel
  obtain ⟨⟨-, -, -, -⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hmodel
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := Q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨P, hmin, hP⟩ := exists_minOver_su_odd (n := m + 1) hcard (by omega) hnm hS e'
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ2]
  refine ⟨P, hmin, fun q hq hqd => hP q hq ?_ (by rw [← hQc]; exact hqd)⟩
  rintro rfl
  have h2 : 2 ∣ 2 ^ Q.exponent := dvd_pow_self 2 Q.exponent_pos.ne'
  rw [← hQc] at h2
  have h3 : 2 ∣ 1 := (Nat.dvd_add_right h2).1 hqd
  omega

theorem KParU5_holds : KParU5 := by
  intro X _ _ T hX Ls hL d Q hQ2 hd e
  exact exists_minOver_of_twistedA_even (m := 4) (by norm_num) (by decide) hX hL hQ2 hd e

end CFSG.LocalAnalysis.RankThreeUC.S15
