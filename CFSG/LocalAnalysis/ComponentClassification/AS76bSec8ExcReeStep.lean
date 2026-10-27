module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcEleven
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeClass
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeResidual
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeD0
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.SymCtxQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KLAY.Frames
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate8026Base

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.ReeSec8

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoExceptional.Exc
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)

theorem step814_ree
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) :
    Step814 .twistedF4 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | ree a ha K hK e =>
    have : CharP K F4.prime :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK
    have h34 : Asc08Lemma34 := asc08Lemma34
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    obtain ⟨E⟩ := nonempty_derivedCentralQuotient_mulEquiv_reeGamma (K := K) ha hK
    have e₁ : ReeQuot K a ≃* DerivedCentralQuotient (F4.reeGamma K a) := by
      rw [reeGamma_eq_reeFixedGroup]
      exact MulEquiv.refl _
    have hZC := large_Ree_fixed_group_center_trivial a K hK
    have hR : ReeTitsModel (rankTwoQuot A) .twistedF4 2 (2 * a + 1) :=
      ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl, K, inferInstance,
        inferInstance, hK, ⟨e⟩⟩
    have hOut := odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_twistedF4 hR)
    have : Finite (F4.reeGamma K a) := Subtype.finite
    have hz : centralZ K a 1 ∈ F4.reeGamma K a := (zK_le ha hK) ((mem_zK hK).2 ⟨1, rfl⟩)
    have ht : sylowL a K 1 ∈ F4.reeGamma K a := (tK_le ha hK) ((mem_tK hK).2 ⟨1, rfl⟩)
    have hresz := residualMem_z ha hK hz
    have hrest := residualMem_t ha hK ht
    refine exists_config814_of_otherClass h32 h33 h4 h34 _ hA hZA hZC ((e.trans e₁).trans E)
      hOut (2 ^ (2 * a + 1)) rfl (reps := [⟨_, hz⟩, ⟨_, ht⟩]) (lreps := [⟨_, ht⟩])
      (classesCover_ree ha hK hz ht) ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨_, ⟨centreData_z ha hK hz, card_zK hK (zK_le ha hK), charTwo_z ha hK hz,
          Or.inl hresz⟩, hresz⟩
      · exact ⟨_, ⟨centreData_t ha hK ht, card_tK hK (tK_le ha hK), charTwo_t ha hK ht,
          Or.inl hrest⟩, hrest⟩
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · obtain ⟨u, hu⟩ := regular_z ha hK
        exact ⟨_, u, centreData_z ha hK hz, hu, sylowData_z ha hK hz⟩
      · obtain ⟨u, hu⟩ := regular_t ha hK
        exact ⟨_, u, centreData_t ha hK ht, hu, sylowData_t ha hK ht⟩
    · intro _ y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · rw [zx_eq_of_centreData (centreData_z ha hK hz)]
        exact d0Data_z ha hK hz
      · rw [zx_eq_of_centreData (centreData_t ha hK ht)]
        exact d0Data_t ha hK ht
    · intro _ y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      obtain ⟨Dl, Ql, Hl, Ll, hL, hAF, hT⟩ := reeLevi a ha K hK ht
      exact ⟨Dl, Ql, Hl, Ll, ⟨hL, hAF, fun L₀ ⟨f⟩ => statedPSL_of_mulEquiv f hT,
        fun h => by simp [ExcModel.IsTrialityFour] at h⟩⟩
    · intro _ y hy hyl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy hyl
      rcases hy with rfl | rfl
      · rw [zx_eq_of_centreData (centreData_z ha hK hz)]
        exact fusion_z ha hK ht
      · exact absurd rfl hyl
    · intro h
      simp [ExcModel.IsTrialityFour] at h
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional.ReeSec8
