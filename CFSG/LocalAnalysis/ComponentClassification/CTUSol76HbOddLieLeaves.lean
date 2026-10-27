module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleAssembly
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpHolds
public import CFSG.LocalAnalysis.ComponentClassification.Sol76F316
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporadic
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporRu
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigBigCenter
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleExcRest
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigC1Rank2
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39K2

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76T13

section Certified

theorem lemma315bInputFor_simple_of_hbKCLeaves
    (h39 : Lemma39TwoDiscKCAt solRestrictedHub)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (hQSi : SolomonQTwoDisconnectedSylowInvFor) :
    Lemma315bInputFor Sol76T13.simpleAmbient := by
  have hq : QuasisimpleTwoPartInput :=
    quasisimpleTwoPartInput_of_centralFour Hq4.quasisimpleCentralFourInput_holds
  have h𝒜 : ∀ (G : Type) [Group G] [Finite G], Sol76T13.simpleAmbient G → KStarKProper G :=
    fun _ _ _ hG => kStarKProper_of_simpleAmbient hG
  have hR1 : Lemma32ConditionTwoInputFor Sol76T13.simpleAmbient :=
    lemma32ConditionTwoInputFor_of_rankTwo
      (lemma32ConditionTwoRankTwoInputFor_of_kernel hq h𝒜
        (lemma32RankTwoKernelInput_of_central
          (R12.quasisimpleRankTwoCentralInput_of_symplectic
            (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz R12.Pcls.sporadicCoverRankInput_Suz))))
  have hC : SingleComponentCatalogFor :=
    singleComponentCatalogFor_of_quasisimple
      (singleComponentQuasisimpleFor_of_clean singleComponentCleanAt_oddClassical
        singleComponentCleanAt_oddExceptional
        (singleComponentQuasisimpleAt_sporadic_of_Ru singleComponentCleanAt_Ru))
  have hBig : QuasisimpleBigCenterRankThree := quasisimpleBigCenterRankThree_holds
  have hI : ∀ (X : Type) [Group X] [Finite X], IsSolomonI X →
      IsInvolutionCoreFree (X ⧸ center X) := by
    intro X _ _ hX
    exact isInvolutionCoreFree_of_isSolomonI involutionCoreFreeJLA_holds hX
  have h39' : Lemma39TwoDiscAt solRestrictedHub :=
    lemma39TwoDiscAt_of_SE (lemma39TwoDiscSEAt_of_I hBig hSJ (lemma39TwoDiscIAt_of_K hq hR1
      (lemma39TwoDiscKAt_of_KK hq hR1 hBig hSJ involutionCoreFreeJLA_holds
        (lemma39TwoDiscKKAt_of_KB hq hR1 (lemma39TwoDiscKBAt_of_KZ_of_le hI solRestrictedHub_le
          (lemma39TwoDiscKZAt_hub_of_KC hq hR1 hI h39))))))
  have hgood : GoodInvolutionsLeftDiscAt solRestrictedHub :=
    goodInvolutionsLeftDiscAt_of_rank2
      (c1Rank2_of_simple (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz
          R12.Pcls.sporadicCoverRankInput_Suz)
        TBLit.griessMultipliersAllModels_holds c1Rank2Simple_holds)
      (goodInvolutionsLeftDiscThreeAt_of_SCN hSJ solRestrictedHub)
  have hQS : SolomonQTwoDisconnectedSylowFor :=
    solomonQTwoDisconnectedSylowFor_of_cent hBig hSJ
      (solomonQTwoDisconnectedSylowCentFor_of_cyc (solomonQTwoDisconnectedSylowCycFor_of_inv hQSi))
  exact lemma315bInputFor_simple_of_forced hq hR1
    (wTrivialFor_of_disc hq hR1 false316CoverFor_simple hC h39' hgood)
    (forcedSeparationFor_of_two hq (fun _ _ _ _ _ _ hr => solRestrictedHub_of_ncard_ne_two hr)
      (forcedSeparationTwoFor_hub (forcedSeparationTwoFor_of_split
        (solomonQTwoDisconnectedFor_of_sylow hBig hQS) forcedSharedRankTwoFor_holds)))

theorem lemma315bInputFor_simple_of_hbK2Leaves
    (h39 : Lemma39TwoDiscK2At solRestrictedHub)
    (hSJ : QuasisimpleSylowFourJoinedSCN) (hQSi : SolomonQTwoDisconnectedSylowInvFor) :
    Lemma315bInputFor Sol76T13.simpleAmbient := by
  have hq : QuasisimpleTwoPartInput :=
    quasisimpleTwoPartInput_of_centralFour Hq4.quasisimpleCentralFourInput_holds
  have h𝒜 : ∀ (G : Type) [Group G] [Finite G], Sol76T13.simpleAmbient G → KStarKProper G :=
    fun _ _ _ hG => kStarKProper_of_simpleAmbient hG
  have hR1 : Lemma32ConditionTwoInputFor Sol76T13.simpleAmbient :=
    lemma32ConditionTwoInputFor_of_rankTwo
      (lemma32ConditionTwoRankTwoInputFor_of_kernel hq h𝒜
        (lemma32RankTwoKernelInput_of_central
          (R12.quasisimpleRankTwoCentralInput_of_symplectic
            (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz R12.Pcls.sporadicCoverRankInput_Suz))))
  have hI : ∀ (X : Type) [Group X] [Finite X], IsSolomonI X →
      IsInvolutionCoreFree (X ⧸ center X) := by
    intro X _ _ hX
    exact isInvolutionCoreFree_of_isSolomonI involutionCoreFreeJLA_holds hX
  exact lemma315bInputFor_simple_of_hbKCLeaves
    (lemma39TwoDiscKCAt_of_KP hq hR1
      (lemma39TwoDiscKPAt_of_K2 (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz
          R12.Pcls.sporadicCoverRankInput_Suz)
        TBLit.griessMultipliersAllModels_holds hI solRestrictedHub_le h39))
    hSJ hQSi

end Certified

end CFSG.ComponentClassification.Sol76.Sig
