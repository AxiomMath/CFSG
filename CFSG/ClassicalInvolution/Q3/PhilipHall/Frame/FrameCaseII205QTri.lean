module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205QEmpty

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.AzTri

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem thm4_pairFam_of_bar {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    {K₁ K₂ : Subgroup ↥(Subgroup.centralizer ({c} : Set G))} (hK₁ : K₁ ∈ cFam Ω c)
    (hK₂ : K₂ ∈ cFam Ω c) (hPB : FrameAEmptyPf.PairBarEmpty K₁ K₂)
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G)))
    (hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < n) :
    ∀ J ∈ quotFamily (restrictFamily (pairFam K₁ K₂) X) (classicalInvolutionOddCore ↥X),
      ∀ L ∈ quotFamily (restrictFamily (pairFam K₁ K₂) X) (classicalInvolutionOddCore ↥X),
      (¬ ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X, conjSub g J = L) → Commutes J L := by
  have hΛ : HypOmegaGen (cFam Ω c) := TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hsub : pairFam K₁ K₂ ⊆ cFam Ω c := pairFam_subset hΛ.conjInvariant hK₁ hK₂
  have hΛ' : HypOmegaGen (pairFam K₁ K₂) :=
    TL4.hypOmegaGen_sub hΛ hsub (conjInvariant_pairFam K₁ K₂)
  have hΛX := hypOmegaGen_restrict hΛ' X
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥X
  have hmem : ∀ J ∈ quotFamily (restrictFamily (pairFam K₁ K₂) X) (classicalInvolutionOddCore ↥X),
      J ∈ famX Ω c X := by
    rintro _ ⟨_, ⟨L₀, hL₀, hL₀X, rfl⟩, rfl⟩
    exact ⟨_, ⟨L₀, hsub hL₀, hL₀X, rfl⟩, rfl⟩
  exact h4 _ hlt _ (TwinEdge.hypOmegaGen_quotFamily_odd hΛX hodd)
    (fun J hJ => famX_twoGroup h2 X J (hmem J hJ))
    (fun J hJ => famX_q8 hc2 hq X J (hmem J hJ)) (hPB X)
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥X)

end Fam

section Sec

variable {Y : Type} [Group Y] [Finite Y]



open CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL

theorem aEmpty_section_of_bar {K₀ : Subgroup Y} (hΩ : HypOmegaGen (CoreAssembly.conjClass K₀))
    {c : Y} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K₂ : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))}
    (hK₁ : tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ∈
      cFam (CoreAssembly.conjClass K₀) c)
    (hK₂ : K₂ ∈ cFam (CoreAssembly.conjClass K₀) c)
    (hPB : FrameAEmptyPf.PairBarEmpty
      (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) K₂) :
    AEmpty (CoreAssembly.conjClass (tightCore (secR K₀ c))) (tightCore (secR K₀ c)) := by
  have hΛ : HypOmegaGen (cFam (CoreAssembly.conjClass K₀) c) :=
    TwinADescent.hypOmegaGen_coreFamily hΩ hc2
  have hΛp : HypOmegaGen (pairFam
      (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) K₂) :=
    TL4.hypOmegaGen_sub hΛ (pairFam_subset hΛ.conjInvariant hK₁ hK₂)
      (conjInvariant_pairFam _ _)
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(secH K₀ c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(secH K₀ c)
  have hΔ := hypOmegaGen_quotFamily_odd (hypOmegaGen_restrict hΛp (secH K₀ c)) hodd
  have hKH : tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ≤ secH K₀ c :=
    le_subnormalClosure _
  have hmem : tightCore (secR K₀ c) ∈ quotFamily (restrictFamily (pairFam
      (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) K₂) (secH K₀ c))
      (classicalInvolutionOddCore ↥(secH K₀ c)) :=
    ⟨_, ⟨_, left_mem_pairFam _ _, hKH, rfl⟩, (TwinEdge.tightCore_secR K₀ c).symm⟩
  have hsub : CoreAssembly.conjClass (tightCore (secR K₀ c)) ⊆ quotFamily (restrictFamily
      (pairFam (tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)))) K₂)
      (secH K₀ c)) (classicalInvolutionOddCore ↥(secH K₀ c)) := by
    rintro _ ⟨g, rfl⟩
    exact hΔ.conjInvariant g _ hmem
  exact Thm4Twin.aEmpty_sub hΔ hsub (hPB (secH K₀ c) _ hmem)


variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem pair_mem_cFam {n : ℕ} (h : SecCoreHyp n R S t) (hRc : tightCore R = R) {c : Y}
    (hcm : c ∈ centralizerModOdd ⊤ R) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ∈
        cFam (CoreAssembly.conjClass R) c ∧
      (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)) ∈
        cFam (CoreAssembly.conjClass R) c := by
  have hRΩ : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hRtq : R ∈ tqMembers3 (CoreAssembly.conjClass R) c :=
    ⟨hRΩ, ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩⟩
  have hK'Ω : K' ∈ CoreAssembly.conjClass R := by
    have := hK'.1; rwa [hRc] at this
  have hK'tq : K' ∈ tqMembers3 (CoreAssembly.conjClass R) c := ⟨hK'Ω, hcK'⟩
  have hK₁eq : tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) =
      (TwinADescent.coreAt c R).subgroupOf (Subgroup.centralizer ({c} : Set Y)) :=
    tightCore_subgroupOf_cent R c
  exact ⟨⟨TwinADescent.coreAt c R, TwinADescent.coreAt_mem_coreFamily hRtq,
      TwinADescent.coreAt_le_centralizer c R, hK₁eq⟩,
    ⟨TwinADescent.coreAt c K', TwinADescent.coreAt_mem_coreFamily hK'tq,
      TwinADescent.coreAt_le_centralizer c K', rfl⟩⟩

theorem hasTwin_or_inO2_bar {n : ℕ} (h4 : Thm4RTwinBelow 3 n) {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : SecCoreHyp n R S t) (hRc : tightCore R = R) {c : Y}
    (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hlt0 : Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) < n) {K' : Subgroup Y}
    (hPB : FrameAEmptyPf.PairBarEmpty
      (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
      ((TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c)
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'ne : K' ≠ tightCore R) (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    HasTwin (tightCore (secR R c)) ∨
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
        (⟨⟨t, htc⟩, ht⟩ : secH R c)) := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hRΩ : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have hRtq : R ∈ tqMembers3 (CoreAssembly.conjClass R) c :=
    ⟨hRΩ, ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩⟩
  have hK'Ω : K' ∈ CoreAssembly.conjClass R := by
    have := hK'.1; rwa [hRc] at this
  have hK'tq : K' ∈ tqMembers3 (CoreAssembly.conjClass R) c := ⟨hK'Ω, hcK'⟩
  have hK'ne' : K' ≠ R := by rwa [hRc] at hK'ne
  have htR : IsUniqueInvolution R t := by
    have := Q8Datum.isUniqueInvolution_core h.datum; rwa [hRc] at this
  have htK' : IsUniqueInvolution K' t := by
    obtain ⟨-, z, hzR, hzK'⟩ := hK'
    rw [hRc] at hzR
    rwa [htR.eq hzR]
  have h2 : ∀ M ∈ CoreAssembly.conjClass R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass h.datum.twoGroup
  have hq : ∀ M ∈ CoreAssembly.conjClass R, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup 2) := by
    obtain ⟨P₀, hP₀, ⟨e⟩⟩ := h.datum.exists_sylow_q8 h.q8
    rw [hRc] at hP₀
    rintro _ ⟨g, rfl⟩
    apply forall_sylow_iso_of_exists
    exact ⟨conjSub g P₀, hP₀.conj g, ⟨(Subgroup.equivMapOfInjective P₀ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e⟩⟩
  have hK₁eq : tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) =
      (TwinADescent.coreAt c R).subgroupOf (Subgroup.centralizer ({c} : Set Y)) :=
    tightCore_subgroupOf_cent R c
  have hK₁Λ : tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ∈
      cFam (CoreAssembly.conjClass R) c :=
    ⟨TwinADescent.coreAt c R, TwinADescent.coreAt_mem_coreFamily hRtq,
      TwinADescent.coreAt_le_centralizer c R, hK₁eq⟩
  have hK₂Λ : (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)) ∈
      cFam (CoreAssembly.conjClass R) c :=
    ⟨TwinADescent.coreAt c K', TwinADescent.coreAt_mem_coreFamily hK'tq,
      TwinADescent.coreAt_le_centralizer c K', rfl⟩
  have hne : tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ≠
      (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
    intro he
    rw [hK₁eq] at he
    have h1 := congrArg (Subgroup.map (Subgroup.centralizer ({c} : Set Y)).subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c R),
      Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer c K')] at h1
    exact hK'ne' (eq_of_coreAt_eq hΩ hc2' hK'tq hRtq h1.symm)
  have htR' : IsUniqueInvolution (TwinADescent.coreAt c R) t :=
    isUniqueInvolution_coreAt_of_tq hΩ hc2' hRtq htR
  have htK'' : IsUniqueInvolution (TwinADescent.coreAt c K') t :=
    isUniqueInvolution_coreAt_of_tq hΩ hc2' hK'tq htK'
  have ht₁ : IsUniqueInvolution (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
      (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) := by
    rw [hK₁eq]
    exact isUniqueInvolution_subgroupOf htR' (TwinADescent.coreAt_le_centralizer c R)
  have ht₂ : IsUniqueInvolution ((TwinADescent.coreAt c K').subgroupOf
      (Subgroup.centralizer ({c} : Set Y))) (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) :=
    isUniqueInvolution_subgroupOf htK'' (TwinADescent.coreAt_le_centralizer c K')
  have hH : tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))) ≤ secH R c :=
    le_subnormalClosure _
  have hnorm : (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)) ≤
      Subgroup.normalizer ((secH R c : Subgroup ↥(Subgroup.centralizer ({c} : Set Y))) :
        Set ↥(Subgroup.centralizer ({c} : Set Y))) := by
    intro x hx
    refine mem_normalizer_subnormalClosure ?_
    rw [hK₁eq]
    have hcomm := Sec6Gen.comm_le_oddCore_of_twin hΩ hK'Ω hRΩ hK'ne' htK' htR
    have hc21 : ⁅K', R⁆ ≤ R := hcomm.trans (inf_le_right.trans (oddCoreOf_le_self R))
    have hxn := TwinEdge.Fam.tightCore_inf_le_normalizer
      (Subgroup.centralizer ({c} : Set Y)) hc21 (Subgroup.mem_subgroupOf.mp hx)
    exact (mem_normalizer_subgroupOf_iff (TwinADescent.coreAt_le_centralizer c R)).mp hxn
  have hgen : (⨆ g : ↥(secH R c), conjSub g
      ((tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH R c))) =
        ⊤ :=
    iSup_conjSub_eq_top_of_subnormalClosure (subnormalClosure_subgroupOf_subnormalClosure _)
  have hlt : Nat.card (↥(secH R c ⊔ (TwinADescent.coreAt c K').subgroupOf
      (Subgroup.centralizer ({c} : Set Y))) ⧸ classicalInvolutionOddCore ↥(secH R c ⊔
        (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)))) < n := by
    have h1 := Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c ⊔
        (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)))))
      (QuotientGroup.mk'_surjective _)
    have h2 := Subgroup.card_le_card_group (secH R c ⊔ (TwinADescent.coreAt c K').subgroupOf
      (Subgroup.centralizer ({c} : Set Y)))
    omega
  have h4X := thm4_pairFam_of_bar h4 hΩ hc2' h2 hq hK₁Λ hK₂Λ hPB
    (secH R c ⊔ (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y))) hlt
  have hΛ0 : HypOmegaGen (cFam (CoreAssembly.conjClass R) c) :=
    TwinADescent.hypOmegaGen_coreFamily hΩ hc2'
  have hΛp : HypOmegaGen (pairFam (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
      ((TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)))) :=
    TL4.hypOmegaGen_sub hΛ0 (pairFam_subset hΛ0.conjInvariant hK₁Λ hK₂Λ)
      (conjInvariant_pairFam _ _)
  have hdich := dichotomy_abstract hΛp h4X (left_mem_pairFam _ _) (right_mem_pairFam _ _) hne
    ht₁ ht₂ hH rfl hnorm hgen ht
  have hNH : Odd (Nat.card ↥(classicalInvolutionOddCore ↥(secH R c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(secH R c)
  rcases hdich with hcen | ⟨h₀, hne2, hinv⟩
  · right
    have htt : QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c) *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c) = 1 := by
      rw [← map_mul]
      have : (⟨⟨t, htc⟩, ht⟩ : secH R c) * ⟨⟨t, htc⟩, ht⟩ = 1 := Subtype.ext ht₁.sq
      rw [this, map_one]
    refine ⟨Subgroup.zpowers (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
      (⟨⟨t, htc⟩, ht⟩ : secH R c)), ⟨fun n hn g => ?_⟩, ?_, Subgroup.mem_zpowers _⟩
    · obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hc := hcen g₀
      have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) g₀ *
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
            (⟨⟨t, htc⟩, ht⟩ : secH R c) *
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) g₀)⁻¹ =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
            (⟨⟨t, htc⟩, ht⟩ : secH R c) := by
        rw [hc]; group
      rw [← conj_zpow, h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
    · by_cases h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c) = 1
      · rw [h1, Subgroup.zpowers_one_eq_bot]
        exact IsPGroup.of_bot
      · exact isPGroup_zpowers_of_mul_self_eq_one htt h1
  · left
    have hKbar := TwinEdge.tightCore_secR R c
    unfold HasTwin
    rw [TwinEdge.tightCore_idem, hKbar]
    have hKinv := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNH
      ((tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y)))).subgroupOf (secH R c)))
      (isUniqueInvolution_subgroupOf ht₁ hH)
    refine ⟨conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) h₀) _,
      ⟨⟨_, rfl⟩, _, hKinv, ?_⟩, hne2⟩
    have := hKinv.conj (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c)) h₀)
    rwa [hinv] at this


theorem quietLiftedSecExit_bar {n : ℕ} (hSp : ModelFactSp62) (hD4 : ModelFactD42)
    (h4 : Thm4RTwinBelow 3 n) (h : SecCoreHyp n R S t) (hRc : tightCore R = R)
    {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hlt0 : Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) < n) {K' : Subgroup Y}
    (hPB : FrameAEmptyPf.PairBarEmpty
      (tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set Y))))
      ((TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y))))
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'ne : K' ≠ tightCore R) (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    Quiet c t htc ∨ LiftedAtSec R c t htc ∨
      ((∃ _ : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c,
          ExitE4At (SecQ R c)) ∧ MovedOddFreeAt c t htc) := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_mul_self_eq_one hc2 hc1
  have hcK : c ∈ Balance.Bootstrap.trivialOnQuot R := ⟨hcm.2.1, fun x hx => hcm.2.2.2 x hx⟩
  have hΩs := twinSecHyp_cent h.datum hRc h.hyp hc2 hc1 hcm
  rcases classicalOrQuiet_or_of_cent_sec' h hRc hc2 hc1 hlt0 hcm htc
      (fun ht => ExitE4At (SecQ R c) ∧
        SecOddFree R c (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
          (⟨⟨t, htc⟩, ht⟩ : secH R c)))
      (fun ht Sb hx => by
        rcases hasTwin_or_inO2_bar h4 h hRc hc2 hc1 hlt0 hPB hcm htc ht hK' hK'ne hcK' with
          htw | i
        · have hΩ' : HypOmegaGen (CoreAssembly.conjClass (tightCore (tightCore (secR R c)))) := by
            rw [TwinEdge.tightCore_idem]; exact hΩs
          rcases hx with hx | hx
          · rcases hx with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4'
            · exact Or.inl h2
            · exact absurd he (TwinExitPf.not_tightEdgeless_of_hasTwin hΩ' htw)
            · exact absurd he (TwinExitPf.not_tightEdgeless_of_hasTwin hΩ' htw)
            · exact Or.inr ⟨Or.inr (Or.inl h4'), movedOddFreeIn_of_tightE4 hSp hD4 h4' _⟩
          · exact Or.inr ⟨Or.inl hx, movedOddFreeIn_of_twinE4 hSp hD4 hx _⟩
        · exact Or.inl i)
      (fun ht => Or.inl (aEmpty_section_of_bar hΩ hc2' (pair_mem_cFam h hRc hcm hK' hcK').1
        (pair_mem_cFam h hRc hcm hK' hcK').2 hPB)) with h1 | h1 | ⟨ht, he, o⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨⟨ht, he⟩,
      movedOddFreeAt_of_sec (isSubnormal_subnormalClosure _) ht rfl o⟩)

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.AzTri
