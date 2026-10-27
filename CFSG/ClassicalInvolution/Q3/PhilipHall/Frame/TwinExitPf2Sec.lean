module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

section Prelim

variable {A : Type} [Group A] [Finite A]

theorem mem_normalizer_subnormalClosure {K : Subgroup A} {n : A}
    (hn : n ∈ Subgroup.normalizer (K : Set A)) :
    n ∈ Subgroup.normalizer ((subnormalClosure K : Subgroup A) : Set A) := by
  have key : ∀ m ∈ Subgroup.normalizer (K : Set A),
      subnormalClosure K ≤ conjSub m (subnormalClosure K) := by
    intro m hm
    have hsub : IsSubnormal (conjSub m (subnormalClosure K)) ⊤ := by
      have h1 := isSubnormal_map_conj (isSubnormal_subnormalClosure K) m
      rwa [Subgroup.map_top_of_surjective _ (MulAut.conj m).surjective] at h1
    refine subnormalClosure_le ?_ hsub
    have h2 := conjSub_mono (n := m) (le_subnormalClosure K)
    rwa [conjSub_eq_of_mem_normalizer hm] at h2
  have h1 := key n hn
  have h2 := key n⁻¹ ((Subgroup.normalizer (K : Set A)).inv_mem hn)
  have h3 := conjSub_mono (n := n) h2
  rw [conjSub_conjSub_inv] at h3
  exact mem_normalizer_of_conjSub_eq (le_antisymm h3 h1)

end Prelim

section Main


variable {Y : Type} [Group Y] [Finite Y]

theorem tightCore_subgroupOf_cent (K₀ : Subgroup Y) (c : Y) :
    tightCore (K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y))) =
      (TwinADescent.coreAt c K₀).subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
  have e : K₀.subgroupOf (Subgroup.centralizer ({c} : Set Y)) =
      (K₀ ⊓ Subgroup.centralizer ({c} : Set Y)).subgroupOf (Subgroup.centralizer ({c} : Set Y)) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [e, tightCore_subgroupOf inf_le_right]
  rfl

theorem hasTwin_or_inO2 {n : ℕ} (h4 : Thm4RTwinBelow 3 n) {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (h : TwinCoreHyp n Y R S t) (hRc : tightCore R = R) {c : Y} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcm : c ∈ centralizerModOdd ⊤ R) (htc : t ∈ Subgroup.centralizer ({c} : Set Y))
    (ht : (⟨t, htc⟩ : Subgroup.centralizer ({c} : Set Y)) ∈ secH R c) {K' : Subgroup Y}
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hK'ne : K' ≠ tightCore R) (hcK' : c ∈ Balance.Bootstrap.trivialOnQuot K') :
    HasTwin (tightCore (secR R c)) ∨
      TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c))
        (⟨⟨t, htc⟩, ht⟩ : secH R c)) := by
  classical
  have hΩ : HypOmegaGen (CoreAssembly.conjClass R) := by
    have := h.hyp; rwa [hRc] at this
  have hA : ∀ M ∈ CoreAssembly.conjClass R, AEmpty (CoreAssembly.conjClass R) M := by
    have := h.aEmpty
    rw [hRc] at this
    rintro _ ⟨g, rfl⟩
    exact aEmpty_conj hΩ.conjInvariant this g
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
    have hZ : Subgroup.center Y = ⊥ :=
      InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
    have h1 := Nat.card_le_card_of_surjective
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R c ⊔
        (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y)))))
      (QuotientGroup.mk'_surjective _)
    have h2 := Subgroup.card_le_card_group (secH R c ⊔ (TwinADescent.coreAt c K').subgroupOf
      (Subgroup.centralizer ({c} : Set Y)))
    have h3 := TwinEdge.card_centralizer_lt_of_center hZ hc1
    rw [← h.card]
    omega
  have h4X := thm4_famX h4 hΩ hc2' h2 hq hA
    (secH R c ⊔ (TwinADescent.coreAt c K').subgroupOf (Subgroup.centralizer ({c} : Set Y))) hlt
  have hdich := dichotomy_abstract (TwinADescent.hypOmegaGen_coreFamily hΩ hc2') h4X hK₁Λ hK₂Λ hne
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

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
