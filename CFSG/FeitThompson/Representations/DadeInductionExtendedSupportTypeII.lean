module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem isDadeData_congr [Finite G] {L : Subgroup G} {A : Set G} {H H' : G → Subgroup G}
    (hD : IsDadeData L A H) (h : ∀ a ∈ A, H' a = H a) : IsDadeData L A H' where
  subset_sdiff := hD.subset_sdiff
  conj_mem := hD.conj_mem
  fusion := hD.fusion
  le_centralizer := by intro a ha; rw [h a ha]; exact hD.le_centralizer ha
  normal_subgroupOf := by intro a ha; rw [h a ha]; exact hD.normal_subgroupOf ha
  inf_eq_bot := by intro a ha; rw [h a ha]; exact hD.inf_eq_bot ha
  mul_eq := by intro a ha; rw [h a ha]; exact hD.mul_eq ha
  coprime_card := by intro a ha b hb; rw [h a ha]; exact hD.coprime_card ha hb

theorem isTIWithNormalizer_of_normalizer_eq {A : Set G} {M : Subgroup G} (hne : A.Nonempty)
    (h1 : (1 : G) ∉ A) (hnorm : normalizer A = M)
    (hdisj : ∀ g : G, g ∉ M → A ∩ conjSet g A = ∅) : IsTIWithNormalizer A M where
  nonempty := hne
  one_notMem := h1
  normalizer_eq := hnorm
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ M := fun h => hg (by simpa using inv_mem h)
    have himg : conjSet g⁻¹ A = MulAut.conj g '' A := by
      refine Set.image_congr' fun x => ?_
      simp [mul_assoc]
    rw [Set.disjoint_iff_inter_eq_empty, ← himg]
    exact hdisj g⁻¹ hg'

theorem mem_classFun_restrict {M : Subgroup G} {f : G → ℂ}
    (hfc : ∀ m ∈ M, ∀ z : G, f (m⁻¹ * z * m) = f z) : (fun x : ↥M => f x) ∈ classFun ↥M := by
  refine mem_classFun.2 fun x y hxy => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  have hcG : (c : G) * (x : G) * (c : G)⁻¹ = (y : G) := by
    have := congrArg (Subtype.val (p := fun z => z ∈ M)) hc
    simpa using this
  have := hfc (c : G)⁻¹ (inv_mem c.2) (x : G)
  rw [inv_inv] at this
  rw [← hcG]
  exact this.symm

theorem dadeCoset_eq_singleton {H : G → Subgroup G} {a : G} (h : H a = ⊥) :
    dadeCoset H a = {a} := by
  ext x
  rw [mem_dadeCoset_iff, h, Subgroup.mem_bot, mul_inv_eq_one, Set.mem_singleton_iff]

theorem mem_dadeSupport_iff_of_trivial {J : G → Subgroup G} {a : G} (h : J a = ⊥) {g : G} :
    g ∈ dadeSupport J a ↔ IsConj a g := by
  rw [mem_dadeSupport_iff, dadeCoset_eq_singleton h]
  simp

theorem mem_totalDadeSupport_iff_of_trivial {A₀ : Set G} {J : G → Subgroup G}
    (hJ : ∀ a ∈ A₀, J a = ⊥) {g : G} :
    g ∈ totalDadeSupport A₀ J ↔ ∃ a ∈ A₀, IsConj a g := by
  rw [mem_totalDadeSupport_iff]
  refine ⟨fun ⟨a, ha, hx⟩ => ⟨a, ha, ?_⟩, fun ⟨a, ha, hc⟩ => ⟨a, ha, ?_⟩⟩
  · exact (mem_dadeSupport_iff_of_trivial (hJ a ha)).1 hx
  · exact (mem_dadeSupport_iff_of_trivial (hJ a ha)).2 hc

theorem extendByZero_restrict {M : Subgroup G} {f : G → ℂ} (hf : ∀ z : G, z ∉ M → f z = 0) :
    extendByZero M (fun x : ↥M => f x) = f := by
  funext x
  by_cases hx : x ∈ M
  · rw [extendByZero_of_mem _ hx]
  · rw [extendByZero_of_notMem M _ hx, hf x hx]

theorem dadeSupportExtension_eq_indClassFun [Fintype G] {M : Subgroup G} {A₀ : Set G}
    {J : G → Subgroup G} (hD : IsDadeData M A₀ J) (hTI : IsTIWithNormalizer A₀ M)
    {f : G → ℂ} (hf0 : ∀ z : G, z ∉ A₀ → f z = 0)
    (hfc : ∀ m ∈ M, ∀ z : G, f (m⁻¹ * z * m) = f z) :
    dadeSupportExtension A₀ J f = indClassFun M (fun x : ↥M => f x) := by
  have hfd : (fun x : ↥M => f x) ∈ dadeDomain M A₀ :=
    mem_dadeDomain.2 ⟨mem_classFun_restrict hfc, fun x hx => hf0 x hx⟩
  have hext : extendByZero M (fun x : ↥M => f x) = f :=
    extendByZero_restrict fun z hz => hf0 z fun h => hz (hD.subset h)
  have h1 := dadeMap_eq_indClassFun hD hTI subset_rfl (fun x : ↥M => f x) hfd
  rw [dadeMap_apply_coe, hext] at h1
  exact h1

theorem classFunInner_eq_cfInner (X : Type*) [Group X] [Fintype X] (f h : X → ℂ) :
    classFunInner X f h = cfInner f h := by
  rw [classFunInner_def, cfInner_def, finsum_eq_sum_of_fintype]

theorem inducedClassFun_eq_indClassFun [Fintype G] (M : Subgroup G) (f : G → ℂ) (g : G) :
    inducedClassFun M f g = indClassFun M (fun x : ↥M => f x) g := by
  classical
  rw [inducedClassFun_def, indClassFun_eq_sum_extendByZero]
  congr 1
  rw [show {x : G | x⁻¹ * g * x ∈ M}
      = ((({x : G | x⁻¹ * g * x ∈ M}).toFinset : Finset G) : Set G) from (Set.coe_toFinset _).symm,
    finsum_mem_coe_finset, Set.toFinset_ofPred, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x⁻¹ * g * x ∈ M
  · rw [if_pos hx, extendByZero_of_mem _ hx]
  · rw [if_neg hx, extendByZero_of_notMem M _ hx]

theorem FTS_type_II_extended_dade_induction
    (h₁ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₂ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FTS_type_II_extended_dade_induction.{u} := by
  intro G _ _ hG M E W₁ W₂ hM hMII hW A₀ hA₀
  have : Fintype G := Fintype.ofFinite _
  have : Fintype ↥M := Fintype.ofFinite _
  have hamb : IsFTAmbient G :=
    { isSimpleGroup := hG.isSimpleGroup
      not_isMulCommutative := hG.not_isMulCommutative
      odd_natCard := hG.odd_natCard
      isSolvable := hG.isSolvable_of_ne_top }
  obtain ⟨hHS, hne, hsub, hnorm, hdisj, hfus, hcent⟩ := h₂ G hG M E W₁ W₂ hM hMII hW A₀ hA₀
  have h1A : (1 : G) ∉ A₀ := fun h => (hsub h).2 rfl
  have hTI : IsTIWithNormalizer A₀ M :=
    isTIWithNormalizer_of_normalizer_eq hne h1A hnorm hdisj
  have hJ : ∀ a ∈ A₀, hallSignalizerOn M a = ⊥ := by
    intro a ha
    by_cases haH : a ∈ hallCoreIn M
    ·
      rw [hallSignalizerOn_of_mem haH]
      have ha1 : a ≠ 1 := fun h => (hsub ha).2 h
      have hasig : a ∈ sigmaCore M := hHS ▸ haH
      have haU : a ∈ sigmaSupport G := mem_sigmaSupport.2 ⟨M, hM, hasig, ha1⟩
      have hinf := ((h₁ G hamb a haU).2.2.2.2.1 M
        (mem_sigmaSupportingMaximals.2 ⟨hM, hasig⟩)).2
      have hle : sigmaSignalizer a ≤ M := by
        refine le_trans (sigmaSignalizer_le_centralizer a) ?_
        rw [hcent a ha]
        exact centIn_le M {a}
      exact le_antisymm (by rw [← hinf]; exact le_inf le_rfl hle) bot_le
    · exact hallSignalizerOn_of_notMem haH
  have hD : IsDadeData M A₀ (hallSignalizerOn M) := isDadeData_congr hTI.isDadeData hJ
  refine ⟨hJ, ?_, ?_, ?_, hne, h1A, ?_, hD, ?_, ?_, ?_⟩
  ·
    intro a ha
    refine ⟨by rw [hJ a ha]; exact bot_le, ?_, ?_, ?_, ?_⟩
    · rw [hJ a ha, Subgroup.bot_subgroupOf]; infer_instance
    · rw [hJ a ha, bot_sup_eq, hcent a ha]
    · rw [hJ a ha]
      exact le_top.trans (Subgroup.normalizer_eq_top (⊥ : Subgroup G)).ge
    · rw [hJ a ha]; exact disjoint_bot_left
  ·
    intro a ha b _
    rw [hJ a ha]
    simp
  ·
    intro a ha m hm
    have hmem := Subgroup.mem_normalizer_iff_conj_image_eq.1
      (hnorm ▸ (inv_mem hm) : m⁻¹ ∈ normalizer A₀)
    rw [← hmem]
    exact ⟨a, ha, by simp [MulAut.conj]⟩
  ·
    rintro a ha b hb ⟨g, hg⟩
    exact ⟨g, hfus a ha b hb g hg, hg⟩
  ·
    intro f hf0 hfc g
    have hind := dadeSupportExtension_eq_indClassFun hD hTI hf0 hfc
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro a ha hconj
      refine dadeSupportExtension_apply_of_mem_dadeSupport hD ?_ ha
        ((mem_dadeSupport_iff_of_trivial (hJ a ha)).2 hconj)
      intro b _ l hl
      have := hfc l⁻¹ (inv_mem hl) b
      rwa [inv_inv] at this
    · intro hgn
      refine dadeSupportExtension_eq_zero_of_notMem ?_
      intro hmem
      obtain ⟨a, ha, hc⟩ := (mem_totalDadeSupport_iff_of_trivial hJ).1 hmem
      exact hgn a ha hc
    · rw [hind, inducedClassFun_eq_indClassFun]
  ·
    intro f h hf0 hh0 hfc hhc
    rw [dadeSupportExtension_eq_indClassFun hD hTI hf0 hfc,
      dadeSupportExtension_eq_indClassFun hD hTI hh0 hhc,
      classFunInner_eq_cfInner, classFunInner_eq_cfInner]
    exact hTI.cfInner_indClassFun
      (mem_dadeDomain.2 ⟨mem_classFun_restrict hfc, fun x hx => hf0 x hx⟩)
      (mem_dadeDomain.2 ⟨mem_classFun_restrict hhc, fun x hx => hh0 x hx⟩)
  ·
    intro f hf0 hfc hfZ
    have hfd : (fun x : ↥M => f x) ∈ dadeZDomain M A₀ :=
      mem_dadeZDomain.2 ⟨hfZ, fun x hx => hf0 x hx⟩
    rw [dadeSupportExtension_eq_indClassFun hD hTI hf0 hfc]
    exact ⟨hTI.indClassFun_mem_virtualChars hfd,
      hTI.indClassFun_apply_one fun x hx => hf0 x hx⟩

end

end CFSG.FeitThompson.Proofs
