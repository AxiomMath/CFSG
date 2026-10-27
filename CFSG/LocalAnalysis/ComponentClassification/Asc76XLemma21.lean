module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherStrongEmbedding

theorem involutionPointHull_eq_normalClosure {G : Type*} [Group G] (z : G) :
    involutionPointHull z = normalClosure ({z} : Set G) := by
  unfold involutionPointHull normalClosure
  congr 1
  ext t
  simp only [involutionPointClass, Set.mem_range, Group.mem_conjugatesOfSet_iff,
    Set.mem_singleton_iff, exists_eq_left, isConj_iff, rightConjugateElem]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by group⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by group⟩

theorem mem_involutionPointClass_iff {G : Type*} [Group G] {z t : G} :
    t ∈ involutionPointClass z ↔ IsConj z t := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [rightConjugateElem]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by simp [rightConjugateElem]⟩

theorem asc76Lemma21 :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G), standardComponentOddCore G = ⊥ →
      H ≠ ⊤ → z ∈ H → orderOf z = 2 → (∃! ω : G ⧸ H, z • ω = ω) →
      (∀ z₁ z₂ : G, IsConj z z₁ → IsConj z z₂ → z₁ ≠ z₂ → Commute z₁ z₂ →
        ∃! ω : G ⧸ H, (z₁ * z₂) • ω = ω) →
      let L : Subgroup G := normalClosure {z}
      ∃ u ∈ L, u ^ 2 = 1 ∧ u ∈ centralizer (L : Set G) ∧ zpowers u ⊓ ⁅L, L⁆ = ⊥ ∧
        zpowers u ⊔ ⁅L, L⁆ = L ∧ fusionStronglyEmbedded (H.subgroupOf ⁅L, L⁆) ∧
        ∀ t : G, IsConj z t → u⁻¹ * t ∈ ⁅L, L⁆ := by
  intro G _ _ H z hO hH hzH hz hfix hprod L
  have hL : involutionPointHull z = L := involutionPointHull_eq_normalClosure z
  rw [← hL]
  have hO' : CFSG.oddCore G = ⊥ := hO
  have hbase : z • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 :=
    class_mem_iff_fixes_base.mp hzH
  have huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H := by
    intro g
    constructor
    · intro hg
      obtain ⟨ω₀, -, hω₀⟩ := hfix
      have h1 : z • (QuotientGroup.mk g⁻¹ : G ⧸ H) = QuotientGroup.mk g⁻¹ := by
        rw [smul_mk_eq_mk_iff, inv_inv]
        rwa [mem_rightConjugate_iff] at hg
      have h2 := (hω₀ _ h1).trans (hω₀ _ hbase).symm
      rw [mk_eq_base_iff] at h2
      exact H.inv_mem_iff.mp h2
    · intro hg
      rw [mem_rightConjugate_iff]
      exact H.mul_mem (H.mul_mem hg hzH) (H.inv_mem hg)
  have hPUC : ProductUniqueContainment H z := by
    intro t ht hzt htz g
    obtain ⟨ω₀, hω₀, huω⟩ := hprod z t (IsConj.refl z) (mem_involutionPointClass_iff.mp ht)
      (Ne.symm htz) hzt
    have hzω : z • ω₀ = ω₀ := by
      apply huω
      rw [smul_smul, show z * t * z = z * (z * t) by rw [mul_assoc, ← hzt.eq], ← smul_smul,
        hω₀]
    have hω₀b : ω₀ = QuotientGroup.mk 1 := (smul_eq_iff_eq_base huniq ω₀).mp hzω
    rw [← smul_mk_eq_mk_iff]
    constructor
    · intro h
      have := huω _ h
      rwa [hω₀b, mk_eq_base_iff] at this
    · intro hg
      rw [(mk_eq_base_iff g).mpr hg, ← hω₀b]
      exact hω₀
  obtain ⟨h12, h23, -⟩ := theorem_3_3 not_minimalInvolutionPointLocalFailure
    benderDoubleCoverRigidity H z hz hH huniq
  have hcpc := h12 hPUC
  rcases h23 hcpc with hrank | ⟨u, hu2, hucen, hinf, hsup, hse, hclass⟩
  ·
    exfalso
    have hiso : ∀ t ∈ involutionPointClass z, Commute z t → t = z := by
      intro t ht hzt
      by_contra hne
      have hzL : z ∈ involutionPointHull z := subset_closure (distinguished_mem_pointClass z)
      have htL : t ∈ involutionPointHull z := subset_closure ht
      set s : involutionPointHull z := ⟨z, hzL⟩
      set s' : involutionPointHull z := ⟨t, htL⟩
      have hss : s * s = 1 := Subtype.ext (class_mul_self hz (distinguished_mem_pointClass z))
      have hss' : s' * s' = 1 := Subtype.ext (class_mul_self hz ht)
      have hst : Commute s s' := Subtype.ext hzt.eq
      have hs1 : s ≠ 1 := fun h => by
        have : z = 1 := congrArg Subtype.val h
        rw [this, orderOf_one] at hz
        exact absurd hz (by decide)
      have ht1 : s' ≠ 1 := fun h => by
        have h' : t = 1 := congrArg Subtype.val h
        have := class_orderOf hz ht
        rw [h', orderOf_one] at this
        exact absurd this (by decide)
      have hss'ne : s ≠ s' := fun h => hne (congrArg Subtype.val h).symm
      have hcard := commutingPairSubgroup_card (hs := hss) (ht := hss') (hst := hst) hs1 ht1
        hss'ne
      have hE : IsElemAbelian 2 (commutingPairSubgroup s s' hss hss' hst) :=
        ⟨CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one fun x =>
          Subtype.ext (commutingPairSubgroup_sq x.2), fun x hx => commutingPairSubgroup_sq hx⟩
      have := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary _ _ hE 2 hcard
      omega
    have hzc := mem_center_of_isolated hO' hz hcpc.1 hiso
    apply hH
    rw [eq_top_iff]
    intro g _
    rw [← huniq g, mem_rightConjugate_iff, mem_center_iff.mp hzc g, mul_inv_cancel_right]
    exact hzH
  ·
    have : (involutionPointHull z).Normal := by
      rw [involutionPointHull_eq_normalClosure]
      exact normalClosure_normal
    have hOL : CFSG.oddCore (involutionPointHull z) = ⊥ := oddCore_eq_bot_of_normal hO' _
    set q := QuotientGroup.mk' (CFSG.oddCore (involutionPointHull z)) with hqdef
    have hq : Function.Injective q := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hOL
    have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hqcomm : (commutator (involutionPointHull z)).map q =
        commutator (involutionPointHull z ⧸ CFSG.oddCore (involutionPointHull z)) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hqs, ← _root_.commutator_def]
    have hsubcomm := map_subtype_commutator (involutionPointHull z)
    refine ⟨u, u.2, by simpa using congrArg Subtype.val hu2, ?_, ?_, ?_, hse, fun t ht =>
      hclass t (mem_involutionPointClass_iff.mpr ht)⟩
    · rw [mem_centralizer_iff]
      intro h hh
      have hc := mem_center_iff.mp hucen (q ⟨h, hh⟩)
      rw [← map_mul, ← map_mul] at hc
      exact congrArg Subtype.val (hq hc)
    · rw [eq_bot_iff]
      rintro y ⟨hy1, hy2⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy1
      rw [← hsubcomm] at hy2
      obtain ⟨x, hx, hxe⟩ := hy2
      have hxu : x = u ^ n := Subtype.ext (by simpa using hxe)
      have hqx : q x ∈ zpowers (q u) ⊓
          commutator (involutionPointHull z ⧸ CFSG.oddCore (involutionPointHull z)) := by
        refine ⟨⟨n, by rw [hxu, map_zpow]⟩, ?_⟩
        rw [← hqcomm]
        exact mem_map_of_mem q hx
      rw [hinf, mem_bot, ← map_one q] at hqx
      have hx1 := hq hqx
      rw [hxu] at hx1
      rw [mem_bot]
      simpa using congrArg Subtype.val hx1
    · refine le_antisymm (sup_le (zpowers_le.mpr u.2) (commutator_le_self _)) ?_
      intro x hx
      have hmap : (zpowers u ⊔ commutator (involutionPointHull z)).map q = ⊤ := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, hqcomm, hsup]
      have hx' : q ⟨x, hx⟩ ∈ (zpowers u ⊔ commutator (involutionPointHull z)).map q := by
        rw [hmap]
        exact mem_top _
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = ⟨x, hx⟩ := hq hyx
      have hmem : x ∈ (zpowers u ⊔ commutator (involutionPointHull z)).map
          (involutionPointHull z).subtype := ⟨y, hy, by rw [hyx']; rfl⟩
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, hsubcomm] at hmem

end CFSG.ComponentClassification.Asc76X
