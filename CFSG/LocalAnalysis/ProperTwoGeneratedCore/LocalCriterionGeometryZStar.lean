module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryEmbedding

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u v

variable {G : Type u} [Group G]

@[expose] def pairPointStabilizer (H : Subgroup G) (beta : rightCosetSpace H) :
    Subgroup G :=
  rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta

@[expose] def pairFlipGroup (H : Subgroup G) (beta : rightCosetSpace H) (t : G) :
    Subgroup G :=
  pairPointStabilizer H beta ⊔ Subgroup.zpowers t

theorem pairPointStabilizer_le_point (H : Subgroup G) (beta : rightCosetSpace H) :
    pairPointStabilizer H beta ≤ H := by
  unfold pairPointStabilizer
  rw [rightCosetStabilizer_base]
  exact inf_le_left

theorem pairPointStabilizer_le_pairFlipGroup
    (H : Subgroup G) (beta : rightCosetSpace H) (t : G) :
    pairPointStabilizer H beta ≤ pairFlipGroup H beta t := le_sup_left

theorem flip_mem_pairFlipGroup (H : Subgroup G) (beta : rightCosetSpace H) (t : G) :
    t ∈ pairFlipGroup H beta t :=
  (show Subgroup.zpowers t ≤ pairFlipGroup H beta t from le_sup_right)
    (Subgroup.mem_zpowers t)

private theorem flip_left_image {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (ht : t ∈ rightPairFlipFiber H z beta) :
    t • (QuotientGroup.mk 1 : conjugateCosetSpace H) =
      QuotientGroup.quotientRightRelEquivQuotientLeftRel H beta := by
  have hbase : QuotientGroup.quotientRightRelEquivQuotientLeftRel H
      (rightCosetMk H 1) = (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  have h := congrArg (QuotientGroup.quotientRightRelEquivQuotientLeftRel H) ht.2
  rw [rightCosetTranslate_inversion,
    inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass hz ht.1)] at h
  rwa [hbase] at h

private theorem flip_mem_of_left_image {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (htclass : t ∈ involutionPointClass z)
    (htimage : t • (QuotientGroup.mk 1 : conjugateCosetSpace H) =
      QuotientGroup.quotientRightRelEquivQuotientLeftRel H beta) :
    t ∈ rightPairFlipFiber H z beta := by
  have hbase : QuotientGroup.quotientRightRelEquivQuotientLeftRel H
      (rightCosetMk H 1) = (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  refine ⟨htclass, (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).injective ?_⟩
  rw [rightCosetTranslate_inversion,
    inv_eq_self_of_orderOf_eq_two (order_two_of_mem_pointClass hz htclass)]
  rwa [hbase]

theorem pair_flip_not_mem_point {H : Subgroup G} {z t : G}
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (ht : t ∈ rightPairFlipFiber H z beta) : t ∉ H := by
  intro htH
  have htfix := (mem_rightCosetStabilizer_iff H (rightCosetMk H 1) t).mp
    ((rightCosetStabilizer_base H).symm ▸ htH)
  exact hbeta (ht.2.symm.trans htfix)

theorem pair_flip_product_mem {H : Subgroup G} {z t s : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (ht : t ∈ rightPairFlipFiber H z beta)
    (hs : s ∈ rightPairFlipFiber H z beta) :
    s * t ∈ pairPointStabilizer H beta := by
  have hbase : QuotientGroup.quotientRightRelEquivQuotientLeftRel H
      (rightCosetMk H 1) = (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  change s * t ∈ MulAction.stabilizer G
      (QuotientGroup.quotientRightRelEquivQuotientLeftRel H (rightCosetMk H 1)) ⊓
    MulAction.stabilizer G (QuotientGroup.quotientRightRelEquivQuotientLeftRel H beta)
  rw [hbase]
  exact flip_product_mem_two_point_stabilizer
    (order_two_of_mem_pointClass hz hs.1) (order_two_of_mem_pointClass hz ht.1)
    (flip_left_image hz hs) (flip_left_image hz ht)

theorem pair_flip_mem_group {H : Subgroup G} {z t s : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (ht : t ∈ rightPairFlipFiber H z beta)
    (hs : s ∈ rightPairFlipFiber H z beta) : s ∈ pairFlipGroup H beta t := by
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp
      (order_two_of_mem_pointClass hz ht.1)).1
  have hprod := (pairFlipGroup H beta t).mul_mem
    (pairPointStabilizer_le_pairFlipGroup H beta t (pair_flip_product_mem hz ht hs))
    (flip_mem_pairFlipGroup H beta t)
  simpa only [mul_assoc, htt, mul_one] using hprod

private theorem pair_setwise_alternatives {Ω : Type v} [MulAction G Ω]
    {a b : Ω} (hba : b ≠ a) {g : G}
    (hg : g ∈ MulAction.stabilizer G ({a, b} : Set Ω)) :
    (g • a = a ∧ g • b = b) ∨ (g • a = b ∧ g • b = a) := by
  have hfinite : ({a, b} : Set Ω).Finite := (Set.finite_singleton _).insert _
  have hga := (MulAction.mem_stabilizer_set' hfinite).mp hg (Set.mem_insert a {b})
  have hgb := (MulAction.mem_stabilizer_set' hfinite).mp hg
    (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hga hgb
  rcases hga with hga | hga
  · refine Or.inl ⟨hga, ?_⟩
    rcases hgb with hgb | hgb
    · exact False.elim (hba (smul_left_cancel g (hgb.trans hga.symm)))
    · exact hgb
  · refine Or.inr ⟨hga, ?_⟩
    rcases hgb with hgb | hgb
    · exact hgb
    · exact False.elim (hba (smul_left_cancel g (hgb.trans hga.symm)))

private theorem pair_group_le_setwise {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (ht : t ∈ rightPairFlipFiber H z beta) :
    pairFlipGroup H beta t ≤ MulAction.stabilizer G
      ({(QuotientGroup.mk 1 : conjugateCosetSpace H),
        QuotientGroup.quotientRightRelEquivQuotientLeftRel H beta} : Set _) := by
  let a : conjugateCosetSpace H := QuotientGroup.mk 1
  let b := QuotientGroup.quotientRightRelEquivQuotientLeftRel H beta
  have hfinite : ({a, b} : Set (conjugateCosetSpace H)).Finite :=
    (Set.finite_singleton _).insert _
  have hbase : QuotientGroup.quotientRightRelEquivQuotientLeftRel H
      (rightCosetMk H 1) = a := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  have hB : pairPointStabilizer H beta ≤ MulAction.stabilizer G ({a, b} : Set _) := by
    rintro g hg
    have hga : g • a = a := by
      apply MulAction.mem_stabilizer_iff.mp
      have hgbase : g ∈ MulAction.stabilizer G
          (QuotientGroup.quotientRightRelEquivQuotientLeftRel H (rightCosetMk H 1)) :=
        hg.1
      rwa [hbase] at hgbase
    have hgb : g • b = b := MulAction.mem_stabilizer_iff.mp hg.2
    apply (MulAction.mem_stabilizer_set' hfinite).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl hga
    · exact Or.inr hgb
  have htimage : t • a = b := flip_left_image hz ht
  have htreturn : t • b = a := involution_flips_pair
    (order_two_of_mem_pointClass hz ht.1) htimage
  apply sup_le hB
  apply Subgroup.zpowers_le.mpr
  apply (MulAction.mem_stabilizer_set' hfinite).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inr htimage
  · exact Or.inl htreturn

theorem pair_group_index_two {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta) :
    (pairPointStabilizer H beta).relIndex (pairFlipGroup H beta t) = 2 := by
  let a : conjugateCosetSpace H := QuotientGroup.mk 1
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  let b := e beta
  have hbase : e (rightCosetMk H 1) = a := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  have hba : b ≠ a := fun heq => hbeta (e.injective (heq.trans hbase.symm))
  have htimage : t • a = b := flip_left_image hz ht
  have htreturn : t • b = a := involution_flips_pair
    (order_two_of_mem_pointClass hz ht.1) htimage
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨t, flip_mem_pairFlipGroup H beta t, ?_, ?_⟩
  · exact fun htB => pair_flip_not_mem_point hbeta ht
      (pairPointStabilizer_le_point H beta htB)
  · intro g hg
    rcases pair_setwise_alternatives hba (pair_group_le_setwise hz ht hg) with
      ⟨hga, hgb⟩ | ⟨hga, hgb⟩
    · apply Or.inr
      change g ∈ MulAction.stabilizer G (e (rightCosetMk H 1)) ⊓
        MulAction.stabilizer G b
      rw [hbase]
      exact ⟨MulAction.mem_stabilizer_iff.mpr hga, MulAction.mem_stabilizer_iff.mpr hgb⟩
    · apply Or.inl
      change g * t ∈ MulAction.stabilizer G (e (rightCosetMk H 1)) ⊓
        MulAction.stabilizer G b
      rw [hbase]
      constructor
      · exact MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, htimage, hgb])
      · exact MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, htreturn, hga])

theorem pair_stabilizer_normal {H : Subgroup G} {z t : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta) :
    ((pairPointStabilizer H beta).subgroupOf (pairFlipGroup H beta t)).Normal :=
  Subgroup.normal_of_index_eq_two (pair_group_index_two hz hbeta ht)

theorem pointClass_right_conjugate_mem {z s : G}
    (hs : s ∈ involutionPointClass z) (g : G) :
    rightConjugateElem s g ∈ involutionPointClass z := by
  obtain ⟨a, rfl⟩ := hs
  refine ⟨a * g, ?_⟩
  simp only [rightConjugateElem, mul_inv_rev, mul_assoc]

theorem pair_group_conjugate_flip_mem {H : Subgroup G} {z t s g : G}
    (hz : orderOf z = 2) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta)
    (hs : s ∈ rightPairFlipFiber H z beta) (hg : g ∈ pairFlipGroup H beta t) :
    rightConjugateElem s g ∈ rightPairFlipFiber H z beta := by
  let a : conjugateCosetSpace H := QuotientGroup.mk 1
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  let b := e beta
  have hbase : e (rightCosetMk H 1) = a := by
    change (QuotientGroup.mk ((1 : G)⁻¹) : G ⧸ H) = QuotientGroup.mk 1
    rw [inv_one]
  have hba : b ≠ a := fun heq => hbeta (e.injective (heq.trans hbase.symm))
  have hsimage : s • a = b := flip_left_image hz hs
  have hsreturn : s • b = a := involution_flips_pair
    (order_two_of_mem_pointClass hz hs.1) hsimage
  apply flip_mem_of_left_image hz (pointClass_right_conjugate_mem hs.1 g)
  change (g⁻¹ * s * g) • a = b
  rcases pair_setwise_alternatives hba (pair_group_le_setwise hz ht hg) with
    ⟨hga, hgb⟩ | ⟨hga, hgb⟩
  · rw [mul_smul, mul_smul, hga, hsimage]
    simpa only [inv_smul_smul] using
      (congrArg (fun x : conjugateCosetSpace H => g⁻¹ • x) hgb).symm
  · rw [mul_smul, mul_smul, hga, hsreturn]
    simpa only [inv_smul_smul] using
      (congrArg (fun x : conjugateCosetSpace H => g⁻¹ • x) hgb).symm

theorem involution_conjugate_into_sylow [Finite G] (S : Sylow 2 G)
    {x : G} (hx : orderOf x = 2) :
    ∃ g : G, g⁻¹ * x * g ∈ (S : Subgroup G) := by
  have hcyclic : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨Q, hQ⟩ := hcyclic.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hmem : MulAut.conj g • x ∈ ((g • Q : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers x))
  rw [hg] at hmem
  refine ⟨g⁻¹, ?_⟩
  simpa only [MulAut.smul_def, MulAut.conj_apply, inv_inv] using hmem

theorem central_sylow_le_point {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (S : Sylow 2 G)
    (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) ∧ (S : Subgroup G) ≤ H := by
  have hcentral : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzcenter)
      (⟨x, hx⟩ : (S : Subgroup G)))
  exact ⟨hcentral, hcentral.trans (point_centralizer_le h)⟩

theorem pair_flips_commute_iff_eq [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t s : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hs : s ∈ rightPairFlipFiber H z beta) : Commute t s ↔ t = s := by
  constructor
  · intro hcomm
    by_contra hne
    have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
    have hsorder := order_two_of_mem_pointClass h.distinguished_order hs.1
    have htt : t * t = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
    have hss : s * s = 1 := by
      simpa only [pow_two] using (orderOf_eq_prime_iff.mp hsorder).1
    have hprodne : t * s ≠ 1 := by
      intro heq
      exact hne ((mul_eq_one_iff_eq_inv.mp heq).trans
        (inv_eq_self_of_orderOf_eq_two hsorder))
    have hprodorder : orderOf (t * s) = 2 := by
      apply orderOf_eq_prime_iff.mpr
      refine ⟨?_, hprodne⟩
      rw [pow_two, ← mul_assoc, mul_assoc t s t, hcomm.eq.symm,
        ← mul_assoc, htt, one_mul, hss]
    have hprodH := pairPointStabilizer_le_point H beta
      (pair_flip_product_mem h.distinguished_order hs ht)
    obtain ⟨hcentral, hSH⟩ := central_sylow_le_point h S hzS hzcenter
    let uH : H := ⟨t * s, hprodH⟩
    have huH : orderOf uH = 2 := (Subgroup.orderOf_coe uH).symm.trans hprodorder
    obtain ⟨a, ha⟩ := involution_conjugate_into_sylow (S.subtype hSH) huH
    have hprodS : (a : G)⁻¹ * (t * s) * a ∈ (S : Subgroup G) := by
      simpa only [Sylow.coe_subtype, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_inv, uH] using ha
    have hproduct : rightConjugateElem t (a : G) * rightConjugateElem s (a : G) =
        (a : G)⁻¹ * (t * s) * a := by
      simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]
    have hconjnotone : rightConjugateElem t (a : G) * rightConjugateElem s (a : G) ≠ 1 := by
      rw [hproduct]
      intro hone
      have heq := congrArg (fun x : G => (a : G) * x * (a : G)⁻¹) hone
      exact hprodne (by simpa only [mul_assoc, mul_inv_cancel_left,
        mul_inv_cancel_right, mul_one, one_mul, mul_inv_cancel] using heq)
    have hconjcentral : Commute
        (rightConjugateElem t (a : G) * rightConjugateElem s (a : G)) z := by
      apply Subgroup.mem_centralizer_singleton_iff.mp
      rw [hproduct]
      exact hcentral hprodS
    have htconjH := (pointClass_factors_mem_of_product_centralizing h
      (pointClass_right_conjugate_mem ht.1 a) (pointClass_right_conjugate_mem hs.1 a)
      hconjnotone hconjcentral).1
    have htH : t ∈ H := by
      have hmem := H.mul_mem (H.mul_mem a.property htconjH) (H.inv_mem a.property)
      simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left,
        mul_inv_cancel_right, mul_inv_cancel, mul_one] using hmem
    exact pair_flip_not_mem_point hbeta ht htH
  · rintro rfl
    exact Commute.refl t

theorem central_of_no_distinct_commuting_conjugate
    {P : Type v} [Group P] [Finite P] (hP : IsPGroup 2 P) (t : P)
    (hisolated : ∀ g : P, Commute (g⁻¹ * t * g) t → g⁻¹ * t * g = t) :
    t ∈ Subgroup.center P := by
  let C := Subgroup.centralizer ({t} : Set P)
  have hnormalizer : Subgroup.normalizer (C : Set P) = C := by
    apply le_antisymm _ C.le_normalizer
    intro g hg
    have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl t)
    have htconjC : g⁻¹ * t * g ∈ C := by
      have hh := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (C : Set P)).inv_mem hg) t).mp htC
      simpa only [inv_inv] using hh
    have heq := hisolated g (Subgroup.mem_centralizer_singleton_iff.mp htconjC)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun x : P => g * x) heq
    simpa only [mul_assoc, mul_inv_cancel_left] using hh.symm
  let : Group.IsNilpotent P := hP.isNilpotent
  have hCtop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P))) C hnormalizer
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (hCtop ▸ (Subgroup.mem_top g) : g ∈ C)

theorem pair_flip_central_and_weakly_closed [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (P : Sylow 2 (pairFlipGroup H beta t))
    (htP : (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) ∈
      (P : Subgroup (pairFlipGroup H beta t))) :
    (⟨⟨t, flip_mem_pairFlipGroup H beta t⟩, htP⟩ :
        (P : Subgroup (pairFlipGroup H beta t))) ∈
      Subgroup.center (P : Subgroup (pairFlipGroup H beta t)) ∧
    ∀ g : pairFlipGroup H beta t,
      g⁻¹ * (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) * g ∈
          (P : Subgroup (pairFlipGroup H beta t)) →
        g⁻¹ * (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) * g =
          (⟨t, flip_mem_pairFlipGroup H beta t⟩ : pairFlipGroup H beta t) := by
  let tK : pairFlipGroup H beta t := ⟨t, flip_mem_pairFlipGroup H beta t⟩
  let tP : (P : Subgroup (pairFlipGroup H beta t)) := ⟨tK, htP⟩
  have hisolatedP : ∀ g : (P : Subgroup (pairFlipGroup H beta t)),
      Commute (g⁻¹ * tP * g) tP → g⁻¹ * tP * g = tP := by
    intro g hcomm
    have hcg : Commute
        (rightConjugateElem t ((g : pairFlipGroup H beta t) : G)) t := by
      exact congrArg (fun x : (P : Subgroup (pairFlipGroup H beta t)) =>
        ((x : pairFlipGroup H beta t) : G)) hcomm.eq
    have heq := (pair_flips_commute_iff_eq h S hzS hzcenter hbeta
      (pair_group_conjugate_flip_mem h.distinguished_order hbeta ht ht g.val.property)
      ht).mp hcg
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hcenter := central_of_no_distinct_commuting_conjugate P.isPGroup' tP hisolatedP
  refine ⟨hcenter, ?_⟩
  intro g hg
  have hcg : Commute (rightConjugateElem t (g : G)) t := by
    change (g : G)⁻¹ * t * g * t = t * ((g : G)⁻¹ * t * g)
    exact congrArg (fun x : (P : Subgroup (pairFlipGroup H beta t)) =>
      ((x : pairFlipGroup H beta t) : G)) ((Subgroup.mem_center_iff.mp hcenter)
      (⟨g⁻¹ * tK * g, hg⟩ : (P : Subgroup (pairFlipGroup H beta t))))
  apply Subtype.ext
  exact (pair_flips_commute_iff_eq h S hzS hzcenter hbeta
    (pair_group_conjugate_flip_mem h.distinguished_order hbeta ht ht g.property) ht).mp hcg

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
