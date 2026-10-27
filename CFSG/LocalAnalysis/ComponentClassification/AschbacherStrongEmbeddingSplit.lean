module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem two_le_twoRank_hull {X : Type} [Group X] [Finite X] {H : Subgroup X} {z : X}
    (hz : orderOf z = 2) (hH : H ≠ ⊤) (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (hcentral : InvolutionPointCentralSylow z) (hO : CFSG.oddCore X = ⊥) :
    2 ≤ twoRank (involutionPointHull z) := by
  by_contra hlt
  have hle : twoRank (involutionPointHull z) ≤ 1 := by omega
  have hzL : z ∈ involutionPointHull z :=
    Subgroup.subset_closure (distinguished_mem_pointClass z)
  have hzc : z ∈ Subgroup.center X := by
    refine mem_center_of_isolated hO hz hcentral fun t ht hzt => ?_
    have htL : t ∈ involutionPointHull z := Subgroup.subset_closure ht
    have h := CFSG.TwoRankLowerBound.Helpers.commuting_involutions_eq_of_twoRank_le_one
      (involutionPointHull z) hle ⟨t, htL⟩ ⟨z, hzL⟩
      (by rw [Subgroup.orderOf_mk]; exact class_orderOf hz ht)
      (by rw [Subgroup.orderOf_mk]; exact hz) (Subtype.ext hzt.eq.symm)
    exact congrArg Subtype.val h
  apply hH
  refine eq_top_iff.mpr fun g _ => centralizer_le_of_unique huniq ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hzc g)

theorem split_of_pointHullStrongSplit {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    {z : X} (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (hcore : CFSG.oddCore (involutionPointHull z) = ⊥)
    (hrank : 2 ≤ twoRank (involutionPointHull z)) (h3 : PointHullStrongSplit H z) :
    ∃ u : X, u ^ 2 = 1 ∧
      ∃ e : involutionPointHull z ≃*
          Subgroup.zpowers u ×
            ↥(⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup X),
        fusionStronglyEmbedded
            (H.subgroupOf ⁅involutionPointHull z, involutionPointHull z⁆) ∧
          ∀ x : involutionPointHull z,
            (e x).2 ∈ H.subgroupOf ⁅involutionPointHull z, involutionPointHull z⁆ ↔
              (x : X) ∈ H := by
  rcases h3 with hlow | ⟨u, hu2, hucen, hinf, hsup, hse, -⟩
  · omega
  let L := involutionPointHull z
  let q := QuotientGroup.mk' (CFSG.oddCore L)
  have hinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcore
  have hcomm : ∀ g : L, u * g = g * u := by
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hucen (q g)).symm
  have hAL : Subgroup.zpowers (u : X) ≤ L := Subgroup.zpowers_le.mpr u.property
  have hBL : ⁅L, L⁆ ≤ L := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have hcommA : ∀ a ∈ Subgroup.zpowers (u : X), ∀ y ∈ L, a * y = y * a := by
    intro a ha y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h : Commute (u ^ k) (⟨y, hy⟩ : L) := (Commute.zpow_left (hcomm ⟨y, hy⟩) k)
    have h' := congrArg Subtype.val h.eq
    simpa only [Subgroup.coe_mul, Subgroup.coe_zpow] using h'
  have hzL : z ∈ L := Subgroup.subset_closure (distinguished_mem_pointClass z)
  have hAH : Subgroup.zpowers (u : X) ≤ H := by
    apply Subgroup.zpowers_le.mpr
    apply centralizer_le_of_unique huniq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (hcomm ⟨z, hzL⟩)
    simpa only [Subgroup.coe_mul] using h
  have hAB : Subgroup.zpowers (u : X) ⊓ ⁅L, L⁆ = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨hwA, hwB⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwA
    rw [← Subgroup.map_subtype_commutator] at hwB
    obtain ⟨c, hc, hcw⟩ := hwB
    have hcu : c = u ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hcw)
    have hqc : q c ∈ Subgroup.zpowers (q u) ⊓ commutator (L ⧸ CFSG.oddCore L) := by
      refine ⟨Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [hcu, map_zpow]⟩, ?_⟩
      rw [← commutator_map_quotient (X := L) (CFSG.oddCore L)]
      exact ⟨c, hc, rfl⟩
    rw [hinf] at hqc
    have hc1 : c = 1 := hinj (by rw [map_one]; exact Subgroup.mem_bot.mp hqc)
    rw [Subgroup.mem_bot, ← hcw, hc1]
    rfl
  let φ : Subgroup.zpowers (u : X) × ↥(⁅L, L⁆ : Subgroup X) →* L :=
    { toFun := fun p => ⟨(p.1 : X) * p.2, L.mul_mem (hAL p.1.property) (hBL p.2.property)⟩
      map_one' := by
        apply Subtype.ext
        simp only [Prod.fst_one, Prod.snd_one, Subgroup.coe_one, mul_one]
      map_mul' := by
        rintro ⟨a, b⟩ ⟨a', b'⟩
        apply Subtype.ext
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
        rw [mul_assoc, ← mul_assoc (a' : X), hcommA _ a'.property _ (hBL b.property)]
        simp only [mul_assoc] }
  have hφ : ∀ p, (φ p : X) = (p.1 : X) * p.2 := fun _ => rfl
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hp
    have h1 : (a : X) * b = 1 := congrArg Subtype.val hp
    have hab : (a : X) = (b : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have haB : (a : X) ∈ ⁅L, L⁆ := hab ▸ ⁅L, L⁆.inv_mem b.property
    have ha1 : (a : X) = 1 := by
      have h := (show (a : X) ∈ Subgroup.zpowers (u : X) ⊓ ⁅L, L⁆ from ⟨a.property, haB⟩)
      rwa [hAB, Subgroup.mem_bot] at h
    have hb1 : (b : X) = 1 := by rw [ha1, one_mul] at h1; exact h1
    exact Subgroup.mem_bot.mpr (Prod.ext (Subtype.ext ha1) (Subtype.ext hb1))
  have hφsurj : Function.Surjective φ := by
    intro x
    have hx : q x ∈ Subgroup.zpowers (q u) ⊔ commutator (L ⧸ CFSG.oddCore L) := by
      rw [hsup]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, c', hc', hyc⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← commutator_map_quotient (X := L) (CFSG.oddCore L)] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    have hxeq : x = u ^ k * c := hinj (by rw [map_mul, map_zpow]; exact hyc.symm)
    have hcB : (c : X) ∈ ⁅L, L⁆ := by
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨c, hc, rfl⟩
    refine ⟨(⟨(u : X) ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩⟩, ⟨(c : X), hcB⟩), ?_⟩
    apply Subtype.ext
    rw [hφ, hxeq, Subgroup.coe_mul, Subgroup.coe_zpow]
  let e : L ≃* Subgroup.zpowers (u : X) × ↥(⁅L, L⁆ : Subgroup X) :=
    (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm
  have he : ∀ x : L, φ (e x) = x := fun x => MulEquiv.ofBijective_apply_symm_apply φ ⟨hφinj, hφsurj⟩
  refine ⟨(u : X), by rw [← Subgroup.coe_pow, hu2]; rfl, e, hse, fun x => ?_⟩
  have hx : (x : X) = ((e x).1 : X) * (e x).2 := by
    rw [← hφ, he]
  rw [Subgroup.mem_subgroupOf, hx]
  exact (H.mul_mem_cancel_left (hAH (e x).1.property)).symm

theorem pointHull_split_of_centralProductCentralizer
    (himp : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G),
      ¬ MinimalInvolutionPointLocalFailure H z)
    (hcov : BenderDoubleCoverRigidity)
    {X : Type} [Group X] [Finite X] (H : Subgroup X) (z : X) (hz : orderOf z = 2)
    (hH : H ≠ ⊤) (huniq : ∀ g : X, z ∈ rightConjugate H g ↔ g ∈ H)
    (h2 : CentralProductCentralizer H z)
    (hcore : CFSG.oddCore (involutionPointHull z) = ⊥)
    (hrank : 2 ≤ twoRank (involutionPointHull z)) :
    ∃ u : X, u ^ 2 = 1 ∧
      ∃ e : involutionPointHull z ≃*
          Subgroup.zpowers u ×
            ↥(⁅involutionPointHull z, involutionPointHull z⁆ : Subgroup X),
        fusionStronglyEmbedded
            (H.subgroupOf ⁅involutionPointHull z, involutionPointHull z⁆) ∧
          ∀ x : involutionPointHull z,
            (e x).2 ∈ H.subgroupOf ⁅involutionPointHull z, involutionPointHull z⁆ ↔
              (x : X) ∈ H :=
  split_of_pointHullStrongSplit huniq hcore hrank
    ((theorem_3_3 himp hcov H z hz hH huniq).2.1 h2)

end CFSG.ComponentClassification.AschbacherStrongEmbedding
