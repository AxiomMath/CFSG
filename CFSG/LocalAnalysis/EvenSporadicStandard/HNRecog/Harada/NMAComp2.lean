module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMAComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMARCard

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} {n : G}

private lemma commute_zpowers_Fconj (h : Setting25 G t z z₁ ι zv R0 F) {a f : G}
    (ha : a ∈ zpowers (n * t * n⁻¹)) (hf : f ∈ Fconj n F) : a * f = f * a := by
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact Commute.zpow_left (conj_t_comm_Fconj h hf) e

private lemma zpowers_inf_Fconj_eq_bot (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) :
    zpowers (n * t * n⁻¹) ⊓ Fconj n F = ⊥ := by
  apply le_antisymm _ bot_le
  calc zpowers (n * t * n⁻¹) ⊓ Fconj n F
      ≤ ι.range ⊓ Fconj n F :=
        inf_le_inf (Subgroup.zpowers_le.mpr (conj_t_mem_range h hn)) le_rfl
    _ = Fconj n F ⊓ ι.range := inf_comm ..
    _ = ⊥ := Fconj_inf_range h hn

private lemma orderOf_conj_t (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) :
    orderOf (n * t * n⁻¹) = 2 :=
  orderOf_eq_prime (conj_t_sq h) (by
    intro h1
    exact conj_t_not_mem_Cgrp h hn hnz (by rw [h1]; exact one_mem _))

private lemma card_zpowers_conj_t (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) :
    Nat.card ↥(zpowers (n * t * n⁻¹)) = 2 := by
  rw [Nat.card_zpowers, orderOf_conj_t h hn hnz]

@[expose] def Qgrp (h : Setting25 G t z z₁ ι zv R0 F) (n : G) : Subgroup G where
  carrier := {x | ∃ a ∈ zpowers (n * t * n⁻¹), ∃ f ∈ Fconj n F, x = a * f}
  mul_mem' := by
    rintro a b ha hb
    rcases ha with ⟨a₁, ha₁, ha'⟩
    rcases ha' with ⟨f₁, hf₁, rfl⟩
    rcases hb with ⟨a₂, ha₂, hb'⟩
    rcases hb' with ⟨f₂, hf₂, rfl⟩
    refine ⟨a₁ * a₂, mul_mem ha₁ ha₂, f₁ * f₂, mul_mem hf₁ hf₂, ?_⟩
    have hca : f₁ * a₂ = a₂ * f₁ := (commute_zpowers_Fconj h ha₂ hf₁).symm
    calc (a₁ * f₁) * (a₂ * f₂)
        = a₁ * (f₁ * a₂) * f₂ := by group
      _ = a₁ * (a₂ * f₁) * f₂ := by rw [hca]
      _ = (a₁ * a₂) * (f₁ * f₂) := by group
  one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  inv_mem' := by
    rintro x hx
    rcases hx with ⟨a, ha, hx'⟩
    rcases hx' with ⟨f, hf, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, f⁻¹, inv_mem hf, ?_⟩
    rw [mul_inv_rev]
    exact (commute_zpowers_Fconj h (inv_mem ha) (inv_mem hf)).symm

theorem mem_Qgrp (h : Setting25 G t z z₁ ι zv R0 F) {x : G} :
    x ∈ Qgrp h n ↔ ∃ a ∈ zpowers (n * t * n⁻¹), ∃ f ∈ Fconj n F, x = a * f := Iff.rfl

private noncomputable def prodToQ (h : Setting25 G t z z₁ ι zv R0 F) :
    ↥(zpowers (n * t * n⁻¹)) × ↥(Fconj n F) →* ↥(Qgrp h n) where
  toFun p := ⟨(p.1 : G) * p.2, ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' := by
    intro p q
    apply Subtype.ext
    have hca : (q.1 : G) * p.2 = p.2 * (q.1 : G) := commute_zpowers_Fconj h q.1.2 p.2.2
    calc ((p.1 : G) * q.1) * ((p.2 : G) * q.2)
        = ((p.1 : G) * (q.1 * p.2)) * q.2 := by group
      _ = ((p.1 : G) * (p.2 * q.1)) * q.2 := by rw [hca]
      _ = ((p.1 : G) * p.2) * ((q.1 : G) * q.2) := by group

private lemma prodToQ_injective (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) :
    Function.Injective (prodToQ (n := n) (F := F) h) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ hpq
  have heq : (r : G) * q = (r' : G) * q' := by
    simpa [prodToQ] using Subtype.ext_iff.mp hpq
  have hcomm : (r' : G)⁻¹ * r = q' * (q : G)⁻¹ := by
    calc (r' : G)⁻¹ * r
        = (r' : G)⁻¹ * ((r : G) * q) * (q : G)⁻¹ := by group
      _ = (r' : G)⁻¹ * ((r' : G) * q') * (q : G)⁻¹ := by rw [heq]
      _ = q' * (q : G)⁻¹ := by group
  have hmem : (r' : G)⁻¹ * r ∈ (⊥ : Subgroup G) := by
    rw [← zpowers_inf_Fconj_eq_bot (F := F) h hn]
    exact Subgroup.mem_inf.mpr ⟨
      Subgroup.mul_mem (zpowers (n * t * n⁻¹))
        (Subgroup.inv_mem (zpowers (n * t * n⁻¹)) r'.2) r.2, by
          rw [hcomm]
          exact Subgroup.mul_mem (Fconj n F) q'.2 (Subgroup.inv_mem (Fconj n F) q.2)⟩
  have h1 : (r' : G)⁻¹ * r = 1 := by simpa using hmem
  have hr : (r : G) = (r' : G) := (inv_mul_eq_one.mp h1).symm
  have hq : (q : G) = (q' : G) := by
    have h2 := heq
    rw [hr] at h2
    exact mul_left_cancel h2
  exact Prod.ext (Subtype.ext hr) (Subtype.ext hq)

private lemma prodToQ_surjective (h : Setting25 G t z z₁ ι zv R0 F) :
    Function.Surjective (prodToQ (n := n) (F := F) h) := by
  rintro ⟨x, hx⟩
  rcases (mem_Qgrp h).mp hx with ⟨a, ha, hx'⟩
  rcases hx' with ⟨f, hf, rfl⟩
  exact ⟨(⟨a, ha⟩, ⟨f, hf⟩), rfl⟩

private noncomputable def QgrpMulEquiv (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) :
    ↥(Qgrp h n) ≃* ↥(zpowers (n * t * n⁻¹)) × ↥(Fconj n F) :=
  (MulEquiv.ofBijective (prodToQ (n := n) (F := F) h)
    ⟨prodToQ_injective h hn, prodToQ_surjective h⟩).symm

theorem Qgrp_le_K (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Qgrp h n ≤ Kgrp ι z := by
  intro x hx
  rcases (mem_Qgrp h).mp hx with ⟨a, ha, hx'⟩
  rcases hx' with ⟨f, hf, rfl⟩
  exact mul_mem
    (Subgroup.zpowers_le.mpr (Setting25.range_le_K h (conj_t_mem_range h hn)) ha)
    (Fconj_le_K h hn hnz hf)

theorem card_Qgrp (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Nat.card (Qgrp h n) = 120 := by
  calc Nat.card (Qgrp h n)
      = Nat.card (↥(zpowers (n * t * n⁻¹)) × ↥(Fconj n F)) :=
        Nat.card_congr (QgrpMulEquiv h hn).toEquiv
    _ = Nat.card ↥(zpowers (n * t * n⁻¹)) * Nat.card ↥(Fconj n F) := Nat.card_prod _ _
    _ = 2 * 60 := by rw [card_zpowers_conj_t h hn hnz, card_Fconj h]
    _ = 120 := by norm_num

theorem Qgrp_equiv (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) :
    Nonempty (↥(Qgrp h n) ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) := by
  have hM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hcard : Nat.card ↥(zpowers (n * t * n⁻¹)) =
      Nat.card (Multiplicative (ZMod 2)) := by
    rw [card_zpowers_conj_t h hn hnz, hM]
  exact ⟨(QgrpMulEquiv h hn).trans (MulEquiv.prodCongr
    (mulEquivOfCyclicCardEq hcard) (Classical.choice (Fconj_equiv h)))⟩

theorem Rgrp_disjoint_Qgrp (h : Setting25 G t z z₁ ι zv R0 F)
    (hn : n ∈ normalizer (ι.range : Set G)) (hnz : n * z₁ * n⁻¹ = z) :
    Disjoint (Rgrp h) (Qgrp h n) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxR, hxQ⟩
  rw [Subgroup.mem_bot]
  rcases (mem_Qgrp h).mp hxQ with ⟨a, ha, hx'⟩
  rcases hx' with ⟨f, hf, rfl⟩
  obtain ⟨u, hu⟩ := Rgrp_eichActs h hxR
  have ha_range : a ∈ ι.range :=
    Subgroup.zpowers_le.mpr (conj_t_mem_range h hn) ha
  have hEa : EichActs ι zv a 0 := EichActs.of_mem_range (w := zv) (ι := ι) ha_range
  have hEf : EichActs ι zv f u := by
    have hmul := hEa.inv.mul hu
    have heq : a⁻¹ * (a * f) = f := by group
    rw [heq] at hmul
    simpa using hmul
  have hf1 : f = 1 := Fconj_eichActs_eq_one h hn hnz hf ⟨u, hEf⟩
  rw [hf1, mul_one]
  have ha_R : a ∈ Rgrp h := by
    have h := hxR
    rw [hf1, mul_one] at h
    exact h
  have ha_C : a ∈ Cgrp ι zv := by
    have hmem : a ∈ Rgrp h ⊓ ι.range := ⟨ha_R, ha_range⟩
    rwa [Rgrp_inf_range h] at hmem
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hmod : a = (n * t * n⁻¹) ^ (e % 2) := by
    rw [← he]
    have hz := zpow_mod_orderOf (n * t * n⁻¹) e
    rw [orderOf_conj_t h hn hnz] at hz
    exact hz.symm
  rcases Int.emod_two_eq_zero_or_one e with h0 | h1
  · rw [hmod, h0]; simp
  · exfalso
    have hav : a = n * t * n⁻¹ := by rw [hmod, h1]; simp
    rw [hav] at ha_C
    exact (conj_t_not_mem_Cgrp h hn hnz) ha_C

theorem Rgrp_sup_Qgrp (h : Setting25 G t z z₁ ι zv R0 F) (hn : n ∈ normalizer (ι.range : Set G))
    (hnz : n * z₁ * n⁻¹ = z) : Rgrp h ⊔ Qgrp h n = Kgrp ι z := by
  apply le_antisymm
  · exact sup_le (Rgrp_le_K h) (Qgrp_le_K h hn hnz)
  · intro k hk
    let φ : ↥(Rgrp h) × ↥(Qgrp h n) → ↥(Kgrp ι z) :=
      fun p => ⟨p.1 * p.2,
        mul_mem (Rgrp_le_K h p.1.2) (Qgrp_le_K h hn hnz p.2.2)⟩
    have hinj : Function.Injective φ := by
      rintro ⟨r, q⟩ ⟨r', q'⟩ hpq
      have heq : (r : G) * q = (r' : G) * q' := by
        simpa [φ] using Subtype.ext_iff.mp hpq
      have hcomm : (r' : G)⁻¹ * r = q' * (q : G)⁻¹ := by
        calc (r' : G)⁻¹ * r
            = (r' : G)⁻¹ * ((r : G) * q) * (q : G)⁻¹ := by group
          _ = (r' : G)⁻¹ * ((r' : G) * q') * (q : G)⁻¹ := by rw [heq]
          _ = q' * (q : G)⁻¹ := by group
      have hle := disjoint_iff_inf_le.mp (Rgrp_disjoint_Qgrp h hn hnz)
      have h1 : (r' : G)⁻¹ * r = 1 := by
        have hmem : (r' : G)⁻¹ * r ∈ (⊥ : Subgroup G) :=
          hle (Subgroup.mem_inf.mpr ⟨
            Subgroup.mul_mem (Rgrp h) (Subgroup.inv_mem (Rgrp h) r'.2) r.2, by
              rw [hcomm]
              exact Subgroup.mul_mem (Qgrp h n) q'.2 (Subgroup.inv_mem (Qgrp h n) q.2)⟩)
        simpa using hmem
      have hr : (r : G) = (r' : G) := (inv_mul_eq_one.mp h1).symm
      have hq : (q : G) = (q' : G) := by
        have h2 := heq
        rw [hr] at h2
        exact mul_left_cancel h2
      exact Prod.ext (Subtype.ext hr) (Subtype.ext hq)
    have hcard : Nat.card (↥(Rgrp h) × ↥(Qgrp h n)) = Nat.card ↥(Kgrp ι z) := by
      rw [Nat.card_prod, card_Rgrp h, card_Qgrp h hn hnz, Setting25.card_K h]
      norm_num
    have hsurj : Function.Surjective φ :=
      ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩).2
    obtain ⟨p, hp⟩ := hsurj ⟨k, hk⟩
    have hp' : (p.1 : G) * p.2 = k := by simpa [φ] using Subtype.ext_iff.mp hp
    rw [← hp']
    exact Subgroup.mul_mem_sup p.1.2 p.2.2

end CFSG.EvenSporadicStandard.HNRecog.Harada
