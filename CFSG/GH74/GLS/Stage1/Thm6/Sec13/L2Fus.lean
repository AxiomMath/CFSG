module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2U

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

section CosetForm

variable {M N : Subgroup G} [(N.subgroupOf M).Normal]

theorem coset_form (hMn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (h : qm M N ⟨a, ha⟩ = qm M N ⟨b, hb⟩) : ∃ p ∈ N, a = p * b := by
  have hu : a⁻¹ * b ∈ N := qm_eq_iff.1 h
  refine ⟨b * (a⁻¹ * b)⁻¹ * b⁻¹, hMn b hb _ (N.inv_mem hu), by group⟩

end CosetForm

namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem exists_Hs_not_H [Finite G] (hT16 : Nat.card T = 16) : ∃ g : G, g ∈ H ⊔ T ∧ g ∉ H := by
  have hTH : ¬ T ≤ H := by
    intro h
    have : T ≤ EV x V := by
      rw [← c.c2.c3.hp.T_inter]
      exact le_inf le_rfl h
    have := Subgroup.card_le_of_le this
    rw [c.c2.c3.out.card_EV] at this
    omega
  obtain ⟨t, htT, htH⟩ := IsConcreteLE.not_le_iff_exists.1 hTH
  exact ⟨t, Subgroup.mem_sup_right htT, htH⟩

end Ctx2S


namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem Hs_classes [Finite G] (h64 : Nat.card ↥(H ⊔ T) = 64) (hsq : ∀ s ∈ H ⊔ T, s * s ∈ Hzero H f)
    {g₁ : G} (hg₁S : g₁ ∈ H ⊔ T) (hg₁H : g₁ ∉ H) :
    ∀ s ∈ H ⊔ T, ∃ p ∈ Hzero H f, s = p ∨ s = p * x ∨ s = p * g₁ ∨ s = p * (x * g₁) := by
  classical
  have hP := c.c2.c3
  have hn := c.normIn_Hs
  have := hn.normal
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  have hg₁P : g₁ ∉ Hzero H f := fun h => hg₁H (hP.H0_le h)
  have hRcard : Nat.card (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) = 4 := by
    have := card_QR (M := H ⊔ T) (N := Hzero H f) hn.le
    rw [c.c2.P_card, h64] at this
    omega
  have hR2 : ∀ r : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T), r * r = 1 := by
    intro r
    obtain ⟨⟨s, hs⟩, rfl⟩ := (QuotientGroup.mk'_surjective _) r
    show qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ * qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩ = 1
    rw [← map_mul]
    exact qm_eq_one.2 (hsq s hs)
  let xb : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T) := qm (H ⊔ T) (Hzero H f) ⟨x, hxS⟩
  let gb : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T) := qm (H ⊔ T) (Hzero H f) ⟨g₁, hg₁S⟩
  have hxb1 : xb ≠ 1 := fun h => hP.x_notin_H0 (qm_eq_one.1 h)
  have hgb1 : gb ≠ 1 := fun h => hg₁P (qm_eq_one.1 h)
  have hxgb : xb ≠ gb := by
    intro h
    have h1 : x⁻¹ * g₁ ∈ Hzero H f := qm_eq_iff.1 h
    apply hg₁H
    have : g₁ = x * (x⁻¹ * g₁) := by group
    rw [this]
    exact H.mul_mem hP.x_mem_H (hP.H0_le h1)
  have hgbi : gb⁻¹ = gb := inv_eq_of_mul_eq_one_right (hR2 gb)
  have hR4 : ∀ r : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T),
      r = 1 ∨ r = xb ∨ r = gb ∨ r = xb * gb := by
    intro r
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    have : Fintype (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) := Fintype.ofFinite _
    have hmem : ({1, xb, gb, xb * gb, r} : Finset (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))).card = 5 := by
      have e1 : (1 : ↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)) ∉ ({xb, gb, xb * gb, r} : Finset _) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hxb1.symm, hgb1.symm, ?_, h1.symm⟩
        intro h
        apply hxgb
        have : xb = gb⁻¹ := eq_inv_of_mul_eq_one_left h.symm
        rw [this, hgbi]
      have e2 : xb ∉ ({gb, xb * gb, r} : Finset (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hxgb, ?_, h2.symm⟩
        intro h
        apply hgb1
        have := congrArg (fun t => xb⁻¹ * t) h
        simpa using this.symm
      have e3 : gb ∉ ({xb * gb, r} : Finset (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, h3.symm⟩
        intro h
        apply hxb1
        have := congrArg (fun t => t * gb⁻¹) h
        simpa using this.symm
      have e4 : xb * gb ∉ ({r} : Finset (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T))) := by
        simp only [Finset.mem_singleton]
        exact h4.symm
      rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
        Finset.card_insert_of_notMem e3, Finset.card_insert_of_notMem e4, Finset.card_singleton]
    have := Finset.card_le_univ ({1, xb, gb, xb * gb, r} : Finset (↥(H ⊔ T) ⧸ (Hzero H f).subgroupOf (H ⊔ T)))
    rw [← Nat.card_eq_fintype_card, hRcard] at this
    omega
  have hxg₁S : x * g₁ ∈ H ⊔ T := (H ⊔ T).mul_mem hxS hg₁S
  have hxg : qm (H ⊔ T) (Hzero H f) ⟨x * g₁, hxg₁S⟩ = xb * gb := by
    rw [show (⟨x * g₁, hxg₁S⟩ : ↥(H ⊔ T)) = ⟨x, hxS⟩ * ⟨g₁, hg₁S⟩ from rfl, map_mul]
  intro s hs
  rcases hR4 (qm (H ⊔ T) (Hzero H f) ⟨s, hs⟩) with h | h | h | h
  · exact ⟨s, qm_eq_one.1 h, Or.inl (by simp)⟩
  · obtain ⟨p, hp, hsp⟩ := coset_form c.hPT hs hxS h
    exact ⟨p, hp, Or.inr (Or.inl hsp)⟩
  · obtain ⟨p, hp, hsp⟩ := coset_form c.hPT hs hg₁S h
    exact ⟨p, hp, Or.inr (Or.inr (Or.inl hsp))⟩
  · obtain ⟨p, hp, hsp⟩ := coset_form c.hPT hs hxg₁S (h.trans hxg.symm)
    exact ⟨p, hp, Or.inr (Or.inr (Or.inr hsp))⟩

theorem exists_free_reps [Finite G] (h15 : IG_15_15) (hSeq : S = H ⊔ T) (hT16 : Nat.card T = 16)
    (h64 : Nat.card ↥(H ⊔ T) = 64) (hsq : ∀ s ∈ H ⊔ T, s * s ∈ Hzero H f) :
    ∃ y₁ : G, IsFreeConj x (Hzero H f) y₁ ∧ y₁ ∈ H ⊔ T ∧ y₁ ∉ H ∧
      (∀ s ∈ H ⊔ T, ∃ p ∈ Hzero H f, s = p ∨ s = p * x ∨ s = p * y₁ ∨ s = p * (x * y₁)) ∧
      ∀ s ∈ H ⊔ T, s ∉ Hzero H f →
        ∃ y' : G, IsFreeConj x (Hzero H f) y' ∧ ∃ p ∈ Hzero H f, s = p * y' := by
  classical
  have hP := c.c2.c3
  have hn := c.normIn_Hs
  have := hn.normal
  have hS : Sylow2In (H ⊔ T) ⊤ := hSeq ▸ c.syl
  have hxS : x ∈ H ⊔ T := Subgroup.mem_sup_left hP.x_mem_H
  obtain ⟨g₁, hg₁S, hg₁H⟩ := c.exists_Hs_not_H hT16
  have hg₁P : g₁ ∉ Hzero H f := fun h => hg₁H (hP.H0_le h)
  have hxg₁S : x * g₁ ∈ H ⊔ T := (H ⊔ T).mul_mem hxS hg₁S
  have hxg₁P : x * g₁ ∉ Hzero H f := by
    intro h
    apply hg₁H
    have : g₁ = x⁻¹ * (x * g₁) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem hP.x_mem_H) (hP.H0_le h)
  have hcls := c.Hs_classes h64 hsq hg₁S hg₁H
  have hQ : ∀ g ∈ H ⊔ T, g ∉ Hzero H f → x ∉ Hzero H f ⊔ zpowers g →
      ∃ w : G, w * x * w⁻¹ ∈ Hzero H f ⊔ zpowers g ∧ IsExtremal2 (H ⊔ T) (w * x * w⁻¹) := by
    intro g hgS hgP hxg
    have hgn : ∀ q ∈ Hzero H f, g * q * g⁻¹ ∈ Hzero H f := c.hPT g hgS
    have hcard := card_sup_zpowers_sq (hsq g hgS) hgn hgP
    have hQS : Hzero H f ⊔ zpowers g ≤ H ⊔ T := sup_le hn.le ((zpowers_le).2 hgS)
    have hrel : (Hzero H f ⊔ zpowers g).relIndex (H ⊔ T) = 2 := by
      have hm := relIndex_mul_card (Hzero H f ⊔ zpowers g) (H ⊔ T)
      rw [inf_of_le_left hQS, hcard, c.c2.P_card, h64] at hm
      omega
    exact transfer_index_two h15 hP.out.simple hP.out.nonabelian hS hQS hrel hxS hxg hP.x_sq
  obtain ⟨w₁, hw₁Q, hw₁ext⟩ := hQ g₁ hg₁S hg₁P (by
    intro h
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq (hsq g₁ hg₁S) (c.hPT g₁ hg₁S)).1 h
    · exact hP.x_notin_H0 (h1 ▸ hq)
    · apply hg₁H
      have : g₁ = q⁻¹ * x := by rw [h1]; group
      rw [this]
      exact H.mul_mem (H.inv_mem (hP.H0_le hq)) hP.x_mem_H)
  obtain ⟨w₂, hw₂Q, hw₂ext⟩ := hQ (x * g₁) hxg₁S hxg₁P (by
    intro h
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq (hsq _ hxg₁S) (c.hPT _ hxg₁S)).1 h
    · exact hP.x_notin_H0 (h1 ▸ hq)
    · apply hg₁P
      have e : g₁ = x⁻¹ * q⁻¹ * x := by
        calc g₁ = x⁻¹ * q⁻¹ * (q * (x * g₁)) := by group
          _ = x⁻¹ * q⁻¹ * x := by rw [← h1]
      rw [e]
      have := c.hPT x⁻¹ ((H ⊔ T).inv_mem hxS) q⁻¹ ((Hzero H f).inv_mem hq)
      simpa using this)
  have hy₁S : w₁ * x * w₁⁻¹ ∈ H ⊔ T := (sup_le hn.le ((zpowers_le).2 hg₁S)) hw₁Q
  have hy₂S : w₂ * x * w₂⁻¹ ∈ H ⊔ T := (sup_le hn.le ((zpowers_le).2 hxg₁S)) hw₂Q
  have hfr₁ : IsFreeConj x (Hzero H f) (w₁ * x * w₁⁻¹) := ⟨⟨w₁, rfl⟩, c.hPT _ hy₁S⟩
  have hfr₂ : IsFreeConj x (Hzero H f) (w₂ * x * w₂⁻¹) := ⟨⟨w₂, rfl⟩, c.hPT _ hy₂S⟩
  have hy₁P := hfr₁.notin c.c2
  have hy₂P := hfr₂.notin c.c2
  obtain ⟨q₁, hq₁, hy₁⟩ : ∃ q ∈ Hzero H f, w₁ * x * w₁⁻¹ = q * g₁ := by
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq (hsq g₁ hg₁S) (c.hPT g₁ hg₁S)).1 hw₁Q
    · exact absurd (h1 ▸ hq) hy₁P
    · exact ⟨q, hq, h1⟩
  obtain ⟨q₂, hq₂, hy₂⟩ : ∃ q ∈ Hzero H f, w₂ * x * w₂⁻¹ = q * (x * g₁) := by
    obtain ⟨q, hq, h1 | h1⟩ := (mem_sup_zpowers_sq (hsq _ hxg₁S) (c.hPT _ hxg₁S)).1 hw₂Q
    · exact absurd (h1 ▸ hq) hy₂P
    · exact ⟨q, hq, h1⟩
  have hy₁H : w₁ * x * w₁⁻¹ ∉ H := by
    intro h
    apply hg₁H
    have : g₁ = q₁⁻¹ * (w₁ * x * w₁⁻¹) := by rw [hy₁]; group
    rw [this]
    exact H.mul_mem (H.inv_mem (hP.H0_le hq₁)) h
  refine ⟨w₁ * x * w₁⁻¹, hfr₁, hy₁S, hy₁H, ?_, ?_⟩
  · intro s hs
    obtain ⟨p, hp, h | h | h | h⟩ := hcls s hs
    · exact ⟨p, hp, Or.inl h⟩
    · exact ⟨p, hp, Or.inr (Or.inl h)⟩
    · refine ⟨p * q₁⁻¹, (Hzero H f).mul_mem hp ((Hzero H f).inv_mem hq₁),
        Or.inr (Or.inr (Or.inl ?_))⟩
      rw [h, hy₁]; group
    · have hxq : x * q₁⁻¹ * x⁻¹ ∈ Hzero H f :=
        hP.H0_norm_H x hP.x_mem_H _ ((Hzero H f).inv_mem hq₁)
      refine ⟨p * (x * q₁⁻¹ * x⁻¹), (Hzero H f).mul_mem hp hxq, Or.inr (Or.inr (Or.inr ?_))⟩
      rw [h, hy₁]; group
  · intro s hs hsP
    obtain ⟨p, hp, h | h | h | h⟩ := hcls s hs
    · exact absurd (h ▸ hp) hsP
    · exact ⟨x, c.isFree_x, p, hp, h⟩
    · refine ⟨w₁ * x * w₁⁻¹, hfr₁, p * q₁⁻¹, (Hzero H f).mul_mem hp ((Hzero H f).inv_mem hq₁), ?_⟩
      rw [hy₁, h]; group
    · refine ⟨w₂ * x * w₂⁻¹, hfr₂, p * q₂⁻¹, (Hzero H f).mul_mem hp ((Hzero H f).inv_mem hq₂), ?_⟩
      rw [hy₂, h]; group

end Ctx2S


namespace Ctx2S

variable {x : G} {T V H : Subgroup G} {f : G} {S : Subgroup G} (c : Ctx2S G x T V H f S)
include c

theorem cent_eq_P [Finite G]
    (hfr : ∀ s ∈ H ⊔ T, s ∉ Hzero H f →
      ∃ y' : G, IsFreeConj x (Hzero H f) y' ∧ ∃ p ∈ Hzero H f, s = p * y') :
    ∀ s ∈ H ⊔ T, (∀ q ∈ Hzero H f, s * q * s⁻¹ = q) → s ∈ Hzero H f := by
  intro s hs hcent
  by_contra hsP
  obtain ⟨y', hy', p, hp, rfl⟩ := hfr s hs hsP
  have hy'c : ∀ q ∈ Hzero H f, y' * q * y'⁻¹ = q := by
    intro q hq
    have h1 := hcent q hq
    have h2 : p * y' * q * (p * y')⁻¹ = p * (y' * q * y'⁻¹) * p⁻¹ := by group
    rw [h2] at h1
    have hmem : y' * q * y'⁻¹ ∈ Hzero H f := hy'.2 q hq
    have h3 := c.c2.P_comm p hp _ hmem
    calc y' * q * y'⁻¹ = p⁻¹ * (p * (y' * q * y'⁻¹) * p⁻¹) * p := by group
      _ = p⁻¹ * q * p := by rw [h1]
      _ = q := by
        have := c.c2.P_comm p⁻¹ ((Hzero H f).inv_mem hp) q hq
        rw [this]; group
  have hle : Hzero H f ≤ Hzero H f ⊓ centralizer ({y'} : Set G) := by
    intro q hq
    refine ⟨hq, ?_⟩
    show q ∈ centralizer ({y'} : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have := hy'c q hq
    calc y' * q = (y' * q * y'⁻¹) * y' := by group
      _ = q * y' := by rw [this]
  have hcard := hy'.card4 c.c2
  have := Subgroup.card_le_of_le hle
  rw [hcard, c.c2.P_card] at this
  omega

theorem fusion_invol [Finite G] (h10 : IG_10_31)
    (hfr : ∀ s ∈ H ⊔ T, s ∉ Hzero H f →
      ∃ y' : G, IsFreeConj x (Hzero H f) y' ∧ ∃ p ∈ Hzero H f, s = p * y') :
    ∀ s ∈ H ⊔ T, s * s = 1 → s ∉ Hzero H f → ∃ w : G, s = w * x * w⁻¹ := by
  intro s hs hss hsP
  obtain ⟨y', hy', p, hp, rfl⟩ := hfr s hs hsP
  obtain ⟨q, hq, h⟩ := hy'.conj_coset c.c2 h10 p hp hss
  obtain ⟨⟨g, hg⟩, -⟩ := hy'
  exact ⟨q * g, by rw [h, hg]; group⟩

end Ctx2S

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
