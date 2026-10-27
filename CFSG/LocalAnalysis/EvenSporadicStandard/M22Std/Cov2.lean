module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Facts

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Algebra

variable {L : Type*} [Group L]

theorem comm_mul_eq_of_squares {t x y : L} (htt : t * t = 1) (ht1 : t ≠ 1) (hx : x * x = t)
    (hy : y * y = t) (hxy : (x * y) * (x * y) = t)
    (hc : x * y = y * x ∨ x * y = y * x * t) : y * x = x * y * t := by
  rcases hc with h | h
  · exfalso
    have : (x * y) * (x * y) = (x * x) * (y * y) := by
      calc (x * y) * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [h]
        _ = (x * x) * (y * y) := by simp only [mul_assoc]
    rw [this, hx, hy, htt] at hxy
    exact ht1 hxy.symm
  · calc y * x = y * x * t * t := by rw [mul_assoc, htt, mul_one]
      _ = x * y * t := by rw [← h]

theorem false_of_three_squares {t a b c : L} (ht : ∀ z, t * z = z * t) (htt : t * t = 1)
    (ht1 : t ≠ 1) (ha : a * a = t) (hb : b * b = t) (hc : c * c = t)
    (hab : (a * b) * (a * b) = t) (hac : (a * c) * (a * c) = t) (hbc : (b * c) * (b * c) = t)
    (habc : (a * b * c) * (a * b * c) = t)
    (hab' : a * b = b * a ∨ a * b = b * a * t) (hac' : a * c = c * a ∨ a * c = c * a * t) :
    False := by
  have hba : b * a = a * b * t := comm_mul_eq_of_squares htt ht1 ha hb hab hab'
  have hca : c * a = a * c * t := comm_mul_eq_of_squares htt ht1 ha hc hac hac'
  have h1 : a * b * a = b := by
    calc a * b * a = a * (b * a) := by rw [mul_assoc]
      _ = a * (a * b * t) := by rw [hba]
      _ = (a * a) * b * t := by simp only [mul_assoc]
      _ = t * b * t := by rw [ha]
      _ = b * t * t := by rw [ht b]
      _ = b := by rw [mul_assoc, htt, mul_one]
  have h2 : a * b * c * (a * b * c) = (b * c) * (b * c) * t := by
    calc a * b * c * (a * b * c) = a * b * (c * a) * b * c := by simp only [mul_assoc]
      _ = a * b * (a * c * t) * b * c := by rw [hca]
      _ = (a * b * a) * c * t * b * c := by simp only [mul_assoc]
      _ = b * c * t * b * c := by rw [h1]
      _ = b * c * (t * b) * c := by simp only [mul_assoc]
      _ = b * c * (b * t) * c := by rw [ht b]
      _ = b * c * b * (t * c) := by simp only [mul_assoc]
      _ = b * c * b * (c * t) := by rw [ht c]
      _ = (b * c) * (b * c) * t := by simp only [mul_assoc]
  rw [habc, hbc, htt] at h2
  exact ht1 h2

end Algebra

structure IsM22Cover (L : Type) [Group L] (t : L) : Prop where
  orderOf_t : orderOf t = 2
  center_eq : center L = zpowers t
  quotient : IsSporadic (L ⧸ center L) .M22

namespace IsM22Cover

variable {L : Type} [Group L] {t : L}

theorem mul_self_t (h : IsM22Cover L t) : t * t = 1 := by
  rw [← sq, ← h.orderOf_t]
  exact pow_orderOf_eq_one t

theorem t_ne_one (h : IsM22Cover L t) : t ≠ 1 := by
  intro h1
  have := h.orderOf_t
  rw [h1, orderOf_one] at this
  exact absurd this (by decide)

theorem t_central (h : IsM22Cover L t) (z : L) : t * z = z * t :=
  (mem_center_iff.1 (h.center_eq ▸ mem_zpowers t) z).symm

theorem eq_one_or_eq_t_of_mk_eq_one (h : IsM22Cover L t) {x : L}
    (hx : (x : L ⧸ center L) = 1) : x = 1 ∨ x = t := by
  have hxc : x ∈ center L := (QuotientGroup.eq_one_iff x).1 hx
  rw [h.center_eq] at hxc
  exact eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two h.orderOf_t hxc

theorem eq_or_eq_mul_t_of_mk_eq (h : IsM22Cover L t) {x y : L}
    (hxy : (x : L ⧸ center L) = y) : x = y ∨ x = y * t := by
  have h1 : ((y⁻¹ * x : L) : L ⧸ center L) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxy, inv_mul_cancel]
  rcases h.eq_one_or_eq_t_of_mk_eq_one h1 with h2 | h2
  · left
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  · right
    rw [← h2]
    group

end IsM22Cover

section Triple

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.M22

theorem m22_triple :
    ∃ a b c : Carrier .M22, a * b = b * a ∧ a * c = c * a ∧ b * c = c * b ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf c = 2 ∧ orderOf (a * b) = 2 ∧
      orderOf (a * c) = 2 ∧ orderOf (b * c) = 2 ∧ orderOf (a * b * c) = 2 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hmem : ∀ w : List ℤ, evalCodes gensM w ∈ NativeSporadic.M22 := fun w =>
    evalCodes_mem _ (by
      intro g hg
      simp only [gensM, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact m22a.2
      · exact m22b.2) w
  have h1 : e1 ∈ NativeSporadic.M22 := hmem wordE1
  have h2 : e2 ∈ NativeSporadic.M22 := hmem wordE2
  have h3 : e3 ∈ NativeSporadic.M22 := hmem wordE3
  have h : e8Check 22 (toTable e1) (toTable e2) (toTable e3) = true :=
    Certificates.certificate24274.2.2.1
  simp only [e8Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hac⟩, hbc⟩, ha2⟩, hb2⟩, hc2⟩, hab2⟩, hac2⟩, hbc2⟩, habc2⟩ := h
  have rA := rep_toTable hn e1
  have rB := rep_toTable hn e2
  have rC := rep_toTable hn e3
  have order2 : ∀ {T : Table} {g : Equiv.Perm (Fin 22)}, Rep 22 T g → ordTest 22 2 T = true →
      orderOf g = 2 := fun hT hT2 => (ordTest_iff perm_faithful hT (by norm_num)).1 hT2
  refine ⟨mkM22 e1 h1, mkM22 e2 h2, mkM22 e3 h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact toPerm_injective (by
      rw [map_mul, map_mul, toPerm_mkM22, toPerm_mkM22]
      exact (commT_iff rA rB).1 hab)
  · exact toPerm_injective (by
      rw [map_mul, map_mul, toPerm_mkM22, toPerm_mkM22]
      exact (commT_iff rA rC).1 hac)
  · exact toPerm_injective (by
      rw [map_mul, map_mul, toPerm_mkM22, toPerm_mkM22]
      exact (commT_iff rB rC).1 hbc)
  · rw [← orderOf_toPerm, toPerm_mkM22]
    exact order2 rA ha2
  · rw [← orderOf_toPerm, toPerm_mkM22]
    exact order2 rB hb2
  · rw [← orderOf_toPerm, toPerm_mkM22]
    exact order2 rC hc2
  · rw [← orderOf_toPerm, map_mul, toPerm_mkM22, toPerm_mkM22]
    exact order2 (Rep.compT rA rB) hab2
  · rw [← orderOf_toPerm, map_mul, toPerm_mkM22, toPerm_mkM22]
    exact order2 (Rep.compT rA rC) hac2
  · rw [← orderOf_toPerm, map_mul, toPerm_mkM22, toPerm_mkM22]
    exact order2 (Rep.compT rB rC) hbc2
  · rw [← orderOf_toPerm, map_mul, map_mul, toPerm_mkM22, toPerm_mkM22, toPerm_mkM22]
    exact order2 (Rep.compT (Rep.compT rA rB) rC) habc2

end Triple

namespace IsM22Cover

variable {L : Type} [Group L] {t : L}

theorem involution_conj
    (h : IsM22Cover L t) {u v : L ⧸ center L} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    ∃ c : L ⧸ center L, v = c * u * c⁻¹ := by
  obtain ⟨e⟩ := h.quotient
  have hu' : orderOf (e u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
  have hv' : orderOf (e v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
  obtain ⟨c₁, hc₁⟩ := m22_involution_conj _ hu'
  obtain ⟨c₂, hc₂⟩ := m22_involution_conj _ hv'
  refine ⟨e.symm (c₂ * c₁⁻¹), e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc₂, hc₁]
  group

theorem sq_eq_of_exists_sq
    (h : IsM22Cover L t) (hg : ∃ g : L, g * g = t) :
    ∀ y : L, orderOf (y : L ⧸ center L) = 2 → y * y = t := by
  obtain ⟨g, hg⟩ := hg
  have ht1 : ((t : L) : L ⧸ center L) = 1 :=
    (QuotientGroup.eq_one_iff t).2 (h.center_eq ▸ mem_zpowers t)
  have hgbar : orderOf (g : L ⧸ center L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← QuotientGroup.mk_mul, hg]
      exact ht1
    · intro h1
      rcases h.eq_one_or_eq_t_of_mk_eq_one h1 with h2 | h2
      · rw [h2, mul_one] at hg
        exact h.t_ne_one hg.symm
      · rw [h2, h.mul_self_t] at hg
        exact h.t_ne_one hg.symm
  intro y hy
  obtain ⟨cb, hc⟩ := h.involution_conj hgbar hy
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have hyc : (y : L ⧸ center L) = ((c * g * c⁻¹ : L) : L ⧸ center L) := by
    rw [hc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hA : c * g * c⁻¹ * (c * g * c⁻¹) = t := by
    calc c * g * c⁻¹ * (c * g * c⁻¹) = c * (g * g) * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [hg]
      _ = t := by rw [← h.t_central c, mul_inv_cancel_right]
  rcases h.eq_or_eq_mul_t_of_mk_eq hyc with h1 | h1
  · rw [h1]
    exact hA
  · rw [h1]
    calc c * g * c⁻¹ * t * (c * g * c⁻¹ * t)
        = c * g * c⁻¹ * (t * (c * g * c⁻¹)) * t := by simp only [mul_assoc]
      _ = c * g * c⁻¹ * ((c * g * c⁻¹) * t) * t := by rw [h.t_central (c * g * c⁻¹)]
      _ = (c * g * c⁻¹ * (c * g * c⁻¹)) * (t * t) := by simp only [mul_assoc]
      _ = t := by rw [hA, h.mul_self_t, mul_one]

theorem not_sq_t
    (h : IsM22Cover L t) : ∀ g : L, g * g ≠ t := by
  intro g hg
  have hsq := h.sq_eq_of_exists_sq ⟨g, hg⟩
  obtain ⟨a', b', c', hab, hac, hbc, ha, hb, hc, hab2, hac2, hbc2, habc2⟩ := m22_triple
  obtain ⟨e⟩ := h.quotient
  obtain ⟨a, haA⟩ := QuotientGroup.mk_surjective (e.symm a')
  obtain ⟨b, hbA⟩ := QuotientGroup.mk_surjective (e.symm b')
  obtain ⟨c, hcA⟩ := QuotientGroup.mk_surjective (e.symm c')
  have hord : ∀ x : Carrier .M22, orderOf x = 2 → ∀ l : L,
      (l : L ⧸ center L) = e.symm x → orderOf (l : L ⧸ center L) = 2 := by
    intro x hx l hl
    rw [hl, MulEquiv.orderOf_eq]
    exact hx
  have hmul : ∀ (x y : Carrier .M22) (l m : L), (l : L ⧸ center L) = e.symm x →
      (m : L ⧸ center L) = e.symm y → ((l * m : L) : L ⧸ center L) = e.symm (x * y) := by
    intro x y l m hl hm
    rw [QuotientGroup.mk_mul, hl, hm, map_mul]
  have hab3 := hmul a' b' a b haA hbA
  have hac3 := hmul a' c' a c haA hcA
  have hbc3 := hmul b' c' b c hbA hcA
  have habc3 := hmul (a' * b') c' (a * b) c hab3 hcA
  refine false_of_three_squares h.t_central h.mul_self_t h.t_ne_one (hsq a (hord _ ha a haA))
    (hsq b (hord _ hb b hbA)) (hsq c (hord _ hc c hcA)) (hsq (a * b) (hord _ hab2 _ hab3))
    (hsq (a * c) (hord _ hac2 _ hac3)) (hsq (b * c) (hord _ hbc2 _ hbc3))
    (hsq (a * b * c) (hord _ habc2 _ habc3)) ?_ ?_
  · refine h.eq_or_eq_mul_t_of_mk_eq ?_
    rw [hab3, QuotientGroup.mk_mul, hbA, haA, ← map_mul, hab, map_mul]
  · refine h.eq_or_eq_mul_t_of_mk_eq ?_
    rw [hac3, QuotientGroup.mk_mul, hcA, haA, ← map_mul, hac, map_mul]

theorem mul_self_of_lift
    (h : IsM22Cover L t) {y : L}
    (hy : orderOf (y : L ⧸ center L) = 2) : y * y = 1 := by
  have h1 : ((y * y : L) : L ⧸ center L) = 1 := by
    rw [QuotientGroup.mk_mul, ← sq]
    have := pow_orderOf_eq_one (y : L ⧸ center L)
    rwa [hy] at this
  rcases h.eq_one_or_eq_t_of_mk_eq_one h1 with h2 | h2
  · exact h2
  · exact absurd h2 (h.not_sq_t y)

end IsM22Cover

end CFSG.EvenSporadicStandard.M22Std
