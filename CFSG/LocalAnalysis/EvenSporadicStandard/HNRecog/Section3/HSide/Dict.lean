module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private lemma orderOf_eq_of_isConj {a x : G} (h : IsConj a x) : orderOf x = orderOf a := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa using MulEquiv.orderOf_eq (MulAut.conj c) a

private lemma isConj_coe_of_isConj {b : G} {x y : ↥(Gx b)} (h : IsConj x y) :
    IsConj (x : G) (y : G) :=
  MonoidHom.map_isConj (Gx b).subtype h

private lemma isConj_mul_of_isConj {b : G} {x y : ↥(Gx b)} (h : IsConj x y) :
    IsConj (b * (x : G)) (b * (y : G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hcG : (c : G) * (x : G) * (c : G)⁻¹ = (y : G) := by
    have := congrArg (fun z : ↥(Gx b) => (z : G)) hc
    simpa using this
  have hcb : (c : G) * b = b * (c : G) := (mem_Gx.1 c.2).symm
  refine isConj_iff.2 ⟨(c : G), ?_⟩
  calc (c : G) * (b * (x : G)) * (c : G)⁻¹
      = b * ((c : G) * (x : G) * (c : G)⁻¹) := by
        rw [← mul_assoc (c : G) b (x : G), hcb]
        group
    _ = b * (y : G) := by rw [hcG]

private lemma eq_of_isConj_of_mem_center {H : Type*} [Group H] {x y : H}
    (hx : x ∈ Subgroup.center H) (h : IsConj x y) : y = x := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hcx : c * x * c⁻¹ = x := by
    rw [Subgroup.mem_center_iff.1 hx c, mul_assoc, mul_inv_cancel, mul_one]
  rw [← hc]
  exact hcx

structure HLab (b z : G) (z₀ b₀ u₀ : ↥(Gx b)) : Prop where
  facts : TwoHSFacts ↥(Gx b) (GxSelf b) z₀ b₀ u₀
  not_conj : ¬ IsConj b z
  z₀_B : IsConj z (z₀ : G)
  bz₀_A : IsConj b (b * (z₀ : G))
  b₀_A : IsConj b (b₀ : G)
  bb₀_A : IsConj b (b * (b₀ : G))
  u₀_B : IsConj z (u₀ : G)
  bu₀_B : IsConj z (b * (u₀ : G))

namespace HLab

variable {b z : G} {z₀ b₀ u₀ : ↥(Gx b)}

private lemma orderOf_b (L : HLab b z z₀ b₀ u₀) : orderOf b = 2 := by
  have hb₀ : orderOf ((GxSelf b : ↥(Gx b)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, L.facts.orderOf_a]
  exact hb₀

private lemma orderOf_z (L : HLab b z z₀ b₀ u₀) : orderOf z = 2 := by
  have hz₀ : orderOf ((z₀ : ↥(Gx b)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, L.facts.orderOf_z]
  exact (orderOf_eq_of_isConj L.z₀_B).symm.trans hz₀

private lemma b_sq (L : HLab b z z₀ b₀ u₀) : b * b = 1 := by
  have h := pow_orderOf_eq_one b
  rw [orderOf_b L] at h
  simpa [pow_two] using h

private lemma b_ne_one (L : HLab b z z₀ b₀ u₀) : b ≠ 1 := by
  intro h
  have h2 := orderOf_b L
  rw [h, orderOf_one] at h2
  exact (by decide : (1 : ℕ) ≠ 2) h2

private lemma z_ne_one (L : HLab b z z₀ b₀ u₀) : z ≠ 1 := by
  intro h
  have h2 := orderOf_z L
  rw [h, orderOf_one] at h2
  exact (by decide : (1 : ℕ) ≠ 2) h2

private lemma self_mem_center (L : HLab b z z₀ b₀ u₀) :
    GxSelf b ∈ Subgroup.center ↥(Gx b) := by
  rw [L.facts.center_eq]
  exact Subgroup.mem_zpowers (GxSelf b)

private lemma involution_cases (L : HLab b z z₀ b₀ u₀) {t : ↥(Gx b)} (ht : orderOf t = 2) :
    IsConj (GxSelf b) t ∨ IsConj z₀ t ∨ IsConj (GxSelf b * z₀) t ∨ IsConj b₀ t ∨
      IsConj u₀ t := by
  obtain ⟨i, hi⟩ := L.facts.involution_cover t ht
  fin_cases i
  · left; simpa using hi
  · right; left; simpa using hi
  · right; right; left; simpa using hi
  · right; right; right; left; simpa using hi
  · right; right; right; right; simpa using hi

theorem isA_iff (L : HLab b z z₀ b₀ u₀) (t : ↥(Gx b)) :
    HIsA (GxSelf b) z₀ b₀ t ↔ IsConj b (t : G) := by
  constructor
  · intro h
    have h' : IsConj (GxSelf b) t ∨ IsConj (GxSelf b * z₀) t ∨ IsConj b₀ t := h
    rcases h' with h' | h' | h'
    · exact isConj_coe_of_isConj h'
    · exact L.bz₀_A.trans (isConj_coe_of_isConj h')
    · exact L.b₀_A.trans (isConj_coe_of_isConj h')
  · intro hb
    have ht2 : orderOf t = 2 := by
      rw [← Subgroup.orderOf_coe t, orderOf_eq_of_isConj hb, orderOf_b L]
    rcases involution_cases L ht2 with h | h | h | h | h
    · exact Or.inl h
    · exfalso
      exact L.not_conj (hb.trans (L.z₀_B.trans (isConj_coe_of_isConj h)).symm)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exfalso
      exact L.not_conj (hb.trans (L.u₀_B.trans (isConj_coe_of_isConj h)).symm)

theorem isB_iff (L : HLab b z z₀ b₀ u₀) (t : ↥(Gx b)) :
    HIsB z₀ u₀ t ↔ IsConj z (t : G) := by
  constructor
  · intro h
    have h' : IsConj z₀ t ∨ IsConj u₀ t := h
    rcases h' with h' | h'
    · exact L.z₀_B.trans (isConj_coe_of_isConj h')
    · exact L.u₀_B.trans (isConj_coe_of_isConj h')
  · intro hz
    have ht2 : orderOf t = 2 := by
      rw [← Subgroup.orderOf_coe t, orderOf_eq_of_isConj hz, orderOf_z L]
    rcases involution_cases L ht2 with h | h | h | h | h
    · exfalso
      exact L.not_conj ((isConj_coe_of_isConj h).trans hz.symm)
    · exact Or.inl h
    · exfalso
      exact L.not_conj ((L.bz₀_A.trans (isConj_coe_of_isConj h)).trans hz.symm)
    · exfalso
      exact L.not_conj ((L.b₀_A.trans (isConj_coe_of_isConj h)).trans hz.symm)
    · exact Or.inr h

theorem isConj_z₀_iff (L : HLab b z z₀ b₀ u₀) {t : ↥(Gx b)} (ht : IsConj z (t : G)) :
    IsConj z₀ t ↔ IsConj b (b * (t : G)) := by
  constructor
  · intro h
    exact L.bz₀_A.trans (isConj_mul_of_isConj h)
  · intro h
    rcases (isB_iff L t).2 ht with h' | h'
    · exact h'
    · exfalso
      exact L.not_conj (h.trans (L.bu₀_B.trans (isConj_mul_of_isConj h')).symm)

theorem isConj_b₀_iff (L : HLab b z z₀ b₀ u₀) (c : ↥(Gx b)) :
    IsConj b₀ c ↔ IsConj b (c : G) ∧ IsConj b (b * (c : G)) := by
  constructor
  · intro h
    exact ⟨L.b₀_A.trans (isConj_coe_of_isConj h),
      L.bb₀_A.trans (isConj_mul_of_isConj h)⟩
  · rintro ⟨h1, h2⟩
    rcases (isA_iff L c).2 h1 with h | h | h
    · exfalso
      have hc : c = GxSelf b := eq_of_isConj_of_mem_center (self_mem_center L) h
      have hcG : (c : G) = b := congrArg (fun x : ↥(Gx b) => (x : G)) hc
      have hbc : b * (c : G) = 1 := by rw [hcG, b_sq L]
      exact b_ne_one L (isConj_one_left.1 (hbc ▸ h2))
    · exfalso
      have hz : IsConj z (b * (c : G)) := by
        have h' : IsConj (b * (b * (z₀ : G))) (b * (c : G)) := isConj_mul_of_isConj h
        rw [show b * (b * (z₀ : G)) = z₀ by rw [← mul_assoc, b_sq L, one_mul]] at h'
        exact L.z₀_B.trans h'
      exact L.not_conj (h2.trans hz.symm)
    · exact h

theorem isConj_bz₀_iff (L : HLab b z z₀ b₀ u₀) (c : ↥(Gx b)) :
    IsConj (GxSelf b * z₀) c ↔ IsConj b (c : G) ∧ IsConj z (b * (c : G)) := by
  constructor
  · intro h
    refine ⟨L.bz₀_A.trans (isConj_coe_of_isConj h), ?_⟩
    have h' : IsConj (b * (b * (z₀ : G))) (b * (c : G)) := isConj_mul_of_isConj h
    rw [show b * (b * (z₀ : G)) = z₀ by rw [← mul_assoc, b_sq L, one_mul]] at h'
    exact L.z₀_B.trans h'
  · rintro ⟨h1, h2⟩
    rcases (isA_iff L c).2 h1 with h | h | h
    · exfalso
      have hc : c = GxSelf b := eq_of_isConj_of_mem_center (self_mem_center L) h
      have hcG : (c : G) = b := congrArg (fun x : ↥(Gx b) => (x : G)) hc
      have hbc : b * (c : G) = 1 := by rw [hcG, b_sq L]
      exact z_ne_one L (isConj_one_left.1 (hbc ▸ h2))
    · exact h
    · exfalso
      exact L.not_conj ((L.bb₀_A.trans (isConj_mul_of_isConj h)).trans h2.symm)

end HLab

theorem mem_Gx_of_isConj_mul {x y b c : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hb : IsConj x b)
    (hc : IsConj x c) (hbc : IsConj x (b * c) ∨ IsConj y (b * c)) : c ∈ Gx b := by
  have hb2 : b ^ 2 = 1 := by
    have h := hb.pow 2
    rw [hx] at h
    exact isConj_one_right.1 h
  have hc2 : c ^ 2 = 1 := by
    have h := hc.pow 2
    rw [hx] at h
    exact isConj_one_right.1 h
  have hbc2 : (b * c) ^ 2 = 1 := by
    rcases hbc with h | h
    · have h' := h.pow 2
      rw [hx] at h'
      exact isConj_one_right.1 h'
    · have h' := h.pow 2
      rw [hy] at h'
      exact isConj_one_right.1 h'
  exact mem_Gx.2 (comm_of_sq_mul hb2 hc2 hbc2)

end CFSG.EvenSporadicStandard.HNRecog.Section3
