module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup

variable {G A B : Type} [Group G] [Group A] [Group B]

theorem index_mul_of_commute [Finite G] [Finite A] [Finite B] (ι₁ : A →* G) (ι₂ : B →* G)
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (hc : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Nat.card (center A) ∧
      (ι₁.range ⊔ ι₂.range).index * (Nat.card A * Nat.card B) = Nat.card G * k := by
  set μ := ι₁.noncommCoprod ι₂ fun a b => (show Commute (ι₁ a) (ι₂ b) from hc a b) with hμ
  have hrange : μ.range = ι₁.range ⊔ ι₂.range := MonoidHom.noncommCoprod_range _ _ _
  have hcard : Nat.card A * Nat.card B = Nat.card μ.range * Nat.card μ.ker := by
    rw [← Nat.card_prod, card_eq_card_quotient_mul_card_subgroup μ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv]
  have hcen : ∀ x ∈ μ.ker, x.1 ∈ center A := by
    intro x hx
    rw [MonoidHom.mem_ker, hμ, MonoidHom.noncommCoprod_apply] at hx
    have h2 : ι₂ x.2 = (ι₁ x.1)⁻¹ := eq_inv_of_mul_eq_one_right hx
    rw [mem_center_iff]
    intro a
    apply hι₁
    rw [map_mul, map_mul]
    have hca : ι₁ a * (ι₁ x.1)⁻¹ = (ι₁ x.1)⁻¹ * ι₁ a := by rw [← h2, hc]
    calc ι₁ a * ι₁ x.1 = ι₁ x.1 * ((ι₁ x.1)⁻¹ * ι₁ a) * ι₁ x.1 := by group
      _ = ι₁ x.1 * (ι₁ a * (ι₁ x.1)⁻¹) * ι₁ x.1 := by rw [hca]
      _ = ι₁ x.1 * ι₁ a := by group
  have hinj : Function.Injective fun x : μ.ker => (⟨(x : A × B).1, hcen x x.2⟩ : center A) := by
    rintro ⟨⟨a, b⟩, hx⟩ ⟨⟨a', b'⟩, hx'⟩ h
    simp only [Subtype.mk.injEq] at h
    subst h
    rw [MonoidHom.mem_ker, hμ, MonoidHom.noncommCoprod_apply] at hx hx'
    have hb : b = b' := hι₂ ((eq_inv_of_mul_eq_one_right hx).trans
      (eq_inv_of_mul_eq_one_right hx').symm)
    subst hb
    rfl
  refine ⟨Nat.card μ.ker, Nat.card_pos, Nat.card_le_card_of_injective _ hinj, ?_⟩
  rw [hcard, ← mul_assoc, ← hrange, index_mul_card]

theorem card_center_SL2_le {K : Type} [Field K] :
    Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ 2 := by
  have : NeZero (max (Fintype.card (Fin 2)) 1) := ⟨by simp⟩
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity).toEquiv]
  exact (card_rootsOfUnity K _).trans (by simp)

theorem le_normalizer_of_commute (ι₁ : A →* G) (ι₂ : B →* G)
    (hc : ∀ a b, ι₁ a * ι₂ b = ι₂ b * ι₁ a) :
    ι₁.range ⊔ ι₂.range ≤ normalizer (ι₁.range : Set G) := by
  refine sup_le le_normalizer ?_
  rintro _ ⟨b, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [← hc, mul_inv_cancel_right]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hx : x = (ι₂ b)⁻¹ * ι₁ a * ι₂ b := by rw [ha]; group
    rw [hx, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

theorem no_two_p_of_odd_centralizer [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ∀ x : G, orderOf x = p → Odd (Nat.card (centralizer ({x} : Set G)))) (w : G) :
    orderOf w ≠ 2 * p := by
  intro hw
  have hx : orderOf (w ^ 2) = p := by
    rw [orderOf_pow_of_dvd (by norm_num) (hw ▸ dvd_mul_right 2 p), hw]
    omega
  have ht : orderOf (w ^ p) = 2 := by
    rw [orderOf_pow_of_dvd hp.ne_zero (hw ▸ dvd_mul_left p 2), hw, Nat.mul_div_cancel _ hp.pos]
  have hmem : w ^ p ∈ centralizer ({w ^ 2} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← pow_add, ← pow_add, add_comm]
  have h2 := Subgroup.orderOf_dvd_natCard _ hmem
  rw [ht] at h2
  exact (Nat.not_even_iff_odd.2 (h _ hx)) (even_iff_two_dvd.2 h2)

end CFSG.OddStandard.GH71.S55
