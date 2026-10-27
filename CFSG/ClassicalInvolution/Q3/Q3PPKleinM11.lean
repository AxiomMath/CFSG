module

public import CFSG.ClassicalInvolution.Q3.Q3PPKleinAt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups

section Model

theorem sl23_sq_unique :
    ∀ s s' : SL(2, ZMod 3), s * s = 1 → s' * s' = 1 → s ≠ 1 → s' ≠ 1 → s = s' := by
  decide +kernel

theorem m11_member_unique_inv {R : Subgroup ↥NativeSporadic.M11} {z : ↥NativeSporadic.M11}
    (h : IsClassicalMember3 R z) :
    ∀ a ∈ R, ∀ b ∈ R, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b := by
  intro a ha b hb ha2 hb2 ha1 hb1
  have hcard : Nat.card R = 24 := h.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  obtain ⟨e⟩ := h.nonempty_equiv
  have hq : Nat.card (R ⧸ classicalInvolutionOddCore R) = 24 := by
    rw [Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore R)
  have hO1 : Nat.card (classicalInvolutionOddCore R) = 1 := by
    rw [hq, hcard] at hmul
    omega
  have hObot : classicalInvolutionOddCore R = ⊥ := Subgroup.eq_bot_of_card_eq _ hO1
  have hπ : Function.Injective (QuotientGroup.mk' (classicalInvolutionOddCore R)) := by
    intro x y hxy
    have h1 : x⁻¹ * y ∈ classicalInvolutionOddCore R := QuotientGroup.eq.mp hxy
    rw [hObot, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  set a' : R := ⟨a, ha⟩ with ha'
  set b' : R := ⟨b, hb⟩ with hb'
  have ha2' : a' * a' = 1 := Subtype.ext ha2
  have hb2' : b' * b' = 1 := Subtype.ext hb2
  have ha1' : a' ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
  have hb1' : b' ≠ 1 := fun h1 => hb1 (congrArg Subtype.val h1)
  have hne : ∀ x : R, x ≠ 1 → e (QuotientGroup.mk' (classicalInvolutionOddCore R) x) ≠ 1 := by
    intro x hx h1
    apply hx
    apply hπ
    apply e.injective
    rw [h1, map_one, map_one]
  have hsq : ∀ x : R, x * x = 1 →
      e (QuotientGroup.mk' (classicalInvolutionOddCore R) x) *
        e (QuotientGroup.mk' (classicalInvolutionOddCore R) x) = 1 := by
    intro x hx
    rw [← map_mul, ← map_mul, hx, map_one, map_one]
  have h1 := sl23_sq_unique _ _ (hsq a' ha2') (hsq b' hb2') (hne a' ha1') (hne b' hb1')
  exact congrArg Subtype.val (hπ (e.injective h1))

end Model

theorem klein_of_conj_involutions {G : Type*} [Group G] {z d : G} (hd2 : d * d = 1)
    (hdz : d * z = z * d) (hdne : d ≠ z) (hd1 : d ≠ 1)
    (hconj : ∀ w : G, w * w = 1 → w ≠ 1 → ∃ c : G, c * z * c⁻¹ = w) :
    ∀ r : G, r * r = 1 → r ≠ 1 →
      ∃ r' g' g'' : G, r' = g' * r * g'⁻¹ ∧ r * r' = g'' * r * g''⁻¹ ∧ r' * r = r * r' ∧
        r' ≠ r := by
  intro r hr2 hr1
  obtain ⟨c, hc⟩ := hconj r hr2 hr1
  have hr'2 : (c * d * c⁻¹) * (c * d * c⁻¹) = 1 := by
    calc c * d * c⁻¹ * (c * d * c⁻¹) = c * (d * d) * c⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  have hr'1 : c * d * c⁻¹ ≠ 1 := by
    intro h
    apply hd1
    have : d = c⁻¹ * (c * d * c⁻¹) * c := by group
    rw [this, h]
    group
  have hr'ne : c * d * c⁻¹ ≠ r := by
    rw [← hc]
    intro h
    exact hdne (mul_left_cancel (mul_right_cancel h))
  have hcomm : c * d * c⁻¹ * r = r * (c * d * c⁻¹) := by
    rw [← hc]
    calc c * d * c⁻¹ * (c * z * c⁻¹) = c * (d * z) * c⁻¹ := by group
      _ = c * (z * d) * c⁻¹ := by rw [hdz]
      _ = c * z * c⁻¹ * (c * d * c⁻¹) := by group
  have hrr2 : (r * (c * d * c⁻¹)) * (r * (c * d * c⁻¹)) = 1 := by
    calc r * (c * d * c⁻¹) * (r * (c * d * c⁻¹))
        = r * (c * d * c⁻¹ * r) * (c * d * c⁻¹) := by group
      _ = r * (r * (c * d * c⁻¹)) * (c * d * c⁻¹) := by rw [hcomm]
      _ = (r * r) * ((c * d * c⁻¹) * (c * d * c⁻¹)) := by group
      _ = 1 := by rw [hr2, hr'2, one_mul]
  have hrr1 : r * (c * d * c⁻¹) ≠ 1 := by
    intro h
    apply hr'ne
    have h' : c * d * c⁻¹ = r⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h']
    exact inv_eq_of_mul_eq_one_right hr2
  obtain ⟨u, hu⟩ := hconj _ hr'2 hr'1
  obtain ⟨v, hv⟩ := hconj _ hrr2 hrr1
  refine ⟨c * d * c⁻¹, u * c⁻¹, v * c⁻¹, ?_, ?_, hcomm, hr'ne⟩
  · rw [← hu, ← hc]
    group
  · rw [← hv, ← hc]
    group

theorem kleinData_m11 : KleinData CompData.m11 := by
  have hM := m11Facts
  refine ⟨center_m11_eq_bot hM, ?_, ?_, ?_⟩
  · intro R hR a ha b hb ha2 hb2 ha1 hb1
    obtain ⟨z, hz⟩ := hR
    exact m11_member_unique_inv hz a ha b hb ha2 hb2 ha1 hb1
  · intro R hR g
    obtain ⟨z, hz⟩ := hR
    exact ⟨g * z * g⁻¹, hz.map_mulEquiv (MulAut.conj g)⟩
  · intro R _ r _ hr2 hr1
    have hd2 : (⟨m11SdY, m11SdY_mem⟩ : ↥NativeSporadic.M11) * ⟨m11SdY, m11SdY_mem⟩ = 1 :=
      Subtype.ext (by
        show m11SdY * m11SdY = 1
        rw [← pow_two]
        exact m11SdY_sq)
    have hdz : (⟨m11SdY, m11SdY_mem⟩ : ↥NativeSporadic.M11) * m11SdZ =
        m11SdZ * ⟨m11SdY, m11SdY_mem⟩ :=
      Subtype.ext (by
        show m11SdY * m11SdX ^ 4 = m11SdX ^ 4 * m11SdY
        decide +kernel)
    have hdne : (⟨m11SdY, m11SdY_mem⟩ : ↥NativeSporadic.M11) ≠ m11SdZ := fun h => by
      have h' : m11SdY = m11SdX ^ 4 := congrArg Subtype.val h
      revert h'
      decide +kernel
    have hd1 : (⟨m11SdY, m11SdY_mem⟩ : ↥NativeSporadic.M11) ≠ 1 := fun h => by
      have h' : m11SdY = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
    exact klein_of_conj_involutions hd2 hdz hdne hd1
      (fun w hw2 hw1 => isConj_iff.mp (isConj_m11SdZ_of_orderOf_eq_two
        (orderOf_eq_prime (by rwa [pow_two]) hw1))) r hr2 hr1

section Edge


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

theorem EdgeData.kleinAt_of_m11 (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) (hk : D.kind i = CompData.m11) :
    KleinAt K K₁ z₂ :=
  h.kleinAt_of_kleinData hR D hi (by rw [hk]; exact kleinData_m11)

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
