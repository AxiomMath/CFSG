module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

section UT3F4

theorem two_eq_zero_F4 : (2 : F4) = 0 := CharP.cast_eq_zero F4 2

theorem add_self_F4 (x : F4) : x + x = 0 := by
  rw [← two_mul, two_eq_zero_F4, zero_mul]

theorem card_F4 : Nat.card F4 = 4 := by
  have := GaloisField.card 2 2 (by norm_num)
  simpa using this

theorem ut3_sq (x : UT3 F4) : x * x = ⟨0, 0, x.a * x.b⟩ := by
  rw [UT3.mul_def]
  ext
  · exact add_self_F4 _
  · exact add_self_F4 _
  · show x.c + x.c + x.a * x.b = x.a * x.b
    rw [add_self_F4, zero_add]

@[expose] def ZUT : Subgroup (UT3 F4) where
  carrier := {x | x.a = 0 ∧ x.b = 0}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show x.a + y.a = 0
      rw [hx1, hy1, add_zero]
    · show x.b + y.b = 0
      rw [hx2, hy2, add_zero]
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show -x.a = 0
      rw [hx1, neg_zero]
    · show -x.b = 0
      rw [hx2, neg_zero]

@[expose] def E1UT : Subgroup (UT3 F4) where
  carrier := {x | x.b = 0}
  mul_mem' := by
    rintro x y hx hy
    show x.b + y.b = 0
    rw [show x.b = 0 from hx, show y.b = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    rintro x hx
    show -x.b = 0
    rw [show x.b = 0 from hx, neg_zero]

@[expose] def E2UT : Subgroup (UT3 F4) where
  carrier := {x | x.a = 0}
  mul_mem' := by
    rintro x y hx hy
    show x.a + y.a = 0
    rw [show x.a = 0 from hx, show y.a = 0 from hy, add_zero]
  one_mem' := rfl
  inv_mem' := by
    rintro x hx
    show -x.a = 0
    rw [show x.a = 0 from hx, neg_zero]

theorem mem_ZUT {x : UT3 F4} : x ∈ ZUT ↔ x.a = 0 ∧ x.b = 0 := Iff.rfl
theorem mem_E1UT {x : UT3 F4} : x ∈ E1UT ↔ x.b = 0 := Iff.rfl
theorem mem_E2UT {x : UT3 F4} : x ∈ E2UT ↔ x.a = 0 := Iff.rfl

theorem E1_inf_E2 : E1UT ⊓ E2UT = ZUT := by
  ext x
  simp only [Subgroup.mem_inf, mem_E1UT, mem_E2UT, mem_ZUT]
  tauto

theorem E1_sup_E2 : E1UT ⊔ E2UT = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : (⟨x.a, 0, 0⟩ : UT3 F4) ∈ E1UT := rfl
  have h2 : (⟨0, x.b, x.c - x.a * x.b⟩ : UT3 F4) ∈ E2UT := rfl
  have : x = (⟨x.a, 0, 0⟩ : UT3 F4) * ⟨0, x.b, x.c - x.a * x.b⟩ := by
    rw [UT3.mul_def]
    ext
    · simp
    · simp
    · show x.c = 0 + (x.c - x.a * x.b) + x.a * x.b
      ring
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

theorem E1_comm : ∀ x ∈ E1UT, ∀ y ∈ E1UT, x * y = y * x := by
  intro x hx y hy
  have hx' : x.b = 0 := hx
  have hy' : y.b = 0 := hy
  rw [UT3.mul_def, UT3.mul_def]
  ext
  · exact add_comm _ _
  · exact add_comm _ _
  · show x.c + y.c + x.a * y.b = y.c + x.c + y.a * x.b
    rw [hx', hy']
    ring

theorem E2_comm : ∀ x ∈ E2UT, ∀ y ∈ E2UT, x * y = y * x := by
  intro x hx y hy
  have hx' : x.a = 0 := hx
  have hy' : y.a = 0 := hy
  rw [UT3.mul_def, UT3.mul_def]
  ext
  · exact add_comm _ _
  · exact add_comm _ _
  · show x.c + y.c + x.a * y.b = y.c + x.c + y.a * x.b
    rw [hx', hy']
    ring

theorem E1_sq : ∀ x ∈ E1UT, x * x = 1 := by
  intro x hx
  rw [ut3_sq, show x.b = 0 from hx, mul_zero]
  rfl

theorem E2_sq : ∀ x ∈ E2UT, x * x = 1 := by
  intro x hx
  rw [ut3_sq, show x.a = 0 from hx, zero_mul]
  rfl

theorem invol_E {x : UT3 F4} (hx : x * x = 1) : x ∈ E1UT ∨ x ∈ E2UT := by
  rw [ut3_sq] at hx
  have h3 : x.a * x.b = 0 := by
    have := congrArg UT3.c hx
    exact this
  rcases mul_eq_zero.1 h3 with h | h
  · right
    exact h
  · left
    exact h

theorem comm_E : ∀ x ∈ E1UT, ∀ y ∈ E2UT, x * y * x⁻¹ * y⁻¹ ∈ ZUT := by
  intro x hx y hy
  have hx' : x.b = 0 := hx
  have hy' : y.a = 0 := hy
  rw [UT3.mul_def, UT3.inv_def, UT3.inv_def]
  refine ⟨?_, ?_⟩
  · show (x.a + y.a + -x.a) + -y.a = 0
    rw [hy']
    ring
  · show (x.b + y.b + -x.b) + -y.b = 0
    ring

theorem card_E1 : Nat.card ↥E1UT = 16 := by
  have e : ↥E1UT ≃ F4 × F4 :=
    { toFun := fun x => (x.1.a, x.1.c)
      invFun := fun p => ⟨⟨p.1, 0, p.2⟩, rfl⟩
      left_inv := fun x => by
        apply Subtype.ext
        ext
        · rfl
        · exact (show x.1.b = 0 from x.2).symm
        · rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_F4]

theorem card_E2 : Nat.card ↥E2UT = 16 := by
  have e : ↥E2UT ≃ F4 × F4 :=
    { toFun := fun x => (x.1.b, x.1.c)
      invFun := fun p => ⟨⟨0, p.1, p.2⟩, rfl⟩
      left_inv := fun x => by
        apply Subtype.ext
        ext
        · exact (show x.1.a = 0 from x.2).symm
        · rfl
        · rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_F4]

theorem card_ZUT : Nat.card ↥ZUT = 4 := by
  have e : ↥ZUT ≃ F4 :=
    { toFun := fun x => x.1.c
      invFun := fun p => ⟨⟨0, 0, p⟩, rfl, rfl⟩
      left_inv := fun x => by
        apply Subtype.ext
        ext
        · exact (show x.1.a = 0 from x.2.1).symm
        · exact (show x.1.b = 0 from x.2.2).symm
        · rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, card_F4]

theorem ut3_comm (x y : UT3 F4) :
    x * y * x⁻¹ * y⁻¹ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  ext <;> simp only [UT3.mul_def, UT3.inv_def] <;> ring

theorem normal_four_eq_Z {N : Subgroup (UT3 F4)} (hN : ∀ y, ∀ x ∈ N, y * x * y⁻¹ ∈ N)
    (h4 : Nat.card ↥N = 4) : N = ZUT := by
  have hZc := card_ZUT
  have : Finite ↥ZUT := Nat.finite_of_card_ne_zero (by omega)
  have : Finite ↥N := Nat.finite_of_card_ne_zero (by omega)
  by_cases hall : ∀ x ∈ N, x ∈ ZUT
  · exact Subgroup.eq_of_le_of_card_ge hall (by omega)
  · push Not at hall
    obtain ⟨u, huN, huZ⟩ := hall
    have hZN : ZUT ≤ N := by
      intro w hw
      have hw' : w = ⟨0, 0, w.c⟩ := by
        ext
        · exact hw.1
        · exact hw.2
        · rfl
      have key : ∀ p q : F4, (⟨0, 0, p * u.b - u.a * q⟩ : UT3 F4) ∈ N := by
        intro p q
        have h1 := mul_mem (hN ⟨p, q, 0⟩ u huN) (inv_mem huN)
        rw [ut3_comm ⟨p, q, 0⟩ u] at h1
        exact h1
      rw [hw']
      by_cases hb : u.b = 0
      · have ha : u.a ≠ 0 := fun ha => huZ ⟨ha, hb⟩
        have h1 := key 0 (-(w.c / u.a))
        have e : (0 : F4) * u.b - u.a * (-(w.c / u.a)) = w.c := by
          rw [zero_mul, zero_sub, mul_neg, neg_neg]
          field_simp
        rw [e] at h1
        exact h1
      · have h1 := key (w.c / u.b) 0
        have e : w.c / u.b * u.b - u.a * (0 : F4) = w.c := by
          rw [mul_zero, sub_zero]
          field_simp
        rw [e] at h1
        exact h1
    exact (Subgroup.eq_of_le_of_card_ge hZN (by omega)).symm

section Transport

variable {G : Type*} [Group G]

theorem exists_E_of_equiv {Y U : Subgroup G} (e : ↥Y ≃* UT3 F4) (hUY : U ≤ Y)
    (hU4 : Nat.card ↥U = 4) (hUN : ∀ y ∈ Y, ∀ w ∈ U, y * w * y⁻¹ ∈ U) :
    ∃ E₁ E₂ : Subgroup G, E₁ ≤ Y ∧ E₂ ≤ Y ∧ (∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) ∧
      (∀ a ∈ E₁, a * a = 1) ∧ (∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a) ∧ (∀ a ∈ E₂, a * a = 1) ∧
      Nat.card ↥E₁ = 16 ∧ Nat.card ↥E₂ = 16 ∧ E₁ ⊓ E₂ = U ∧ E₁ ⊔ E₂ = Y ∧
      (∀ y ∈ Y, y * y = 1 → y ∈ E₁ ∨ y ∈ E₂) ∧ (∀ a ∈ E₁, ∀ b ∈ E₂, a * b * a⁻¹ * b⁻¹ ∈ U) := by
  let φ : UT3 F4 →* G := Y.subtype.comp e.symm.toMonoidHom
  have hφinj : Function.Injective φ := Y.subtype_injective.comp e.symm.injective
  have hφY : ∀ t, φ t ∈ Y := fun t => (e.symm t).2
  have hφe : ∀ y : ↥Y, φ (e y) = (y : G) := fun y => by
    show ((e.symm (e y) : ↥Y) : G) = y
    rw [MulEquiv.symm_apply_apply]
  let Ubar : Subgroup (UT3 F4) := (U.subgroupOf Y).map e.toMonoidHom
  have hUbar4 : Nat.card ↥Ubar = 4 := by
    rw [Subgroup.card_map_of_injective e.injective, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv,
      hU4]
  have hUbarN : ∀ y, ∀ x ∈ Ubar, y * x * y⁻¹ ∈ Ubar := by
    intro y x hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨e.symm y * x₀ * (e.symm y)⁻¹, ?_, ?_⟩
    · show ((e.symm y * x₀ * (e.symm y)⁻¹ : ↥Y) : G) ∈ U
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hUN _ (e.symm y).2 _ hx₀
    · simp
  have hUbarZ : Ubar = ZUT := normal_four_eq_Z hUbarN hUbar4
  have hUφ : ZUT.map φ = U := by
    rw [← hUbarZ]
    show ((U.subgroupOf Y).map e.toMonoidHom).map φ = U
    rw [Subgroup.map_map]
    have : φ.comp e.toMonoidHom = Y.subtype := by
      ext y
      exact hφe y
    rw [this]
    exact Subgroup.map_subgroupOf_eq_of_le hUY
  have hmem : ∀ (T : Subgroup (UT3 F4)) (x : G), x ∈ T.map φ → ∃ t ∈ T, φ t = x := fun T x hx => by
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨t, ht, rfl⟩
  refine ⟨E1UT.map φ, E2UT.map φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨t, -, rfl⟩ := hmem _ _ hx
    exact hφY t
  · rintro x hx
    obtain ⟨t, -, rfl⟩ := hmem _ _ hx
    exact hφY t
  · rintro a ha b hb
    obtain ⟨x, hx, rfl⟩ := hmem _ _ ha
    obtain ⟨y, hy, rfl⟩ := hmem _ _ hb
    rw [← map_mul, ← map_mul, E1_comm x hx y hy]
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := hmem _ _ ha
    rw [← map_mul, E1_sq x hx, map_one]
  · rintro a ha b hb
    obtain ⟨x, hx, rfl⟩ := hmem _ _ ha
    obtain ⟨y, hy, rfl⟩ := hmem _ _ hb
    rw [← map_mul, ← map_mul, E2_comm x hx y hy]
  · rintro a ha
    obtain ⟨x, hx, rfl⟩ := hmem _ _ ha
    rw [← map_mul, E2_sq x hx, map_one]
  · rw [Subgroup.card_map_of_injective hφinj]
    exact card_E1
  · rw [Subgroup.card_map_of_injective hφinj]
    exact card_E2
  · rw [← Subgroup.map_inf _ _ φ hφinj, E1_inf_E2, hUφ]
  · rw [← Subgroup.map_sup, E1_sup_E2, Subgroup.map_top]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact hφY t
    · intro hy
      exact ⟨e ⟨y, hy⟩, hφe ⟨y, hy⟩⟩
  · intro y hy hy2
    set x : UT3 F4 := e ⟨y, hy⟩ with hx
    have hφx : φ x = y := hφe ⟨y, hy⟩
    have hxx : x * x = 1 := by
      apply hφinj
      rw [map_mul, hφx, hy2, map_one]
    rcases invol_E hxx with h1 | h1
    · left
      exact Subgroup.mem_map.2 ⟨x, h1, hφx⟩
    · right
      exact Subgroup.mem_map.2 ⟨x, h1, hφx⟩
  · rintro a ha b hb
    obtain ⟨x, hx, rfl⟩ := hmem _ _ ha
    obtain ⟨y, hy, rfl⟩ := hmem _ _ hb
    rw [← hUφ]
    refine Subgroup.mem_map.2 ⟨x * y * x⁻¹ * y⁻¹, comm_E x hx y hy, ?_⟩
    simp [map_mul, map_inv]

end Transport

end UT3F4

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
