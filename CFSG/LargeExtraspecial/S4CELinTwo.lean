module

public import CFSG.LargeExtraspecial.S4CELin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module

theorem mem_six_of_mem_closure {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y * x = y * x * y) {g : G} (hg : g ∈ closure {x, y}) :
    g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
  have step : ∀ u ∈ ({x, y} : Set G), ∀ g : G,
      (g = 1 ∨ g = x ∨ g = y ∨ g = x * y ∨ g = y * x ∨ g = x * y * x) →
      (u * g = 1 ∨ u * g = x ∨ u * g = y ∨ u * g = x * y ∨ u * g = y * x ∨
        u * g = x * y * x) := by
    intro u hu g hg
    rcases hu with rfl | hu
    · rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (mul_one _))
      · exact Or.inl hx
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, hx, one_mul])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [mul_assoc])))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          rw [← mul_assoc, ← mul_assoc, hx, one_mul])))))
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (mul_one _)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inl hy
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← mul_assoc, ← hxy])))))
      · exact Or.inr (Or.inl (by rw [← mul_assoc, hy, one_mul]))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by
          rw [hxy, ← mul_assoc, ← mul_assoc, hy, one_mul]))))
  induction hg using closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left u hu g _ ih => exact step u hu g ih
  | inv_mul_cancel u hu g _ ih =>
    have hu' : u⁻¹ = u := by
      rcases hu with rfl | hu
      · exact hxi
      · rw [Set.mem_singleton_iff] at hu
        rw [hu, hyi]
    rw [hu']
    exact step u hu g ih

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}

theorem eq_one_or_eq_of_mem_Ept_of_finrank_two (h : CEHyp π E a ⊤ (centreGroup V a))
    (hdim : finrank (ZMod 2) V = 2) {p : V} (hp : ∃ k, π k a = p) (hp0 : p ≠ 0) {e w : K}
    (he : e ∈ Ept π E a p) (hne : π e ≠ 1) (hw : w ∈ Ept π E a p) : w = 1 ∨ w = e := by
  obtain ⟨k, hk⟩ := hp
  have hmap : (Ept π E a p).map π = centreGroup V p := by
    rw [h.map_Ept hk, centreGroup_map_conj, hk]
  have hcard : Nat.card (centreGroup V p) = 2 := by
    rw [card_centreGroup hp0, hdim]
    rfl
  obtain ⟨t, -, ht⟩ := (Nat.card_eq_two_iff' (1 : centreGroup V p)).mp hcard
  have hπe : π e ∈ centreGroup V p := hmap ▸ ⟨e, he, rfl⟩
  have hπw : π w ∈ centreGroup V p := hmap ▸ ⟨w, hw, rfl⟩
  by_cases hw1 : π w = 1
  · exact Or.inl (h.eq_one_of_mem_Ept ⟨k, hk⟩ hw hw1)
  · right
    have h1 := ht ⟨π e, hπe⟩ fun h' => hne (congrArg Subtype.val h')
    have h2 := ht ⟨π w, hπw⟩ fun h' => hw1 (congrArg Subtype.val h')
    exact h.eq_of_mem_Ept ⟨k, hk⟩ hw he (congrArg Subtype.val (h2.trans h1.symm))

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_basis_of_ne_zero (b : Basis (Fin 2) (ZMod 2) V) {v : V} (hv : v ≠ 0) :
    v = b 0 ∨ v = b 1 ∨ v = b 0 + b 1 := by
  have hv' := b.sum_repr v
  rw [Fin.sum_univ_two] at hv'
  rcases OrthoF2.zmod2_eq_zero_or_eq_one (b.repr v 0) with h0 | h0 <;>
    rcases OrthoF2.zmod2_eq_zero_or_eq_one (b.repr v 1) with h1 | h1 <;>
    rw [h0, h1] at hv' <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hv'
  · exact absurd hv'.symm hv
  · exact Or.inr (Or.inl hv'.symm)
  · exact Or.inl hv'.symm
  · exact Or.inr (Or.inr hv'.symm)

theorem ker_eq_bot_of_linPair_two (ha : a ≠ 0) (hdim : finrank (ZMod 2) V = 2)
    (h : CEHyp π E a ⊤ (centreGroup V a)) : π.ker = ⊥ := by
  set b : Basis (Fin 2) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hdim
  have hvv : ∀ v : V, v + v = 0 := OrthoF2.vec_add_self
  have c1 : ∀ u v : V, u + (v + u) = v := fun u v => by
    rw [show u + (v + u) = v + (u + u) by abel, hvv, add_zero]
  have c2 : ∀ u v : V, u + v + v = u := fun u v => by rw [add_assoc, hvv, add_zero]
  have c3 : ∀ u v : V, u + v + u = v := fun u v => by
    rw [add_comm u v, add_assoc, hvv, add_zero]
  have hb10 : b 1 ≠ b 0 := fun e => absurd (b.injective e) (by decide)
  have h01 : (0 : Fin (1 + 1)) ≠ 1 := by decide
  have hp := exists_apply_eq_basis (m := 1) h ha b
  set X01 := linX (m := 1) b (0, 1, 1)
  set X10 := linX (m := 1) b (1, 0, 1)
  set x := linY (m := 1) π E a b (0, 1, 1)
  set y := linY (m := 1) π E a b (1, 0, 1)
  have hxE : x ∈ Ept π E a (b 0) := linY_mem h ha b h01 1
  have hyE : y ∈ Ept π E a (b 1) := linY_mem h ha b h01.symm 1
  have hπx : π x = X01 := apply_linY h ha b _
  have hπy : π y = X10 := apply_linY h ha b _
  have hX0 : X01 (b 0) = b 0 := linX_apply_basis b h01 1
  have hX1 : X01 (b 1) = b 1 + b 0 := by
    rw [linX_apply b h01, b.repr_self, Finsupp.single_apply, ite_eq_left rfl, one_mul, one_smul]
  have hY0 : X10 (b 0) = b 0 + b 1 := by
    rw [linX_apply b h01.symm, b.repr_self, Finsupp.single_apply, ite_eq_left rfl, one_mul,
      one_smul]
  have hY1 : X10 (b 1) = b 1 := linX_apply_basis b h01.symm 1
  have hext : ∀ f g : V ≃ₗ[ZMod 2] V, f (b 0) = g (b 0) → f (b 1) = g (b 1) → f = g :=
    fun f g h0 h1 => LinearEquiv.toLinearMap_injective (b.ext fun j => by
      fin_cases j
      · exact h0
      · exact h1)
  have hxx : x * x = 1 := h.eq_one_of_mem_Ept (hp 0) (mul_mem hxE hxE) (by
    rw [map_mul, hπx]
    refine hext _ _ ?_ ?_ <;>
      simp only [LinearEquiv.mul_apply, map_add, hX0, hX1, c2, LinearEquiv.coe_one, id_eq])
  have hyy : y * y = 1 := h.eq_one_of_mem_Ept (hp 1) (mul_mem hyE hyE) (by
    rw [map_mul, hπy]
    refine hext _ _ ?_ ?_ <;>
      simp only [LinearEquiv.mul_apply, map_add, hY0, hY1, c2, LinearEquiv.coe_one, id_eq])
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_left hxx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hyy
  have hp01 : ∃ k, π k a = b 0 + b 1 := by
    obtain ⟨k, hk⟩ := hp 1
    exact ⟨x * k, by rw [map_mul, LinearEquiv.mul_apply, hk, hπx, hX1, add_comm]⟩
  have hxyx : x * y * x ∈ Ept π E a (b 0 + b 1) := by
    have := h.conj_mem_Ept (hp 1) hyE x
    rwa [hxi, hπx, hX1, add_comm] at this
  have hyxy : y * x * y ∈ Ept π E a (b 0 + b 1) := by
    have := h.conj_mem_Ept (hp 0) hxE y
    rwa [hyi, hπy, hY0] at this
  have hbraid : x * y * x = y * x * y := h.eq_of_mem_Ept hp01 hxyx hyxy (by
    rw [map_mul, map_mul, map_mul, map_mul, hπx, hπy]
    refine hext _ _ ?_ ?_ <;>
      simp only [LinearEquiv.mul_apply, map_add, hX0, hX1, hY0, hY1, c1, c3])
  have hne : ∀ {e : K}, π e (b 0) ≠ b 0 ∨ π e (b 1) ≠ b 1 → π e ≠ 1 := by
    rintro e (he | he) h1 <;> rw [h1] at he <;> exact he rfl
  have hx1 : π x ≠ 1 := hne (Or.inr (by
    rw [hπx, hX1]
    exact fun e => b.ne_zero 0 (add_eq_left.mp e)))
  have hy1 : π y ≠ 1 := hne (Or.inl (by
    rw [hπy, hY0]
    exact fun e => b.ne_zero 1 (add_eq_left.mp e)))
  have hxyx0 : π (x * y * x) (b 0) = b 1 := by
    rw [map_mul, map_mul, hπx, hπy]
    simp only [LinearEquiv.mul_apply, map_add, hX0, hX1, hY0, c1]
  have hxyx1 : π (x * y * x) ≠ 1 := hne (Or.inl (by rw [hxyx0]; exact hb10))
  have hb01 : b 0 + b 1 ≠ 0 := fun h0 => hb10 (by
    calc b 1 = b 0 + (b 1 + b 0) := (c1 _ _).symm
      _ = b 0 := by rw [add_comm (b 1), h0, add_zero])
  have hgen : ∀ g : K, g ∈ closure ({x, y} : Set K) := by
    intro g
    have hg : g ∈ closure {k | ∃ z : K, ∃ e ∈ E, k = z * e * z⁻¹} := by
      rw [h.closure_conj_eq_top]
      exact mem_top g
    refine (closure_le _).mpr ?_ hg
    rintro _ ⟨z, e, he, rfl⟩
    have hw : z * e * z⁻¹ ∈ Ept π E a (π z a) :=
      h.conj_mem_Ept ⟨1, by rw [map_one]; rfl⟩ (by rwa [h.Ept_self]) z
    have hpz0 : π z a ≠ 0 := fun h0 => ha ((π z).injective (h0.trans (map_zero _).symm))
    have hxm : x ∈ closure ({x, y} : Set K) := subset_closure (Set.mem_insert _ _)
    have hym : y ∈ closure ({x, y} : Set K) := subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases eq_basis_of_ne_zero b hpz0 with hq | hq | hq <;> rw [hq] at hw
    · rcases eq_one_or_eq_of_mem_Ept_of_finrank_two h hdim (hp 0) (b.ne_zero 0) hxE hx1 hw
        with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact hxm
    · rcases eq_one_or_eq_of_mem_Ept_of_finrank_two h hdim (hp 1) (b.ne_zero 1) hyE hy1 hw
        with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact hym
    · rcases eq_one_or_eq_of_mem_Ept_of_finrank_two h hdim hp01 hb01 hxyx hxyx1 hw
        with h1 | h1 <;> rw [h1]
      · exact one_mem _
      · exact mul_mem (mul_mem hxm hym) hxm
  rw [eq_bot_iff]
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [mem_bot]
  rcases mem_six_of_mem_closure hxx hyy hbraid (hgen z) with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hz hx1
  · exact absurd hz hy1
  · exact absurd hz (hne (Or.inl (by
      rw [map_mul, hπx, hπy, LinearEquiv.mul_apply, hY0, map_add, hX0, hX1, c1]
      exact hb10)))
  · exact absurd hz (hne (Or.inr (by
      rw [map_mul, hπx, hπy, LinearEquiv.mul_apply, hX1, map_add, hY1, hY0, c1]
      exact hb10.symm)))
  · exact absurd hz hxyx1

theorem ker_eq_bot_of_linPair (ha : a ≠ 0) (hdim : 2 ≤ finrank (ZMod 2) V)
    (h : CEHyp π E a ⊤ (centreGroup V a)) : π.ker = ⊥ := by
  rcases hdim.eq_or_lt with h2 | h3
  · exact ker_eq_bot_of_linPair_two ha h2.symm h
  · exact ker_eq_bot_of_linPair_of_three_le ha h3 h

end CFSG.LargeExtraspecial.S4
