module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Rank2

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

variable {V : Type} [CommGroup V] {G : Type} [Group G]

section Restrict

variable (ρ : G →* MulAut V) (W : Subgroup V)

@[expose] def setStab : Subgroup G where
  carrier := {g | ∀ w : V, ρ g w ∈ W ↔ w ∈ W}
  one_mem' := by
    intro w
    change ρ 1 w ∈ W ↔ w ∈ W
    rw [map_one]
    rfl
  mul_mem' := fun {a b} ha hb w => by
    rw [← rho_rho]
    exact (ha (ρ b w)).trans (hb w)
  inv_mem' := fun {a} ha w => by
    have h1 := ha (ρ a⁻¹ w)
    rw [rho_rho, mul_inv_cancel, map_one] at h1
    exact h1.symm

theorem mem_setStab_of {g : G} (h1 : ∀ w ∈ W, ρ g w ∈ W) (h2 : ∀ w ∈ W, ρ g⁻¹ w ∈ W) :
    g ∈ setStab ρ W := by
  intro w
  refine ⟨fun hw => ?_, h1 w⟩
  have := h2 _ hw
  rwa [rho_rho, inv_mul_cancel, map_one] at this

@[expose] def restrictAction : setStab ρ W →* MulAut W where
  toFun g :=
    { toFun := fun w => ⟨ρ g w, ((g.2 w).2 w.2)⟩
      invFun := fun w => ⟨ρ g⁻¹ w, (((setStab ρ W).inv_mem g.2) w).2 w.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        change ρ (g : G)⁻¹ (ρ g w) = w
        rw [rho_rho, inv_mul_cancel, map_one]
        rfl
      right_inv := fun w => by
        apply Subtype.ext
        change ρ g (ρ (g : G)⁻¹ w) = w
        rw [rho_rho, mul_inv_cancel, map_one]
        rfl
      map_mul' := fun a b => Subtype.ext ((ρ g).map_mul _ _) }
  map_one' := by
    ext w
    change ρ ((1 : setStab ρ W) : G) w = w
    rw [Subgroup.coe_one, map_one]
    rfl
  map_mul' := fun a b => by
    ext w
    change ρ ((a * b : setStab ρ W) : G) w = ρ a (ρ b w)
    rw [Subgroup.coe_mul, ← rho_rho]

end Restrict

section Heis

variable (ρ : G →* MulAut V)

theorem heis_dich [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {z y x : G} (hz : z ^ 3 = 1)
    (hy : y ^ 3 = 1) (hzy : z * y = y * z) (hxz : x * z = z * x) (hxy : x * y * x⁻¹ = z * y) :
    (piece ρ z y 1 = ⊥ ∧ piece ρ z y 2 = ⊥ ∧ piece ρ z y 3 = ⊥) ∨
      (4 ≤ Nat.card (piece ρ z y 1) ∧ 4 ≤ Nat.card (piece ρ z y 2) ∧
        4 ≤ Nat.card (piece ρ z y 3)) := by
  have h : Comm3 z y := ⟨hz, hy, hzy⟩
  have hxz' : x * z * x⁻¹ = z := by rw [hxz]; group
  have hA : ∀ w, ρ x (avgA ρ z y w) = avgA ρ z y (ρ x w) := by
    refine rho_avgA_conj ρ h (m1 := (1, 0)) (m2 := (1, 1)) (by decide) ?_ ?_
    · rw [el_10, hxz']
    · rw [el_11, hxy]
  have d1 : dirs 1 = (0, 1) := rfl
  have d2 : dirs 2 = (1, 1) := rfl
  have d3 : dirs 3 = (1, 2) := rfl
  have c12 : x * el z y (dirs 1) * x⁻¹ = el z y (dirs 2) := by
    rw [d1, d2, el_01, el_11, hxy]
  have hz' : z * z * z = 1 := by rw [← pow_three']; exact hz
  have hy' : y * y * y = 1 := by rw [← pow_three']; exact hy
  have c23 : x * el z y (dirs 2) * x⁻¹ = (el z y (dirs 3))⁻¹ := by
    rw [d2, d3, el_11, el_12]
    have e : x * (z * y) * x⁻¹ = (x * z * x⁻¹) * (x * y * x⁻¹) := by simp [mul_assoc]
    rw [e, hxz', hxy]
    refine eq_inv_of_mul_eq_one_left ?_
    calc z * (z * y) * (z * y ^ 2) = z * z * (y * z) * y * y := by simp only [pow_two, mul_assoc]
      _ = z * z * (z * y) * y * y := by rw [← hzy]
      _ = (z * z * z) * (y * y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hz', hy', one_mul]
  have c31 : x * el z y (dirs 3) * x⁻¹ = (el z y (dirs 1))⁻¹ := by
    rw [d3, d1, el_12, el_01]
    have e : x * (z * y ^ 2) * x⁻¹ = (x * z * x⁻¹) * ((x * y * x⁻¹) * (x * y * x⁻¹)) := by
      simp [pow_two, mul_assoc]
    rw [e, hxz', hxy]
    refine eq_inv_of_mul_eq_one_left ?_
    calc z * ((z * y) * (z * y)) * y = z * z * (y * z) * y * y := by simp only [mul_assoc]
      _ = z * z * (z * y) * y * y := by rw [← hzy]
      _ = (z * z * z) * (y * y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hz', hy', one_mul]
  have h12 := card_piece_le ρ hA (Or.inl c12)
  have h23 := card_piece_le ρ hA (Or.inr c23)
  have h31 := card_piece_le ρ hA (Or.inr c31)
  have e12 : Nat.card (piece ρ z y 1) = Nat.card (piece ρ z y 2) := le_antisymm h12 (h23.trans h31)
  have e23 : Nat.card (piece ρ z y 2) = Nat.card (piece ρ z y 3) := le_antisymm h23 (h31.trans h12)
  rcases piece_eq_bot_or_four_le ρ hV h 1 with hb | h4
  · left
    have hc1 : Nat.card (piece ρ z y 1) = 1 := by rw [hb]; exact Subgroup.card_bot
    exact ⟨hb, Subgroup.card_eq_one.1 (by rw [← e12]; exact hc1),
      Subgroup.card_eq_one.1 (by rw [← e23, ← e12]; exact hc1)⟩
  · right
    have h4' : 4 ≤ Nat.card (piece ρ z y 2) := e12 ▸ h4
    exact ⟨h4, h4', e23 ▸ h4'⟩

theorem heis_card [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {z y x : G} (hz : z ^ 3 = 1)
    (hy : y ^ 3 = 1) (hzy : z * y = y * z) (hxz : x * z = z * x) (hxy : x * y * x⁻¹ = z * y)
    (hfpf : ∀ w : V, ρ z w = w → w = 1) : Nat.card V = 1 ∨ 64 ≤ Nat.card V := by
  have h : Comm3 z y := ⟨hz, hy, hzy⟩
  have hcard := card_cen_mul_prod_piece_le ρ hV h
  rw [Fin.prod_univ_four] at hcard
  have hcen : 0 < Nat.card (cen ρ z y) := Nat.card_pos
  have hp0 : 0 < Nat.card (piece ρ z y 0) := Nat.card_pos
  rcases heis_dich ρ hV hz hy hzy hxz hxy with ⟨hb1, hb2, hb3⟩ | ⟨h41, h42, h43⟩
  · left
    have htriv : ∀ w : V, w = 1 := by
      intro w
      obtain ⟨c, hc, p, hp, rfl⟩ := spanning ρ hV h w
      have hc' : c = 1 := hfpf c hc.1
      have hp0' : p 0 = 1 := by
        have : ρ (el z y (dirs 0)) (p 0) = p 0 := (hp 0).1
        have d0 : dirs 0 = (1, 0) := rfl
        rw [d0, el_10] at this
        exact hfpf _ this
      have hp1' : p 1 = 1 := by simpa [hb1] using hp 1
      have hp2' : p 2 = 1 := by simpa [hb2] using hp 2
      have hp3' : p 3 = 1 := by simpa [hb3] using hp 3
      rw [Fin.prod_univ_four, hc', hp0', hp1', hp2', hp3']
      simp
    exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (htriv a).trans (htriv b).symm⟩, ⟨1⟩⟩
  · right
    calc 64 = 1 * (1 * 4 * 4 * 4) := by norm_num
      _ ≤ Nat.card (cen ρ z y) * (Nat.card (piece ρ z y 0) * Nat.card (piece ρ z y 1) *
          Nat.card (piece ρ z y 2) * Nat.card (piece ρ z y 3)) := by
        refine Nat.mul_le_mul hcen ?_
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp0 h41) h42) h43
      _ ≤ Nat.card V := hcard

theorem heis_card_sub [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (W : Subgroup V) {z y x : G}
    (hzW : z ∈ setStab ρ W) (hyW : y ∈ setStab ρ W) (hxW : x ∈ setStab ρ W) (hz : z ^ 3 = 1)
    (hy : y ^ 3 = 1) (hzy : z * y = y * z) (hxz : x * z = z * x) (hxy : x * y * x⁻¹ = z * y)
    (hfpf : ∀ w ∈ W, ρ z w = w → w = 1) : W = ⊥ ∨ 64 ≤ Nat.card W := by
  have key := heis_card (restrictAction ρ W) (V := W) (G := setStab ρ W)
    (fun v => Subtype.ext (hV v)) (z := ⟨z, hzW⟩) (y := ⟨y, hyW⟩) (x := ⟨x, hxW⟩)
    (Subtype.ext hz) (Subtype.ext hy) (Subtype.ext hzy) (Subtype.ext hxz) (Subtype.ext hxy)
    (fun w hw => Subtype.ext (hfpf w w.2 (congrArg Subtype.val hw)))
  rcases key with h1 | h2
  · exact Or.inl (Subgroup.card_eq_one.1 h1)
  · exact Or.inr h2

end Heis

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
