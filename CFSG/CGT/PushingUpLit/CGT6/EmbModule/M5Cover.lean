module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Stab

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

structure CoverCfg {E : Type} [Group E] (u v a1 a2 c0 : E) : Prop where
  a1_cube : a1 ^ 3 = 1
  a2_cube : a2 ^ 3 = 1
  c0_cube : c0 ^ 3 = 1
  c0u : c0 * u = u * c0
  c0v : c0 * v = v * c0
  c0a1 : c0 * a1 = a1 * c0
  c0a2 : c0 * a2 = a2 * c0
  a12 : a1 * a2 = a2 * a1
  va2 : v * a2 = a2 * v
  ua2 : u * a2 = c0 * a2 * u
  va1 : v * a1 = c0 * c0 * a1 * v
  c0_ne : c0 ≠ 1

variable {V : Type} [CommGroup V] {E : Type} [Group E]

theorem cover_bound [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {u v a1 a2 c0 : E}
    (cfg : CoverCfg u v a1 a2 c0) (ρ : E →* MulAut V) (hρ : Function.Injective ρ) :
    2 ^ 18 ≤ Nat.card V := by
  have h : Comm3 c0 a2 := ⟨cfg.c0_cube, cfg.a2_cube, cfg.c0a2⟩
  have hxy : u * a2 * u⁻¹ = c0 * a2 := mul_inv_eq_iff_eq_mul.2 cfg.ua2
  have d0 : dirs 0 = (1, 0) := rfl
  have hc0 : ∀ w, ρ c0⁻¹ w = w → ρ c0 w = w := fun w hw => by
    calc ρ c0 w = ρ c0 (ρ c0⁻¹ w) := by rw [hw]
      _ = w := by rw [rho_rho, mul_inv_cancel, map_one]; rfl
  have hcard := card_cen_mul_prod_piece_le ρ hV h
  rw [Fin.prod_univ_four] at hcard
  have hcen : 0 < Nat.card (cen ρ c0 a2) := Nat.card_pos
  have hp0 : 0 < Nat.card (piece ρ c0 a2 0) := Nat.card_pos
  rcases heis_dich ρ hV cfg.c0_cube cfg.a2_cube cfg.c0a2 cfg.c0u.symm hxy with
    ⟨hb1, hb2, hb3⟩ | ⟨h41, h42, h43⟩
  · exfalso
    have hfix : ∀ w : V, ρ c0 w = w := by
      intro w
      obtain ⟨c, hc, p, hp, rfl⟩ := spanning ρ hV h w
      have hp0' : ρ c0 (p 0) = p 0 := by
        have := (hp 0).1
        change ρ (el c0 a2 (dirs 0)) (p 0) = p 0 at this
        rwa [d0, el_10] at this
      have hp1 : p 1 = 1 := by simpa [hb1] using hp 1
      have hp2 : p 2 = 1 := by simpa [hb2] using hp 2
      have hp3 : p 3 = 1 := by simpa [hb3] using hp 3
      rw [Fin.prod_univ_four, hp1, hp2, hp3, map_mul, map_mul, map_mul, map_mul, map_one,
        hc.1, hp0']
    apply cfg.c0_ne
    apply hρ
    rw [map_one]
    ext w
    exact hfix w
  ·
    have hz' : c0⁻¹ ^ 3 = 1 := by rw [inv_pow, cfg.c0_cube, inv_one]
    have hzy : c0⁻¹ * a1 = a1 * c0⁻¹ := (show Commute a1 c0 from cfg.c0a1.symm).inv_right.eq.symm
    have hxz : v * c0⁻¹ = c0⁻¹ * v := (show Commute v c0 from cfg.c0v.symm).inv_right.eq
    have hc0inv : c0 * c0 = c0⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact cfg.c0_cube)
    have hxy' : v * a1 * v⁻¹ = c0⁻¹ * a1 := by
      rw [mul_inv_eq_iff_eq_mul.2 cfg.va1, hc0inv]
    have hP : ∀ i : Fin 4, i ≠ 0 → 4 ≤ Nat.card (piece ρ c0 a2 i) →
        64 ≤ Nat.card (piece ρ c0 a2 i) := by
      intro i hi hi4
      have hzs : c0 ∈ setStab ρ (piece ρ c0 a2 i) :=
        mem_setStab_piece ρ h rfl cfg.c0a2 i
      have has : a1 ∈ setStab ρ (piece ρ c0 a2 i) :=
        mem_setStab_piece ρ h cfg.c0a1.symm cfg.a12 i
      have hvs : v ∈ setStab ρ (piece ρ c0 a2 i) :=
        mem_setStab_piece ρ h cfg.c0v.symm cfg.va2 i
      rcases heis_card_sub ρ hV (piece ρ c0 a2 i) (inv_mem hzs) has hvs hz' cfg.a1_cube hzy hxz
        hxy' (fun w hw hfix => piece_fpf ρ hV h hi hw (by
          rw [d0, el_10]
          exact hc0 w hfix)) with hbot | hbig
      · rw [hbot, Subgroup.card_bot] at hi4
        omega
      · exact hbig
    have h1 := hP 1 (by decide) h41
    have h2 := hP 2 (by decide) h42
    have h3 := hP 3 (by decide) h43
    calc 2 ^ 18 = 1 * (1 * 64 * 64 * 64) := by norm_num
      _ ≤ Nat.card (cen ρ c0 a2) * (Nat.card (piece ρ c0 a2 0) * Nat.card (piece ρ c0 a2 1) *
          Nat.card (piece ρ c0 a2 2) * Nat.card (piece ρ c0 a2 3)) :=
        Nat.mul_le_mul hcen (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp0 h1) h2) h3)
      _ ≤ Nat.card V := hcard

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
