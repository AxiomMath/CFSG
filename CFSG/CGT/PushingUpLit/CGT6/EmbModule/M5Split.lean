module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5Stab

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EmbModule

structure SplitCfg {E : Type} [Group E] (u v z0 a1 a2 c : E) : Prop where
  a1_cube : a1 ^ 3 = 1
  a2_cube : a2 ^ 3 = 1
  z0_cube : z0 ^ 3 = 1
  u_cube : u ^ 3 = 1
  a12 : a1 * a2 = a2 * a1
  ua1 : u * a1 = a1 * u
  ua2 : u * a2 = a2 * u
  va1 : v * a1 = a1 * v
  va2 : v * a2 = a2 * v
  za1 : z0 * a1 = a1 * z0
  za2 : z0 * a2 = a2 * z0
  uz : u * z0 = z0 * u
  vz : v * z0 = z0 * v
  uv : u * v = z0 * v * u
  ca1 : c * a1 = a2 * c
  ca2 : c * a2 = a1 * a2 * c
  a1_ne : a1 ≠ 1
  z0_ne : z0 ≠ 1

variable {V : Type} [CommGroup V] {E : Type} [Group E]

theorem mul_cube_aux {p q : E} (hpq : p * q = q * p) (hp : p ^ 3 = 1) (hq : q ^ 3 = 1) :
    q * ((p * q) * (p * q)) * p = 1 := by
  have h3 : (p * q) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute p q from hpq), hp, hq, one_mul]
  have hr : Commute p (p * q) := (Commute.refl p).mul_right (show Commute p q from hpq)
  have hrr : Commute p ((p * q) * (p * q)) := hr.mul_right hr
  calc q * ((p * q) * (p * q)) * p = q * (p * ((p * q) * (p * q))) := by
        rw [mul_assoc, ← hrr.eq]
    _ = (q * p) * ((p * q) * (p * q)) := (mul_assoc _ _ _).symm
    _ = (p * q) * ((p * q) * (p * q)) := by rw [← hpq]
    _ = (p * q) ^ 3 := (pow_three _).symm
    _ = 1 := h3

theorem split_bound [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {u v z0 a1 a2 c : E}
    (cfg : SplitCfg u v z0 a1 a2 c) (ρ : E →* MulAut V) (hρ : Function.Injective ρ) :
    2 ^ 14 ≤ Nat.card V := by
  have h : Comm3 a1 a2 := ⟨cfg.a1_cube, cfg.a2_cube, cfg.a12⟩
  have hca1 : c * a1 * c⁻¹ = a2 := mul_inv_eq_iff_eq_mul.2 cfg.ca1
  have hca2 : c * a2 * c⁻¹ = a1 * a2 := mul_inv_eq_iff_eq_mul.2 cfg.ca2
  have hA : ∀ w, ρ c (avgA ρ a1 a2 w) = avgA ρ a1 a2 (ρ c w) := by
    refine rho_avgA_conj ρ h (m1 := (0, 1)) (m2 := (1, 1)) (by decide) ?_ ?_
    · rw [el_01]; exact hca1
    · rw [el_11]; exact hca2
  have d0 : dirs 0 = (1, 0) := rfl
  have d1 : dirs 1 = (0, 1) := rfl
  have d2 : dirs 2 = (1, 1) := rfl
  have d3 : dirs 3 = (1, 2) := rfl
  have c01 : c * el a1 a2 (dirs 0) * c⁻¹ = el a1 a2 (dirs 1) := by
    rw [d0, d1, el_10, el_01]; exact hca1
  have c12 : c * el a1 a2 (dirs 1) * c⁻¹ = el a1 a2 (dirs 2) := by
    rw [d1, d2, el_01, el_11]; exact hca2
  have c23 : c * el a1 a2 (dirs 2) * c⁻¹ = el a1 a2 (dirs 3) := by
    rw [d2, d3, el_11, el_12]
    have e : c * (a1 * a2) * c⁻¹ = (c * a1 * c⁻¹) * (c * a2 * c⁻¹) := by simp [mul_assoc]
    rw [e, hca1, hca2, pow_two, ← mul_assoc, ← cfg.a12, mul_assoc]
  have c30 : c * el a1 a2 (dirs 3) * c⁻¹ = (el a1 a2 (dirs 0))⁻¹ := by
    rw [d3, d0, el_12, el_10]
    have e : c * (a1 * a2 ^ 2) * c⁻¹ =
        (c * a1 * c⁻¹) * ((c * a2 * c⁻¹) * (c * a2 * c⁻¹)) := by
      simp [pow_two, mul_assoc]
    rw [e, hca1, hca2]
    exact eq_inv_of_mul_eq_one_left (mul_cube_aux cfg.a12 cfg.a1_cube cfg.a2_cube)
  have h01 := card_piece_le ρ hA (Or.inl c01)
  have h12 := card_piece_le ρ hA (Or.inl c12)
  have h23 := card_piece_le ρ hA (Or.inl c23)
  have h30 := card_piece_le ρ hA (Or.inr c30)
  have e01 : Nat.card (piece ρ a1 a2 0) = Nat.card (piece ρ a1 a2 1) :=
    le_antisymm h01 (h12.trans (h23.trans h30))
  have e12 : Nat.card (piece ρ a1 a2 1) = Nat.card (piece ρ a1 a2 2) :=
    le_antisymm h12 (h23.trans (h30.trans h01))
  have e23 : Nat.card (piece ρ a1 a2 2) = Nat.card (piece ρ a1 a2 3) :=
    le_antisymm h23 (h30.trans (h01.trans h12))
  have hN : ∀ i : Fin 4, Nat.card (piece ρ a1 a2 i) = Nat.card (piece ρ a1 a2 0) := by
    intro i
    fin_cases i
    · rfl
    · exact e01.symm
    · exact (e01.trans e12).symm
    · exact (e01.trans (e12.trans e23)).symm
  have hne : piece ρ a1 a2 0 ≠ ⊥ := by
    intro hb
    have hcard1 : ∀ i, piece ρ a1 a2 i = ⊥ := by
      intro i
      refine Subgroup.card_eq_one.1 ?_
      rw [hN i, hb]
      exact Subgroup.card_bot
    have hfix : ∀ w : V, ρ a1 w = w := by
      intro w
      obtain ⟨c0, hc0, p, hp, rfl⟩ := spanning ρ hV h w
      have hp1 : ∀ i, p i = 1 := fun i => by simpa [hcard1 i] using hp i
      simp only [hp1, Finset.prod_const_one, mul_one]
      exact hc0.1
    apply cfg.a1_ne
    apply hρ
    rw [map_one]
    ext w
    exact hfix w
  have h4 : ∀ i, 4 ≤ Nat.card (piece ρ a1 a2 i) := by
    intro i
    rw [hN i]
    exact (piece_eq_bot_or_four_le ρ hV h 0).resolve_left hne
  have stabC : ∀ g, g * a1 = a1 * g → g * a2 = a2 * g → g ∈ setStab ρ (cen ρ a1 a2) :=
    fun g hg1 hg2 => mem_setStab_cen ρ hg1 hg2
  have stabP : ∀ g, g * a1 = a1 * g → g * a2 = a2 * g →
      ∀ i, g ∈ setStab ρ (piece ρ a1 a2 i) :=
    fun g hg1 hg2 i => mem_setStab_piece ρ h hg1 hg2 i
  have hz' : z0⁻¹ ^ 3 = 1 := by rw [inv_pow, cfg.z0_cube, inv_one]
  have hzy : z0⁻¹ * u = u * z0⁻¹ := (show Commute u z0 from cfg.uz).inv_right.eq.symm
  have hxz : v * z0⁻¹ = z0⁻¹ * v := (show Commute v z0 from cfg.vz).inv_right.eq
  have hxy : v * u * v⁻¹ = z0⁻¹ * u := by
    have e1 : v * u = z0⁻¹ * u * v := by
      calc v * u = z0⁻¹ * (z0 * (v * u)) := by rw [inv_mul_cancel_left]
        _ = z0⁻¹ * (z0 * v * u) := by rw [mul_assoc]
        _ = z0⁻¹ * (u * v) := by rw [cfg.uv]
        _ = z0⁻¹ * u * v := by rw [mul_assoc]
    rw [e1, mul_inv_cancel_right]
  have dichU : ∀ U : Subgroup V, u ∈ setStab ρ U → v ∈ setStab ρ U → z0 ∈ setStab ρ U →
      (∀ w ∈ U, ρ z0 w = w) ∨ 64 ≤ Nat.card U := by
    intro U hu hv hz
    rcases dich ρ hV U (inv_mem hz) hu hv hz' cfg.u_cube hzy hxz hxy with h1 | h2
    · refine Or.inl fun w hw => ?_
      have hw' := h1 w hw
      calc ρ z0 w = ρ z0 (ρ z0⁻¹ w) := by rw [hw']
        _ = w := by rw [rho_rho, mul_inv_cancel, map_one]; rfl
    · exact Or.inr h2
  have hcard := card_cen_mul_prod_piece_le ρ hV h
  rw [Fin.prod_univ_four] at hcard
  have dC := dichU (cen ρ a1 a2) (stabC u cfg.ua1 cfg.ua2) (stabC v cfg.va1 cfg.va2)
    (stabC z0 cfg.za1 cfg.za2)
  have dP : ∀ i, (∀ w ∈ piece ρ a1 a2 i, ρ z0 w = w) ∨ 64 ≤ Nat.card (piece ρ a1 a2 i) :=
    fun i => dichU _ (stabP u cfg.ua1 cfg.ua2 i) (stabP v cfg.va1 cfg.va2 i)
      (stabP z0 cfg.za1 cfg.za2 i)
  rcases dC with hCt | hC64
  · by_cases hex : ∃ i, 64 ≤ Nat.card (piece ρ a1 a2 i)
    · obtain ⟨i, hi⟩ := hex
      have h64 : ∀ j, 64 ≤ Nat.card (piece ρ a1 a2 j) := fun j => by
        rw [hN j]
        rw [hN i] at hi
        exact hi
      have hcen : 0 < Nat.card (cen ρ a1 a2) := Nat.card_pos
      calc 2 ^ 14 ≤ 1 * (64 * 64 * 64 * 64) := by norm_num
        _ ≤ Nat.card (cen ρ a1 a2) * (Nat.card (piece ρ a1 a2 0) * Nat.card (piece ρ a1 a2 1) *
            Nat.card (piece ρ a1 a2 2) * Nat.card (piece ρ a1 a2 3)) :=
          Nat.mul_le_mul hcen (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (h64 0) (h64 1))
            (h64 2)) (h64 3))
        _ ≤ Nat.card V := hcard
    · exfalso
      push Not at hex
      have hPt : ∀ i, ∀ w ∈ piece ρ a1 a2 i, ρ z0 w = w :=
        fun i => (dP i).resolve_right (not_le.2 (hex i))
      have hz0 : ∀ w : V, ρ z0 w = w := by
        intro w
        obtain ⟨c0, hc0, p, hp, rfl⟩ := spanning ρ hV h w
        rw [map_mul, map_prod, hCt c0 hc0]
        congr 1
        exact Finset.prod_congr rfl (fun i _ => hPt i (p i) (hp i))
      apply cfg.z0_ne
      apply hρ
      rw [map_one]
      ext w
      exact hz0 w
  · calc 2 ^ 14 = 64 * (4 * 4 * 4 * 4) := by norm_num
      _ ≤ Nat.card (cen ρ a1 a2) * (Nat.card (piece ρ a1 a2 0) * Nat.card (piece ρ a1 a2 1) *
          Nat.card (piece ρ a1 a2 2) * Nat.card (piece ρ a1 a2 3)) :=
        Nat.mul_le_mul hC64 (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (h4 0) (h4 1))
          (h4 2)) (h4 3))
      _ ≤ Nat.card V := hcard

end CFSG.CGT.PushingUpLit.CGT6.EmbModule
