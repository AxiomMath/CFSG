module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnLift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermFacts1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk5AnPermFacts2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open Subgroup Equiv CFSG CFSG.GH74.GLS.IVK.Lifted CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

section Pair

variable {G : Type*} [Group G]

theorem zpow2_zero (g : G) : zpow2 g 0 = 1 := by simp [zpow2]
theorem zpow2_one (g : G) : zpow2 g 1 = g := by simp [zpow2]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zpow2_add {g : G} (hg : g * g = 1) (a b : ZMod 2) : zpow2 g (a + b) = zpow2 g a * zpow2 g b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [zpow2_zero]
  · simp [zpow2_zero]
  · simp [zpow2_zero]
  · have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [this, zpow2_zero, zpow2_one, hg]

theorem commute_zpow2 {g h : G} (hgh : Commute g h) (a b : ZMod 2) : Commute (zpow2 g a) (zpow2 h b) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rw [zpow2_zero, zpow2_zero]
  · rw [zpow2_zero]; exact Commute.one_left _
  · rw [zpow2_zero]; exact Commute.one_right _
  · rw [zpow2_one, zpow2_one]; exact hgh

@[expose] def pairp (p q : G) (x : F4c) : G := zpow2 p x.a * zpow2 q x.b

theorem pairp_one (p q : G) : pairp p q 1 = p := by
  show zpow2 p (1 : ZMod 2) * zpow2 q (0 : ZMod 2) = p
  rw [zpow2_one, zpow2_zero, mul_one]

theorem pairp_omega (p q : G) : pairp p q omegaC = q := by
  show zpow2 p (0 : ZMod 2) * zpow2 q (1 : ZMod 2) = q
  rw [zpow2_one, zpow2_zero, one_mul]

theorem pairp_one_omega (p q : G) : pairp p q (1 + omegaC) = p * q := by
  show zpow2 p (1 : ZMod 2) * zpow2 q (1 : ZMod 2) = p * q
  rw [zpow2_one, zpow2_one]

theorem pairp_zero (p q : G) : pairp p q 0 = 1 := by
  show zpow2 p (0 : ZMod 2) * zpow2 q (0 : ZMod 2) = 1
  rw [zpow2_zero, zpow2_zero, mul_one]

theorem pairp_add {p q : G} (hp : p * p = 1) (hq : q * q = 1) (hpq : Commute p q) (x y : F4c) :
    pairp p q (x + y) = pairp p q x * pairp p q y := by
  have h1 : zpow2 p (x.a + y.a) = zpow2 p x.a * zpow2 p y.a := zpow2_add hp _ _
  have h2 : zpow2 q (x.b + y.b) = zpow2 q x.b * zpow2 q y.b := zpow2_add hq _ _
  have hc : zpow2 q x.b * zpow2 p y.a = zpow2 p y.a * zpow2 q x.b :=
    (commute_zpow2 hpq.symm x.b y.a).eq
  show zpow2 p (x.a + y.a) * zpow2 q (x.b + y.b) = (zpow2 p x.a * zpow2 q x.b) * (zpow2 p y.a * zpow2 q y.b)
  rw [h1, h2]
  calc zpow2 p x.a * zpow2 p y.a * (zpow2 q x.b * zpow2 q y.b)
      = zpow2 p x.a * (zpow2 p y.a * zpow2 q x.b) * zpow2 q y.b := by simp only [mul_assoc]
    _ = zpow2 p x.a * (zpow2 q x.b * zpow2 p y.a) * zpow2 q y.b := by rw [hc]
    _ = _ := by simp only [mul_assoc]

theorem pairp_commute {p q p' q' : G} (hpp : Commute p p') (hpq : Commute p q') (hqp : Commute q p')
    (hqq : Commute q q') (x y : F4c) : Commute (pairp p q x) (pairp p' q' y) := by
  unfold pairp
  exact ((commute_zpow2 hpp _ _).mul_right (commute_zpow2 hpq _ _)).mul_left
    ((commute_zpow2 hqp _ _).mul_right (commute_zpow2 hqq _ _))

end Pair

section Generic

theorem sign_Sfun (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) (x : UT3 F4c) : Perm.sign (Sfun m x) = 1 := by
  revert x
  interval_cases m <;> decide +kernel

theorem zpow2_of_one_elt {G : Type*} [Group G] (a : ZMod 2) : zpow2 (1 : G) a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [zpow2_zero, zpow2_one]

variable {H : Type} [Group H] {K : Subgroup H} {n : ℕ} {R : PermRep K n}

theorem rho_zpow2 (g : H) (a : ZMod 2) : R.ρ (zpow2 g a) = zpow2 (R.ρ g) a := by
  rcases zmod2_cases a with rfl | rfl
  · rw [zpow2_zero, zpow2_zero, map_one]
  · rw [zpow2_one, zpow2_one]

theorem rho_pairp (p q : H) (x : F4c) : R.ρ (pairp p q x) = pairp (R.ρ p) (R.ρ q) x := by
  unfold pairp
  rw [map_mul, rho_zpow2, rho_zpow2]

end Generic

section Lifts

variable {H : Type} [Group H] {K : Subgroup H} {m : ℕ} {R : PermRep K (m + 1)} {z : H}

structure Lifts (R : PermRep K (m + 1)) where
  u : H
  v : H
  x1 : H
  x2 : H
  g : H
  c : H
  hu : R.ρ u = ub m
  hv : R.ρ v = vb m
  hx1 : R.ρ x1 = xb1 m
  hx2 : R.ρ x2 = xb2 m
  hg : R.ρ g = sg m
  hc : R.ρ c = c3 m
  hc3 : c ^ 3 = 1

theorem sign_c3 (m : ℕ) (h7 : 7 ≤ m) (h10 : m ≤ 10) : Perm.sign (c3 m) = 1 := by
  have h : Perm.sign (c3 m) ^ 3 = 1 := by
    rw [← map_pow, c3_cube m h7 h10]; simp
  rcases Int.units_eq_one_or (Perm.sign (c3 m)) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem exists_lifts (hz : R.KerData z) (h7 : 7 ≤ m) (h10 : m ≤ 10) : Nonempty (Lifts R) := by
  obtain ⟨u, hu⟩ := R.lift_even (PermRep.sign_eq_one_of_cycleType_two_two_two_two (ct_ub m h7 h10))
  obtain ⟨v, hv⟩ := R.lift_even (PermRep.sign_eq_one_of_cycleType_two_two_two_two (ct_vb m h7 h10))
  obtain ⟨x1, hx1⟩ := R.lift_even (PermRep.sign_eq_one_of_cycleType_two_two_two_two (ct_xb1 m h7 h10))
  obtain ⟨x2, hx2⟩ := R.lift_even (PermRep.sign_eq_one_of_cycleType_two_two_two_two (ct_xb2 m h7 h10))
  obtain ⟨g, hg⟩ := R.lift_even (PermRep.sign_eq_one_of_cycleType_two_two (ct_sg m h7 h10))
  obtain ⟨c, hc, hc3⟩ := exists_lift_pow_three hz (c3_cube m h7 h10) (sign_c3 m h7 h10)
  exact ⟨⟨u, v, x1, x2, g, c, hu, hv, hx1, hx2, hg, hc, hc3⟩⟩

theorem comm_mul_z (hz : R.KerData z) (a b : H) : a * z * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [← hz.central b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_z' (hz : R.KerData z) (a b : H) : a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [← hz.central a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

namespace Lifts

variable (L : Lifts R) (hz : R.KerData z) (h7 : 7 ≤ m) (h10 : m ≤ 10)

section G1

include h7 h10

theorem rsq_u : R.ρ L.u * R.ρ L.u = 1 := by rw [L.hu]; exact sq_ub m h7 h10
theorem rsq_v : R.ρ L.v * R.ρ L.v = 1 := by rw [L.hv]; exact sq_vb m h7 h10
theorem rsq_x1 : R.ρ L.x1 * R.ρ L.x1 = 1 := by rw [L.hx1]; exact sq_xb1 m h7 h10
theorem rsq_x2 : R.ρ L.x2 * R.ρ L.x2 = 1 := by rw [L.hx2]; exact sq_xb2 m h7 h10
theorem rsq_g : R.ρ L.g * R.ρ L.g = 1 := by rw [L.hg]; exact sq_sg m h7 h10

theorem sq_u : L.u * L.u = 1 :=
  PermRep.sq_four (R := R) (by omega) (by rw [L.hu]; exact ct_ub m h7 h10)
theorem sq_v : L.v * L.v = 1 :=
  PermRep.sq_four (R := R) (by omega) (by rw [L.hv]; exact ct_vb m h7 h10)
theorem sq_x1 : L.x1 * L.x1 = 1 :=
  PermRep.sq_four (R := R) (by omega) (by rw [L.hx1]; exact ct_xb1 m h7 h10)
theorem sq_x2 : L.x2 * L.x2 = 1 :=
  PermRep.sq_four (R := R) (by omega) (by rw [L.hx2]; exact ct_xb2 m h7 h10)

@[expose] def t : H := L.u * L.x1 * L.u⁻¹ * L.x1⁻¹

theorem rho_t : R.ρ L.t = tb m := by
  simp only [t, map_mul, map_inv, L.hu, L.hx1]
  exact comm_ub_xb1 m h7 h10

theorem rsq_t : R.ρ L.t * R.ρ L.t = 1 := by rw [L.rho_t h7 h10]; exact sq_tb m h7 h10

theorem sq_t : L.t * L.t = 1 :=
  PermRep.sq_four (R := R) (by omega) (by rw [L.rho_t h7 h10]; exact ct_tb m h7 h10)

end G1

section G2

include hz h7 h10

theorem sq_g : L.g * L.g = z := hz.sq_double (by omega) (by rw [L.hg]; exact ct_sg m h7 h10)

theorem comm_uv : L.u * L.v = L.v * L.u :=
  commute_of_squares_one hz (L.rsq_u h7 h10) (L.rsq_v h7 h10)
    (by rw [L.hu, L.hv]; exact comm_ub_vb m h7 h10) (L.sq_u h7 h10) (L.sq_v h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.hu, L.hv]; exact ct_ub_vb m h7 h10))

theorem comm_x12 : L.x1 * L.x2 = L.x2 * L.x1 :=
  commute_of_squares_one hz (L.rsq_x1 h7 h10) (L.rsq_x2 h7 h10)
    (by rw [L.hx1, L.hx2]; exact comm_xb1_xb2 m h7 h10) (L.sq_x1 h7 h10) (L.sq_x2 h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.hx1, L.hx2]; exact ct_xb1_xb2 m h7 h10))

theorem comm_ux2 : L.u * L.x2 * L.u⁻¹ * L.x2⁻¹ = z := by
  have h := comm_of_squares hz (L.rsq_u h7 h10) (L.rsq_x2 h7 h10)
    (by rw [L.hu, L.hx2]; exact comm_ub_xb2 m h7 h10) (L.sq_u h7 h10) (L.sq_x2 h7 h10)
    (hz.sq_double (by omega) (by rw [map_mul, L.hu, L.hx2]; exact ct_ub_xb2 m h7 h10))
  simpa using h

theorem comm_vx1 : L.v * L.x1 * L.v⁻¹ * L.x1⁻¹ = z := by
  have h := comm_of_squares hz (L.rsq_v h7 h10) (L.rsq_x1 h7 h10)
    (by rw [L.hv, L.hx1]; exact comm_vb_xb1 m h7 h10) (L.sq_v h7 h10) (L.sq_x1 h7 h10)
    (hz.sq_double (by omega) (by rw [map_mul, L.hv, L.hx1]; exact ct_vb_xb1 m h7 h10))
  simpa using h

theorem comm_tu : L.t * L.u = L.u * L.t :=
  commute_of_squares_one hz (L.rsq_t h7 h10) (L.rsq_u h7 h10)
    (by rw [L.rho_t h7 h10, L.hu]; exact comm_tb_ub m h7 h10) (L.sq_t h7 h10) (L.sq_u h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.rho_t h7 h10, L.hu]; exact ct_tb_ub m h7 h10))

theorem comm_tv : L.t * L.v = L.v * L.t :=
  commute_of_squares_one hz (L.rsq_t h7 h10) (L.rsq_v h7 h10)
    (by rw [L.rho_t h7 h10, L.hv]; exact comm_tb_vb m h7 h10) (L.sq_t h7 h10) (L.sq_v h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.rho_t h7 h10, L.hv]; exact ct_tb_vb m h7 h10))

theorem comm_tx1 : L.t * L.x1 = L.x1 * L.t :=
  commute_of_squares_one hz (L.rsq_t h7 h10) (L.rsq_x1 h7 h10)
    (by rw [L.rho_t h7 h10, L.hx1]; exact comm_tb_xb1 m h7 h10) (L.sq_t h7 h10) (L.sq_x1 h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.rho_t h7 h10, L.hx1]; exact ct_tb_xb1 m h7 h10))

theorem comm_tx2 : L.t * L.x2 = L.x2 * L.t :=
  commute_of_squares_one hz (L.rsq_t h7 h10) (L.rsq_x2 h7 h10)
    (by rw [L.rho_t h7 h10, L.hx2]; exact comm_tb_xb2 m h7 h10) (L.sq_t h7 h10) (L.sq_x2 h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.rho_t h7 h10, L.hx2]; exact ct_tb_xb2 m h7 h10))

theorem conj_g_t : L.g * L.t * L.g⁻¹ = L.t * z := by
  have h := comm_of_squares hz (L.rsq_g h7 h10) (L.rsq_t h7 h10)
    (by rw [L.hg, L.rho_t h7 h10]; exact comm_sg_tb m h7 h10) (L.sq_g hz h7 h10) (L.sq_t h7 h10)
    (PermRep.sq_four (R := R) (by omega) (by rw [map_mul, L.hg, L.rho_t h7 h10]; exact ct_sg_tb m h7 h10))
  calc L.g * L.t * L.g⁻¹ = (L.g * L.t * L.g⁻¹ * L.t⁻¹) * L.t := by group
    _ = z * 1 * 1 * L.t := by rw [h]
    _ = L.t * z := by rw [mul_one, mul_one]; exact (hz.central L.t).symm

theorem comm_vx2 : L.v * L.x2 * L.v⁻¹ * L.x2⁻¹ = L.t * z := by
  have hgu : L.g * L.u * L.g⁻¹ = L.v ∨ L.g * L.u * L.g⁻¹ = L.v * z :=
    conj_mem_ker hz (by rw [map_mul, map_mul, map_inv, L.hg, L.hu, L.hv]; exact sg_ub m h7 h10)
  have hgx : L.g * L.x1 * L.g⁻¹ = L.x2 ∨ L.g * L.x1 * L.g⁻¹ = L.x2 * z :=
    conj_mem_ker hz (by rw [map_mul, map_mul, map_inv, L.hg, L.hx1, L.hx2]; exact sg_xb1 m h7 h10)
  have hconj : L.g * L.t * L.g⁻¹ = (L.g * L.u * L.g⁻¹) * (L.g * L.x1 * L.g⁻¹) * (L.g * L.u * L.g⁻¹)⁻¹ *
      (L.g * L.x1 * L.g⁻¹)⁻¹ := by
    simp only [t]; group
  rw [L.conj_g_t hz h7 h10] at hconj
  rcases hgu with h1 | h1 <;> rcases hgx with h2 | h2 <;> rw [h1, h2] at hconj
  · exact hconj.symm
  · rw [comm_mul_z' hz] at hconj; exact hconj.symm
  · rw [comm_mul_z hz] at hconj; exact hconj.symm
  · rw [comm_mul_z hz, comm_mul_z' hz] at hconj; exact hconj.symm

end G2

section Heis

include hz h7 h10
@[expose] def heis : HeisData H :=
  HeisData.ofBasis (pairp L.u L.v) (pairp L.x1 L.x2) (pairp L.t z)
    (pairp_add (L.sq_u h7 h10) (L.sq_v h7 h10) (L.comm_uv hz h7 h10))
    (pairp_add (L.sq_x1 h7 h10) (L.sq_x2 h7 h10) (L.comm_x12 hz h7 h10))
    (pairp_add (L.sq_t h7 h10) hz.sq (hz.central L.t))
    (fun c a => (pairp_commute (L.comm_tu hz h7 h10) (L.comm_tv hz h7 h10)
      (hz.central L.u).symm (hz.central L.v).symm c a).eq)
    (fun c b => (pairp_commute (L.comm_tx1 hz h7 h10) (L.comm_tx2 hz h7 h10)
      (hz.central L.x1).symm (hz.central L.x2).symm c b).eq)
    (by
      rw [one_mul, pairp_one, pairp_one, pairp_one]
      calc L.u * L.x1 = (L.u * L.x1 * L.u⁻¹ * L.x1⁻¹) * (L.x1 * L.u) := by group
        _ = L.t * (L.x1 * L.u) := rfl)
    (by
      rw [one_mul, pairp_one, pairp_omega, pairp_omega]
      calc L.u * L.x2 = (L.u * L.x2 * L.u⁻¹ * L.x2⁻¹) * (L.x2 * L.u) := by group
        _ = z * (L.x2 * L.u) := by rw [L.comm_ux2 hz h7 h10])
    (by
      rw [mul_one, pairp_one, pairp_omega, pairp_omega]
      calc L.v * L.x1 = (L.v * L.x1 * L.v⁻¹ * L.x1⁻¹) * (L.x1 * L.v) := by group
        _ = z * (L.x1 * L.v) := by rw [L.comm_vx1 hz h7 h10])
    (by
      rw [F4c_mul_cases, pairp_one_omega, pairp_omega, pairp_omega]
      calc L.v * L.x2 = (L.v * L.x2 * L.v⁻¹ * L.x2⁻¹) * (L.x2 * L.v) := by group
        _ = L.t * z * (L.x2 * L.v) := by rw [L.comm_vx2 hz h7 h10])
@[expose] def psi : UT3 F4c →* H := (L.heis hz h7 h10).hom

theorem psi_apply (x : UT3 F4c) :
    L.psi hz h7 h10 x = pairp L.x1 L.x2 x.b * pairp L.u L.v x.a * pairp L.t z x.c := rfl


theorem rho_psi (x : UT3 F4c) : R.ρ (L.psi hz h7 h10 x) = Sfun m x := by
  rw [psi_apply, map_mul, map_mul, rho_pairp, rho_pairp, rho_pairp, L.hx1, L.hx2, L.hu, L.hv,
    L.rho_t h7 h10, hz.ρ_z]
  simp only [Sfun, sbar, rbar, wbar, pairp, zpow2_of_one_elt, mul_one]

theorem psi_mem_K (x : UT3 F4c) : L.psi hz h7 h10 x ∈ K :=
  R.mem_K_of_sign _ (by rw [L.rho_psi hz h7 h10]; exact sign_Sfun m h7 h10 x)

theorem psi_omega : L.psi hz h7 h10 ⟨0, 0, omegaC⟩ = z := by
  rw [psi_apply]
  show pairp L.x1 L.x2 (0 : F4c) * pairp L.u L.v (0 : F4c) * pairp L.t z omegaC = z
  rw [pairp_zero, pairp_zero, pairp_omega, one_mul, one_mul]

theorem psi_injective : Function.Injective (L.psi hz h7 h10) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : Sfun m x = 1 := by rw [← L.rho_psi hz h7 h10 x, hx, map_one]
  rcases Sfun_ker m h7 h10 x h1 with h | h
  · exact h
  · exfalso
    rw [h, L.psi_omega hz h7 h10] at hx
    exact hz.ne_one hx

theorem card_psi_range : Nat.card (L.psi hz h7 h10).range = 64 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (L.psi_injective hz h7 h10)).toEquiv.symm]
  exact card_UT3c

theorem z_mem_range : z ∈ (L.psi hz h7 h10).range := ⟨⟨0, 0, omegaC⟩, L.psi_omega hz h7 h10⟩

theorem mem_range_of_rho (y : H) (x : UT3 F4c) (h : R.ρ y = Sfun m x) :
    y ∈ (L.psi hz h7 h10).range := by
  have hker : R.ρ ((L.psi hz h7 h10 x)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, L.rho_psi hz h7 h10, h, inv_mul_cancel]
  rcases hz.ker _ hker with h1 | h1
  · have : y = L.psi hz h7 h10 x := by
      calc y = L.psi hz h7 h10 x * ((L.psi hz h7 h10 x)⁻¹ * y) := by group
        _ = L.psi hz h7 h10 x := by rw [h1, mul_one]
    rw [this]
    exact ⟨x, rfl⟩
  · have : y = L.psi hz h7 h10 x * z := by
      calc y = L.psi hz h7 h10 x * ((L.psi hz h7 h10 x)⁻¹ * y) := by group
        _ = L.psi hz h7 h10 x * z := by rw [h1]
    rw [this]
    exact Subgroup.mul_mem _ ⟨x, rfl⟩ (L.z_mem_range hz h7 h10)

end Heis

end Lifts

end Lifts

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
