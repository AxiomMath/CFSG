module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.GH74.Uniqueness.SU.SU13TA9Perm

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H]

structure Cfg (π : H →* alternatingGroup (Fin 9)) where
  s₁ : H
  s₂ : H
  s₃ : H
  s₄ : H
  t : H
  x : H
  π_s₁ : π s₁ = ec
  π_s₂ : π s₂ = ea * eb
  π_s₃ : π s₃ = ea * eb * ec
  π_s₄ : π s₄ = ea * eb⁻¹
  π_t : π t = et
  π_x : π x = ex
  s₁_pow : s₁ ^ 3 = 1
  s₂_pow : s₂ ^ 3 = 1
  s₃_pow : s₃ ^ 3 = 1
  s₄_pow : s₄ ^ 3 = 1
  t_sq : t ^ 2 = 1
  x_sq : x ^ 2 = 1

theorem cycleType_of_pow_three_eq_one {σ : alternatingGroup (Fin 9)} (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) :
    (σ : Perm (Fin 9)).cycleType = {3} ∨ (σ : Perm (Fin 9)).cycleType = {3, 3} ∨
      (σ : Perm (Fin 9)).cycleType = {3, 3, 3} := by
  have h3' : (σ : Perm (Fin 9)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3, OneMemClass.coe_one]
  have h1' : (σ : Perm (Fin 9)) ≠ 1 := fun h => h1 (Subtype.ext h)
  obtain ⟨k, hk⟩ : ∃ k, (σ : Perm (Fin 9)).cycleType = Multiset.replicate k 3 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one h3'⟩
  have hsum := Perm.sum_cycleType_le (σ : Perm (Fin 9))
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h1' (Perm.cycleType_eq_zero.mp hk)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  have hk3 : k ≤ 3 := by omega
  rw [hk]
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

variable {π : H →* alternatingGroup (Fin 9)}

theorem ea_mul_eb_inv_pow_three : (ea * eb⁻¹) ^ 3 = 1 := by
  rw [commute_ea_eb.inv_right.mul_pow, ea_pow_three, inv_pow, eb_pow_three, inv_one, one_mul]

theorem ea_mul_eb_ne_one : ea * eb ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  revert this
  decide

theorem ea_mul_eb_mul_ec_ne_one : ea * eb * ec ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  revert this
  decide

theorem ea_mul_eb_inv_ne_one : ea * eb⁻¹ ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  revert this
  decide

theorem et_ne_one : et ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  revert this
  decide

theorem ex_ne_one : ex ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  revert this
  decide

theorem _root_.CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover.nonempty_cfg9 (hπ : TwoCover π) :
    Nonempty (Cfg π) := by
  obtain ⟨s₁, ⟨h1, h1'⟩, -⟩ := hπ.existsUnique_lift_pow_three ec ec_pow_three
  have h2c : (ea * eb) ^ 3 = 1 := by
    rw [commute_ea_eb.mul_pow, ea_pow_three, eb_pow_three, one_mul]
  have h3c : (ea * eb * ec) ^ 3 = 1 := by
    rw [(commute_ea_ec.mul_left commute_eb_ec).mul_pow, h2c, ec_pow_three, one_mul]
  obtain ⟨s₂, ⟨h2, h2'⟩, -⟩ := hπ.existsUnique_lift_pow_three (ea * eb) h2c
  obtain ⟨s₃, ⟨h3, h3'⟩, -⟩ := hπ.existsUnique_lift_pow_three (ea * eb * ec) h3c
  obtain ⟨s₄, ⟨h4, h4'⟩, -⟩ := hπ.existsUnique_lift_pow_three (ea * eb⁻¹) ea_mul_eb_inv_pow_three
  obtain ⟨t, ht⟩ := hπ.surj et
  obtain ⟨x, hx⟩ := hπ.surj ex
  have htsq : t ^ 2 = 1 :=
    hπ.sq_eq_one_of_cycleType_two_two_two_two (by norm_num) (by rw [ht]; exact cycleType_et)
  have hxsq : x ^ 2 = 1 :=
    hπ.sq_eq_one_of_cycleType_two_two_two_two (by norm_num) (by rw [hx]; exact cycleType_ex)
  exact ⟨⟨s₁, s₂, s₃, s₄, t, x, h1, h2, h3, h4, ht, hx, h1', h2', h3', h4', htsq, hxsq⟩⟩

theorem eq_of_pow_three_of_map_eq (hπ : TwoCover π) {σ : alternatingGroup (Fin 9)}
    (hσ : σ ^ 3 = 1) {x y : H} (hx : π x = σ) (hx3 : x ^ 3 = 1) (hy : π y = σ)
    (hy3 : y ^ 3 = 1) : x = y :=
  (hπ.existsUnique_lift_pow_three σ hσ).unique ⟨hx, hx3⟩ ⟨hy, hy3⟩

theorem conj_pow_three {x t : H} (hx : x ^ 3 = 1) : (t * x * t⁻¹) ^ 3 = 1 := by
  rw [conj_pow, hx, mul_one, mul_inv_cancel]

theorem conj_eq_of_pow_three (hπ : TwoCover π) {w u v : H} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1)
    (h : π w * π u * (π w)⁻¹ = π v) : w * u * w⁻¹ = v :=
  eq_of_pow_three_of_map_eq hπ (σ := π v) (by rw [← map_pow, hv, map_one])
    (by rw [map_mul, map_mul, map_inv]; exact h) (conj_pow_three hu) rfl hv

theorem Cfg.isConj_of_pow_three (hπ : TwoCover π) (c : Cfg π) {u : H} (h3 : u ^ 3 = 1)
    (h1 : u ≠ 1) : IsConj u c.s₁ ∨ IsConj u c.s₂ ∨ IsConj u c.s₃ := by
  have hπu : π u ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hπ1 : π u ≠ 1 := fun h => h1 (by
    have hk : u ∈ π.ker := h
    have h2 := hπ.sq_eq_one_of_mem_ker' hk
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul])
  rcases cycleType_of_pow_three_eq_one hπu hπ1 with h | h | h
  · left
    exact hπ.isConj_of_pow_three_of_isConj h3 c.s₁_pow (by
      rw [c.π_s₁]
      exact isConj_alternatingGroup_of_cycleType_eq (by norm_num) (c := {3}) (Or.inl rfl) h
        cycleType_ec)
  · right; left
    exact hπ.isConj_of_pow_three_of_isConj h3 c.s₂_pow (by
      rw [c.π_s₂]
      exact isConj_alternatingGroup_of_cycleType_eq (by norm_num) (c := {3, 3})
        (Or.inr (Or.inl rfl)) h cycleType_ea_mul_eb)
  · right; right
    exact hπ.isConj_of_pow_three_of_isConj h3 c.s₃_pow (by
      rw [c.π_s₃]
      exact isConj_alternatingGroup_of_cycleType_eq (by norm_num) (c := {3, 3, 3})
        (Or.inr (Or.inr (Or.inl rfl))) h cycleType_ea_mul_eb_mul_ec)

theorem Cfg.t_mul_s₂ (hπ : TwoCover π) (c : Cfg π) : c.t * c.s₂ * c.t⁻¹ = c.s₂ :=
  conj_eq_of_pow_three hπ c.s₂_pow c.s₂_pow (by
    rw [c.π_t, c.π_s₂]
    calc et * (ea * eb) * et⁻¹ = (et * ea * et⁻¹) * (et * eb * et⁻¹) := by group
      _ = ea * eb := by rw [et_mul_ea, et_mul_eb, commute_ea_eb.eq])

theorem Cfg.t_mul_s₁ (hπ : TwoCover π) (c : Cfg π) : c.t * c.s₁ * c.t⁻¹ = c.s₁⁻¹ :=
  conj_eq_of_pow_three hπ c.s₁_pow (by rw [inv_pow, c.s₁_pow, inv_one]) (by
    rw [c.π_t, c.π_s₁, map_inv, c.π_s₁, et_mul_ec])

theorem Cfg.t_mul_s₄ (hπ : TwoCover π) (c : Cfg π) : c.t * c.s₄ * c.t⁻¹ = c.s₄⁻¹ :=
  conj_eq_of_pow_three hπ c.s₄_pow (by rw [inv_pow, c.s₄_pow, inv_one]) (by
    rw [c.π_t, c.π_s₄, map_inv, c.π_s₄]
    calc et * (ea * eb⁻¹) * et⁻¹ = (et * ea * et⁻¹) * (et * eb * et⁻¹)⁻¹ := by group
      _ = (ea * eb⁻¹)⁻¹ := by rw [et_mul_ea, et_mul_eb]; group)

theorem Cfg.x_mul_s₁ (hπ : TwoCover π) (c : Cfg π) : c.x * c.s₁ * c.x⁻¹ = c.s₁⁻¹ :=
  conj_eq_of_pow_three hπ c.s₁_pow (by rw [inv_pow, c.s₁_pow, inv_one]) (by
    rw [c.π_x, c.π_s₁, map_inv, c.π_s₁, ex_mul_ec])

theorem Cfg.x_mul_s₂ (hπ : TwoCover π) (c : Cfg π) : c.x * c.s₂ * c.x⁻¹ = c.s₂⁻¹ :=
  conj_eq_of_pow_three hπ c.s₂_pow (by rw [inv_pow, c.s₂_pow, inv_one]) (by
    rw [c.π_x, c.π_s₂, map_inv, c.π_s₂]
    calc ex * (ea * eb) * ex⁻¹ = (ex * ea * ex⁻¹) * (ex * eb * ex⁻¹) := by group
      _ = eb⁻¹ * ea⁻¹ := by rw [ex_mul_ea, ex_mul_eb]
      _ = (ea * eb)⁻¹ := (mul_inv_rev ea eb).symm)

theorem Cfg.x_mul_s₄ (hπ : TwoCover π) (c : Cfg π) : c.x * c.s₄ * c.x⁻¹ = c.s₄ :=
  conj_eq_of_pow_three hπ c.s₄_pow c.s₄_pow (by
    rw [c.π_x, c.π_s₄]
    calc ex * (ea * eb⁻¹) * ex⁻¹ = (ex * ea * ex⁻¹) * (ex * eb * ex⁻¹)⁻¹ := by group
      _ = eb⁻¹ * ea := by rw [ex_mul_ea, ex_mul_eb, inv_inv]
      _ = ea * eb⁻¹ := commute_ea_eb.inv_right.eq.symm)

theorem Cfg.tx_sq (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    (c.t * c.x) ^ 2 = z := by
  obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) (x := c.t * c.x)
    (by rw [map_mul, c.π_t, c.π_x]; exact cycleType_et_mul_ex)
  exact hπ.eq_of_mem_ker_ne_one' hk hz h1 hz1

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
