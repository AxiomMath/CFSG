module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Cfg
public import CFSG.GH74.Uniqueness.SU.SU13Data

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 10)}

theorem ea_mul_eb_ne_one : ea * eb ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 10) => (x : Perm (Fin 10))) h
  revert this
  decide

theorem ea_mul_eb_mul_ec_ne_one : ea * eb * ec ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 10) => (x : Perm (Fin 10))) h
  revert this
  decide

theorem eq_of_pow_three_of_map_eq (hπ : TwoCover π) {σ : alternatingGroup (Fin 10)}
    (hσ : σ ^ 3 = 1) {x y : H} (hx : π x = σ) (hx3 : x ^ 3 = 1) (hy : π y = σ)
    (hy3 : y ^ 3 = 1) : x = y :=
  (hπ.existsUnique_lift_pow_three σ hσ).unique ⟨hx, hx3⟩ ⟨hy, hy3⟩

theorem conj_pow_three {x t : H} (hx : x ^ 3 = 1) : (t * x * t⁻¹) ^ 3 = 1 := by
  rw [conj_pow, hx, mul_one, mul_inv_cancel]

@[expose] noncomputable def Cfg.elts (hπ : TwoCover π) (c : Cfg π) {z : H} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    Elts H z where
  s₁ := c.s₁
  s₂ := c.s₂
  s₃ := c.s₃
  t := c.t
  s₁_comm := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) c.s₁
  s₂_comm := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) c.s₂
  s₃_comm := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) c.s₃
  s₁_ord := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₁_pow (fun h => by
    have := c.π_s₁
    rw [h, map_one] at this
    exact ec_ne_one this.symm)
  s₂_ord := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₂_pow (fun h => by
    have := c.π_s₂
    rw [h, map_one] at this
    exact ea_mul_eb_ne_one this.symm)
  s₃_ord := orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) c.s₃_pow (fun h => by
    have := c.π_s₃
    rw [h, map_one] at this
    exact ea_mul_eb_mul_ec_ne_one this.symm)
  t_comm := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz) c.t
  t_ord := orderOf_eq_prime (hp := ⟨Nat.prime_two⟩) c.t_sq (fun h => by
    have := c.π_t
    rw [h, map_one] at this
    exact et_ne_one this.symm)
  t_ne := fun h => by
    have hk : c.t ∈ π.ker := h ▸ hz
    rw [MonoidHom.mem_ker, c.π_t] at hk
    exact et_ne_one hk
  t_s₂ := by
    have hx : c.t * c.s₂ * c.t⁻¹ = c.s₂ := by
      refine eq_of_pow_three_of_map_eq hπ (σ := ea * eb) ?_ ?_ (conj_pow_three c.s₂_pow)
        c.π_s₂ c.s₂_pow
      · rw [commute_ea_eb.mul_pow, ea_pow_three, eb_pow_three, one_mul]
      · rw [map_mul, map_mul, map_inv, c.π_t, c.π_s₂]
        calc et * (ea * eb) * et⁻¹ = (et * ea * et⁻¹) * (et * eb * et⁻¹) := by group
          _ = ea * eb := by rw [et_mul_ea, et_mul_eb, commute_ea_eb.eq]
    exact (mul_inv_eq_iff_eq_mul.mp hx)
  t_s₁ := by
    refine eq_of_pow_three_of_map_eq hπ (σ := ec⁻¹) ?_ ?_ (conj_pow_three c.s₁_pow) ?_ ?_
    · rw [inv_pow, ec_pow_three, inv_one]
    · rw [map_mul, map_mul, map_inv, c.π_t, c.π_s₁, et_mul_ec]
    · rw [map_inv, c.π_s₁]
    · rw [inv_pow, c.s₁_pow, inv_one]
  class3 := fun u _ hu => by
    have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
    have hcen := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
    rcases c.isConj_of_pow_three hπ hu3 hu1 with h | h | h
    · obtain ⟨g, hg⟩ := isConj_iff.mp h
      exact ⟨g, hcen g, Or.inl hg⟩
    · obtain ⟨g, hg⟩ := isConj_iff.mp h
      exact ⟨g, hcen g, Or.inr (Or.inl hg)⟩
    · obtain ⟨g, hg⟩ := isConj_iff.mp h
      exact ⟨g, hcen g, Or.inr (Or.inr hg)⟩
  class2 := fun u v _ _ hu hv huz hvz => by
    have hcen := Subgroup.mem_center_iff.mp (hπ.ker_le_center hz)
    have hnot : ∀ w : H, orderOf w = 2 → w ≠ z → w ∉ π.ker := fun w hw hwz hk => by
      have hw1 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hw; omega
      exact hwz (hπ.eq_of_mem_ker_ne_one' hk hz hw1 hz1)
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (hπ.isConj_of_orderOf_eq_two (by norm_num) (by norm_num) hu hv (hnot u hu huz)
        (hnot v hv hvz))
    exact ⟨g, hcen g, hg⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
