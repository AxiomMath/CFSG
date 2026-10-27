module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
public import CFSG.GH74.Uniqueness.SU.SU13TA3Perm

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L10

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA

variable {H : Type} [Group H]

structure Cfg (π : H →* alternatingGroup (Fin 10)) where
  s₁ : H
  s₂ : H
  s₃ : H
  t : H
  π_s₁ : π s₁ = ec
  π_s₂ : π s₂ = ea * eb
  π_s₃ : π s₃ = ea * eb * ec
  π_t : π t = et
  s₁_pow : s₁ ^ 3 = 1
  s₂_pow : s₂ ^ 3 = 1
  s₃_pow : s₃ ^ 3 = 1
  t_sq : t ^ 2 = 1

theorem cycleType_of_pow_three_eq_one {σ : alternatingGroup (Fin 10)} (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) :
    (σ : Perm (Fin 10)).cycleType = {3} ∨ (σ : Perm (Fin 10)).cycleType = {3, 3} ∨
      (σ : Perm (Fin 10)).cycleType = {3, 3, 3} := by
  have h3' : (σ : Perm (Fin 10)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3, OneMemClass.coe_one]
  have h1' : (σ : Perm (Fin 10)) ≠ 1 := fun h => h1 (Subtype.ext h)
  obtain ⟨k, hk⟩ : ∃ k, (σ : Perm (Fin 10)).cycleType = Multiset.replicate k 3 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one h3'⟩
  have hsum := Perm.sum_cycleType_le (σ : Perm (Fin 10))
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

variable {π : H →* alternatingGroup (Fin 10)}

theorem _root_.CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover.nonempty_cfg (hπ : TwoCover π) :
    Nonempty (Cfg π) := by
  obtain ⟨s₁, ⟨h1, h1'⟩, -⟩ := hπ.existsUnique_lift_pow_three ec ec_pow_three
  have h2c : (ea * eb) ^ 3 = 1 := by
    rw [commute_ea_eb.mul_pow, ea_pow_three, eb_pow_three, one_mul]
  have h3c : (ea * eb * ec) ^ 3 = 1 := by
    rw [(commute_ea_ec.mul_left commute_eb_ec).mul_pow, h2c, ec_pow_three, one_mul]
  obtain ⟨s₂, ⟨h2, h2'⟩, -⟩ := hπ.existsUnique_lift_pow_three (ea * eb) h2c
  obtain ⟨s₃, ⟨h3, h3'⟩, -⟩ := hπ.existsUnique_lift_pow_three (ea * eb * ec) h3c
  obtain ⟨t, ht⟩ := hπ.surj et
  have htsq : t ^ 2 = 1 :=
    hπ.sq_eq_one_of_cycleType_two_two_two_two (by norm_num) (by rw [ht]; exact cycleType_et)
  exact ⟨⟨s₁, s₂, s₃, t, h1, h2, h3, ht, h1', h2', h3', htsq⟩⟩

theorem et_ne_one : et ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 10) => (x : Perm (Fin 10))) h
  revert this
  decide

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

end CFSG.GH74.Uniqueness.SU.SU13.TA.L10
