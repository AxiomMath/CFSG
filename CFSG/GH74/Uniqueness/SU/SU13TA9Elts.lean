module

public import CFSG.GH74.Uniqueness.SU.SU13TA9Cfg
public import CFSG.GH74.Uniqueness.SU.SU13Data

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13

variable {H : Type} [Group H] {π : H →* alternatingGroup (Fin 9)}

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
  t_s₂ := mul_inv_eq_iff_eq_mul.mp (c.t_mul_s₂ hπ)
  t_s₁ := c.t_mul_s₁ hπ
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

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
