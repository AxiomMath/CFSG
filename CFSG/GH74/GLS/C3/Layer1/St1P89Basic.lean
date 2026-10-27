module

public import CFSG.GH74.GLS.C3.Layer1.St1P89Cfg

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

section Conj

variable {G : Type} [Group G]

@[expose] def conjSub (a : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj a).toMonoidHom

theorem mem_conjSub {a : G} {H : Subgroup G} {g : G} : g ∈ conjSub a H ↔ ∃ h ∈ H, g = a * h * a⁻¹ := by
  unfold conjSub
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩

theorem card_conjSub (a : G) (H : Subgroup G) : Nat.card ↥(conjSub a H) = Nat.card ↥H := by
  unfold conjSub
  exact Subgroup.card_map_of_injective (MulAut.conj a).injective

theorem conj_mem_conjSub {a : G} {H : Subgroup G} {h : G} (hh : h ∈ H) : a * h * a⁻¹ ∈ conjSub a H :=
  mem_conjSub.mpr ⟨h, hh, rfl⟩

end Conj

section Basic

variable {G : Type} [Group G] [Finite G] {T P Q : Subgroup G} {u z x f r s : G}

theorem Cfg89T.z_sq (c : Cfg89T G T P Q u z x f r s) : z ^ 2 = 1 := by
  rw [c.z_eq, ← pow_mul]; exact c.r4

theorem Cfg89T.z_ne_one (c : Cfg89T G T P Q u z x f r s) : z ≠ 1 := by
  rw [c.z_eq]; exact c.r2_ne

theorem Cfg89T.z_mem (c : Cfg89T G T P Q u z x f r s) : z ∈ P := by
  rw [c.z_eq]; exact P.pow_mem c.r_mem 2

theorem Cfg89T.u_ne_z (c : Cfg89T G T P Q u z x f r s) : u ≠ z := fun h =>
  c.u_ne (c.PQ_inf u (h ▸ c.z_mem) c.u_mem)

theorem Cfg89T.r_inv (c : Cfg89T G T P Q u z x f r s) : r⁻¹ = r ^ 3 := by
  have : r * r ^ 3 = 1 := by rw [← pow_succ']; exact c.r4
  exact inv_eq_of_mul_eq_one_right this

theorem Cfg89T.s_r (c : Cfg89T G T P Q u z x f r s) : s * r = r ^ 3 * s := by
  have h := c.srs
  rw [c.r_inv] at h
  calc s * r = (s * r * s⁻¹) * s := by group
    _ = r ^ 3 * s := by rw [h]

theorem Cfg89T.z_comm_s (c : Cfg89T G T P Q u z x f r s) : z * s = s * z := by
  have h1 : s * r ^ 2 * s⁻¹ = r ^ 2 := by
    have : s * r ^ 2 * s⁻¹ = (s * r * s⁻¹) ^ 2 := (conj_pow).symm
    rw [this, c.srs, c.r_inv]
    calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
      _ = r ^ 2 := by rw [c.r4, one_mul]
  rw [mul_inv_eq_iff_eq_mul] at h1
  rw [c.z_eq]; exact h1.symm

theorem Cfg89T.z_comm_P (c : Cfg89T G T P Q u z x f r s) : ∀ p ∈ P, z * p = p * z := by
  intro p hp
  obtain ⟨i, j, rfl⟩ := c.P_gen p hp
  have hr : z * r = r * z := by rw [c.z_eq]; group
  have hs := c.z_comm_s
  have hri : z * r ^ i = r ^ i * z := (Commute.pow_right (show Commute z r from hr) i).eq
  have hsj : z * s ^ j = s ^ j * z := (Commute.pow_right (show Commute z s from hs) j).eq
  calc z * (r ^ i * s ^ j) = (z * r ^ i) * s ^ j := by group
    _ = (r ^ i * z) * s ^ j := by rw [hri]
    _ = r ^ i * (z * s ^ j) := by group
    _ = r ^ i * (s ^ j * z) := by rw [hsj]
    _ = r ^ i * s ^ j * z := by group

theorem Cfg89T.z_central (c : Cfg89T G T P Q u z x f r s) : ∀ t ∈ T, t * z = z * t := by
  intro t ht
  obtain ⟨p, hp, q, hq, i, j, rfl⟩ := c.T_gen t ht
  have hzP := c.z_comm_P
  have hzq : z * q = q * z := c.PQ_comm z c.z_mem q hq
  have hzf : f * z = z * f := c.f_cent z c.z_mem
  have hzx : x * z * x⁻¹ = z := by
    have : x * z * x⁻¹ = (x * r * x⁻¹) ^ 2 := by rw [c.z_eq]; exact (conj_pow).symm
    rw [this, c.x_r, c.r_inv, c.z_eq]
    calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
      _ = r ^ 2 := by rw [c.r4, one_mul]
  have hzx' : x * z = z * x := by rw [mul_inv_eq_iff_eq_mul] at hzx; exact hzx
  have hzfi : f ^ i * z = z * f ^ i := (Commute.pow_left (show Commute f z from hzf) i).eq
  have hzxj : x ^ j * z = z * x ^ j := (Commute.pow_left (show Commute x z from hzx') j).eq
  calc p * q * f ^ i * x ^ j * z = p * q * f ^ i * (x ^ j * z) := by group
    _ = p * q * f ^ i * (z * x ^ j) := by rw [hzxj]
    _ = p * q * (f ^ i * z) * x ^ j := by group
    _ = p * q * (z * f ^ i) * x ^ j := by rw [hzfi]
    _ = p * (q * z) * f ^ i * x ^ j := by group
    _ = p * (z * q) * f ^ i * x ^ j := by rw [hzq]
    _ = (p * z) * q * f ^ i * x ^ j := by group
    _ = (z * p) * q * f ^ i * x ^ j := by rw [(hzP p hp).symm]
    _ = z * (p * q * f ^ i * x ^ j) := by group

theorem Cfg89T.T_two (c : Cfg89T G T P Q u z x f r s) : IsPGroup 2 ↥T := c.sylowT.isPGroup

end Basic

end CFSG.GH74.GLS.C3.Layer1.P89
