module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup

namespace Lemma31iRels

structure Rels {G : Type} [Group G] (n : ℕ) (z t d j d' j' : G) : Prop where
  three_le : 3 ≤ n
  d_ord : orderOf d = 2 ^ (n - 1)
  d'_ord : orderOf d' = 2 ^ (n - 1)
  z_eq : z = d ^ 2 ^ (n - 2)
  z_eq' : z = d' ^ 2 ^ (n - 2)
  jj : j * j = z
  jj' : j' * j' = z
  jdj : j * d * j⁻¹ = d⁻¹
  jdj' : j' * d' * j'⁻¹ = d'⁻¹
  dd' : d * d' = d' * d
  dj' : d * j' = j' * d
  jd' : j * d' = d' * j
  jj'c : j * j' = j' * j
  tt : t * t = 1
  td : t * d * t⁻¹ = d'
  tj : t * j * t⁻¹ = j'
  indep : ∀ k l : ℕ, d ^ k = d' ^ l → d ^ k = 1 ∨ d ^ k = z

section Defs

variable {G : Type} [Group G]

@[expose] def B₁ (d d' j j' t : G) : Subgroup G := zpowers (d * d') ⊔ zpowers (j * j' * t)

@[expose] def B₂ (d d' t : G) : Subgroup G := zpowers (d * d'⁻¹) ⊔ zpowers t

@[expose] def uvec (n : ℕ) (d d' : G) : G := d ^ 2 ^ (n - 3) * d' ^ 2 ^ (n - 3)

end Defs

section Basic

variable {G : Type} [Group G] {n : ℕ} {z t d j d' j' : G}

theorem Rels.d_pow (h : Rels n z t d j d' j') : d ^ 2 ^ (n - 1) = 1 := by
  rw [← h.d_ord]
  exact pow_orderOf_eq_one d

theorem Rels.d'_pow (h : Rels n z t d j d' j') : d' ^ 2 ^ (n - 1) = 1 := by
  rw [← h.d'_ord]
  exact pow_orderOf_eq_one d'

theorem Rels.z_sq (h : Rels n z t d j d' j') : z * z = 1 := by
  have hn := h.three_le
  have : 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp [pow_succ]
    ring
  rw [h.z_eq, ← pow_add, ← this]
  exact h.d_pow

theorem Rels.z_ne_one (h : Rels n z t d j d' j') : z ≠ 1 := by
  intro hz
  have hn := h.three_le
  have h1 : orderOf d ∣ 2 ^ (n - 2) := orderOf_dvd_of_pow_eq_one (by rw [← h.z_eq]; exact hz)
  rw [h.d_ord] at h1
  have h2 := Nat.le_of_dvd (by positivity) h1
  have h3 : 2 ^ (n - 2) < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem Rels.td' (h : Rels n z t d j d' j') : t * d' * t⁻¹ = d := by
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.tt
  rw [← h.td]
  calc t * (t * d * t⁻¹) * t⁻¹ = (t * t) * d * (t * t)⁻¹ := by group
    _ = d := by rw [h.tt]; group

theorem Rels.tj' (h : Rels n z t d j d' j') : t * j' * t⁻¹ = j := by
  rw [← h.tj]
  calc t * (t * j * t⁻¹) * t⁻¹ = (t * t) * j * (t * t)⁻¹ := by group
    _ = j := by rw [h.tt]; group

theorem Rels.z_comm_d (h : Rels n z t d j d' j') : z * d = d * z := by
  rw [h.z_eq]
  exact ((Commute.refl d).pow_left _).eq

theorem Rels.z_comm_d' (h : Rels n z t d j d' j') : z * d' = d' * z := by
  rw [h.z_eq']
  exact ((Commute.refl d').pow_left _).eq

theorem Rels.z_comm_j (h : Rels n z t d j d' j') : z * j = j * z := by
  have hzi : (d ^ 2 ^ (n - 2))⁻¹ = d ^ 2 ^ (n - 2) := by
    rw [← h.z_eq]
    exact inv_eq_of_mul_eq_one_right h.z_sq
  have h1 : j * z * j⁻¹ = z := by
    calc j * z * j⁻¹ = j * d ^ 2 ^ (n - 2) * j⁻¹ := by rw [← h.z_eq]
      _ = (j * d * j⁻¹) ^ 2 ^ (n - 2) := conj_pow.symm
      _ = (d ^ 2 ^ (n - 2))⁻¹ := by rw [h.jdj, inv_pow]
      _ = z := by rw [hzi, ← h.z_eq]
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem Rels.z_comm_j' (h : Rels n z t d j d' j') : z * j' = j' * z := by
  have hzi : (d' ^ 2 ^ (n - 2))⁻¹ = d' ^ 2 ^ (n - 2) := by
    rw [← h.z_eq']
    exact inv_eq_of_mul_eq_one_right h.z_sq
  have h1 : j' * z * j'⁻¹ = z := by
    calc j' * z * j'⁻¹ = j' * d' ^ 2 ^ (n - 2) * j'⁻¹ := by rw [← h.z_eq']
      _ = (j' * d' * j'⁻¹) ^ 2 ^ (n - 2) := conj_pow.symm
      _ = (d' ^ 2 ^ (n - 2))⁻¹ := by rw [h.jdj', inv_pow]
      _ = z := by rw [hzi, ← h.z_eq']
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem Rels.z_comm_t (h : Rels n z t d j d' j') : z * t = t * z := by
  have h1 : t * z * t⁻¹ = z := by
    calc t * z * t⁻¹ = t * d ^ 2 ^ (n - 2) * t⁻¹ := by rw [← h.z_eq]
      _ = (t * d * t⁻¹) ^ 2 ^ (n - 2) := conj_pow.symm
      _ = d' ^ 2 ^ (n - 2) := by rw [h.td]
      _ = z := h.z_eq'.symm
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem Rels.d_ne_d' (h : Rels n z t d j d' j') : d' ≠ d := by
  intro hdd
  have hn := h.three_le
  have h2n : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h.indep 1 1 (by rw [hdd]) with h1 | h1
  · rw [pow_one] at h1
    have : orderOf d = 1 := orderOf_eq_one_iff.mpr h1
    rw [h.d_ord] at this
    omega
  · rw [pow_one] at h1
    have hd1 : d ≠ 1 := fun e => h.z_ne_one (h1 ▸ e)
    have hd2 : d ^ 2 = 1 := by
      rw [sq, h1]
      exact h.z_sq
    have : orderOf d = 2 := orderOf_eq_prime hd2 hd1
    rw [h.d_ord] at this
    omega

end Basic

end Lemma31iRels

end CFSG.GH74.GLS.IVK.Proofs2
