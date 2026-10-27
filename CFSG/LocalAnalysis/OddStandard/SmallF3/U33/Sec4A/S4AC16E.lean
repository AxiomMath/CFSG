module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16H
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Set.Card

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G]

structure C16KBasis (K : Subgroup G) (z u : G) : Prop where
  z_mem : z ∈ K
  u_mem : u ∈ K
  z_sq : z * z = 1
  u_sq : u * u = 1
  comm : z * u = u * z
  z_ne_one : z ≠ 1
  u_ne_one : u ≠ 1
  z_ne_u : z ≠ u
  mem_iff : ∀ k : G, k ∈ K ↔ k = 1 ∨ k = z ∨ k = u ∨ k = z * u

open Classical in
@[expose] noncomputable def c16cK (z u k : G) : C16K0 :=
  if k = 1 then 0 else if k = z then (1, 0) else if k = u then (0, 1) else (1, 1)

private lemma c16_z_mul_zu {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) :
    z * (z * u) = u := by
  rw [← mul_assoc, hB.z_sq, one_mul]

private lemma c16_u_mul_zu {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) :
    u * (z * u) = z := by
  rw [← mul_assoc, hB.comm.symm, mul_assoc, hB.u_sq, mul_one]

private lemma c16_zu_mul_z {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) :
    (z * u) * z = u := by
  rw [mul_assoc, hB.comm.symm, ← mul_assoc, hB.z_sq, one_mul]

private lemma c16_zu_mul_u {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) :
    (z * u) * u = z := by
  rw [mul_assoc, hB.u_sq, mul_one]

private lemma c16_zu_mul_zu {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) :
    (z * u) * (z * u) = 1 := by
  calc (z * u) * (z * u) = ((z * u) * z) * u := by rw [← mul_assoc]
    _ = u * u := by rw [c16_zu_mul_z hB]
    _ = 1 := hB.u_sq

theorem c16cK_one (z u : G) : c16cK z u 1 = 0 := by
  unfold c16cK
  rw [if_pos rfl]

theorem c16cK_z {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) : c16cK z u z = (1, 0) := by
  unfold c16cK
  rw [if_neg hB.z_ne_one, if_pos rfl]

theorem c16cK_u {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) : c16cK z u u = (0, 1) := by
  unfold c16cK
  rw [if_neg hB.u_ne_one, if_neg (Ne.symm hB.z_ne_u), if_pos rfl]

theorem c16cK_zu {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) :
    c16cK z u (z * u) = (1, 1) := by
  have h1 : z * u ≠ 1 := by
    intro h
    have h' : z * u = z * z := by rw [h, hB.z_sq]
    exact hB.z_ne_u (mul_left_cancel h').symm
  have h2 : z * u ≠ z := by
    intro h
    have h' : z * u = z * 1 := by rw [h, mul_one]
    exact hB.u_ne_one (mul_left_cancel h')
  have h3 : z * u ≠ u := by
    intro h
    have h' : z * u = 1 * u := by rw [h, one_mul]
    exact hB.z_ne_one (mul_right_cancel h')
  unfold c16cK
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem c16cK_eq_zero {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) {k : G} (hk : k ∈ K) :
    c16cK z u k = 0 ↔ k = 1 := by
  constructor
  · intro h
    by_contra hne
    rcases (hB.mem_iff k).mp hk with h1 | h1 | h1 | h1
    · exact hne h1
    · subst h1; rw [c16cK_z hB] at h; exact absurd h (by decide)
    · subst h1; rw [c16cK_u hB] at h; exact absurd h (by decide)
    · subst h1; rw [c16cK_zu hB] at h; exact absurd h (by decide)
  · rintro rfl
    exact c16cK_one z u

theorem c16cK_mul {K : Subgroup G} {z u : G} (hB : C16KBasis K z u) {k k' : G} (hk : k ∈ K)
    (hk' : k' ∈ K) : c16cK z u (k * k') = c16cK z u k + c16cK z u k' := by
  rcases (hB.mem_iff k).mp hk with h1 | h1 | h1 | h1 <;>
  rcases (hB.mem_iff k').mp hk' with h2 | h2 | h2 | h2 <;>
  subst h1 <;> subst h2 <;>
  simp only [c16cK_one, c16cK_z hB, c16cK_u hB, c16cK_zu hB, hB.z_sq, hB.u_sq,
    hB.comm.symm, c16_z_mul_zu hB, c16_u_mul_zu hB, c16_zu_mul_z hB, c16_zu_mul_u hB,
    c16_zu_mul_zu hB, one_mul, mul_one] <;>
  decide

theorem c16cK_rho {K : Subgroup G} {z u rho : G} (hB : C16KBasis K z u)
    (hz : rho * z * rho⁻¹ = u) (hu : rho * u * rho⁻¹ = z * u) {k : G} (hk : k ∈ K) :
    c16cK z u (rho * k * rho⁻¹) = c16Rho0 (c16cK z u k) := by
  rcases (hB.mem_iff k).mp hk with h1 | h1 | h1 | h1 <;> subst h1
  · rw [mul_one, mul_inv_cancel, c16cK_one]
    decide
  · rw [hz, c16cK_u hB, c16cK_z hB]
    decide
  · rw [hu, c16cK_zu hB, c16cK_u hB]
    decide
  · have hconj : rho * (z * u) * rho⁻¹ = u * (z * u) := by
      rw [show rho * (z * u) * rho⁻¹ = (rho * z * rho⁻¹) * (rho * u * rho⁻¹) from by
            group, hz, hu]
    rw [hconj, c16_u_mul_zu hB, c16cK_zu hB, c16cK_z hB]
    decide

theorem c16_KBasis_of_card {K : Subgroup G} [Finite G] {z u : G} (hcard : Nat.card K = 4)
    (hel : ∀ k ∈ K, k * k = 1) (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hz : z ∈ K)
    (hu : u ∈ K) (hz1 : z ≠ 1) (hu1 : u ≠ 1) (hzu : z ≠ u) : C16KBasis K z u := by
  have hzu_ne_one : z * u ≠ 1 := by
    intro h
    have h' : z * u = z * z := by rw [h, hel z hz]
    exact hzu (mul_left_cancel h').symm
  have hzu_ne_z : z * u ≠ z := by
    intro h
    have h' : z * u = z * 1 := by rw [h, mul_one]
    exact hu1 (mul_left_cancel h')
  have hzu_ne_u : z * u ≠ u := by
    intro h
    have h' : z * u = 1 * u := by rw [h, one_mul]
    exact hz1 (mul_right_cancel h')
  refine ⟨hz, hu, hel z hz, hel u hu, hcomm z hz u hu, hz1, hu1, hzu, ?_⟩
  intro k
  constructor
  · intro hk
    have hSsub : ({1, z, u, z * u} : Set G) ⊆ (K : Set G) := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact K.one_mem
      · exact hz
      · exact hu
      · exact K.mul_mem hz hu
    have hS : ({1, z, u, z * u} : Set G).ncard = 4 := by
      rw [Set.ncard_eq_four]
      exact ⟨1, z, u, z * u, Ne.symm hz1, Ne.symm hu1, Ne.symm hzu_ne_one,
        hzu, Ne.symm hzu_ne_z, Ne.symm hzu_ne_u, rfl⟩
    have hKn : (K : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard
    have hSeq : ({1, z, u, z * u} : Set G) = (K : Set G) :=
      Set.eq_of_subset_of_ncard_le hSsub (le_of_eq (by rw [hKn, hS]))
    have hkS : k ∈ ({1, z, u, z * u} : Set G) := by
      rw [hSeq]
      exact hk
    simpa using hkS
  · rintro (rfl | rfl | rfl | rfl)
    · exact K.one_mem
    · exact hz
    · exact hu
    · exact K.mul_mem hz hu

theorem c16_rho_zu {K : Subgroup G} {z u rho : G} (hB : C16KBasis K z u) (hr3 : rho ^ 3 = 1)
    (hrK : ∀ k ∈ K, rho * k * rho⁻¹ ∈ K) (hmove : ∀ k ∈ K, k ≠ 1 → rho * k * rho⁻¹ ≠ k)
    (hz : rho * z * rho⁻¹ = u) : rho * u * rho⁻¹ = z * u := by
  have hvK : rho * u * rho⁻¹ ∈ K := hrK u hB.u_mem
  have hv1 : rho * u * rho⁻¹ ≠ 1 := by
    intro h
    have hu1 : u = 1 := by
      calc u = rho⁻¹ * (rho * u * rho⁻¹) * rho := by group
        _ = rho⁻¹ * 1 * rho := by rw [h]
        _ = 1 := by group
    exact hB.u_ne_one hu1
  have hvu : rho * u * rho⁻¹ ≠ u := hmove u hB.u_mem hB.u_ne_one
  rcases (hB.mem_iff (rho * u * rho⁻¹)).mp hvK with h | h | h | h
  · exact absurd h hv1
  · exfalso
    have hconj2 : rho * (rho * z * rho⁻¹) * rho⁻¹ = z := by rw [hz, h]
    have hconj3_u : rho * (rho * (rho * z * rho⁻¹) * rho⁻¹) * rho⁻¹ = u := by
      rw [hconj2, hz]
    have hconj3_z : rho * (rho * (rho * z * rho⁻¹) * rho⁻¹) * rho⁻¹ = z := by
      have h3 : rho * rho * rho = 1 := by
        simpa only [pow_succ, pow_one, pow_zero, one_mul] using hr3
      have hcube : rho * (rho * (rho * z * rho⁻¹) * rho⁻¹) * rho⁻¹
          = (rho * rho * rho) * z * (rho * rho * rho)⁻¹ := by group
      rw [hcube, h3]
      group
    rw [hconj3_u] at hconj3_z
    exact hB.z_ne_u hconj3_z.symm
  · exact absurd h hvu
  · exact h

theorem c16_add_self (w : C16H0) : w + w = 0 := by
  revert w
  decide

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
