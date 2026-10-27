module

public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup

variable {G : Type} [Group G] {z : G}

theorem z_mul_conj_mem {Q A : Subgroup G} (hQ : Odd (Nat.card Q)) (hz : orderOf z = 2)
    (hzQ : z ∈ normalizer (Q : Set G)) (hAn : ∀ q ∈ Q, ∀ a ∈ A, q * a * q⁻¹ ∈ A)
    (hCQ : Q ⊓ centralizer ({z} : Set G) ≤ A) {q : G} (hq : q ∈ Q) : z * q * z⁻¹ * q ∈ A := by
  obtain ⟨hbij, -⟩ := CFSG.OddInversion.odd_involution_product_decomposition hQ hz hzQ
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := hbij.surjOn hq
  have hcA : c ∈ A := hCQ hc
  obtain ⟨hcQ, hcz⟩ := mem_inf.mp hc
  have hzc : z * c * z⁻¹ = c := by
    have := mem_centralizer_singleton_iff.mp hcz
    rw [← this]; group
  have hjQ : j ∈ Q := hj.1
  have hjz : z * j * z⁻¹ = j⁻¹ := hj.2
  have hcj' : c * j = q := hcj
  rw [← hcj']
  have h1 : z * (c * j) * z⁻¹ * (c * j) = c * (j⁻¹ * c * j) := by
    calc z * (c * j) * z⁻¹ * (c * j) = (z * c * z⁻¹) * (z * j * z⁻¹) * (c * j) := by group
      _ = c * j⁻¹ * (c * j) := by rw [hzc, hjz]
      _ = c * (j⁻¹ * c * j) := by group
  rw [h1]
  refine A.mul_mem hcA ?_
  have := hAn j⁻¹ (Q.inv_mem hjQ) c hcA
  simpa using this

theorem comm_mem_gen {Q A : Subgroup G} (hQ : Odd (Nat.card Q)) (hz : orderOf z = 2)
    (hzQ : z ∈ normalizer (Q : Set G)) (hAn : ∀ q ∈ Q, ∀ a ∈ A, q * a * q⁻¹ ∈ A)
    (hCQ : Q ⊓ centralizer ({z} : Set G) ≤ A) {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    q * q' * q⁻¹ * q'⁻¹ ∈ A := by
  have key : ∀ q ∈ Q, ∀ q' ∈ Q, q⁻¹ * q'⁻¹ * q * q' ∈ A := by
    intro q hq q' hq'
    have h1 := z_mul_conj_mem hQ hz hzQ hAn hCQ hq
    have h2 := z_mul_conj_mem hQ hz hzQ hAn hCQ hq'
    have h3 := z_mul_conj_mem hQ hz hzQ hAn hCQ (Q.mul_mem hq hq')
    have h4 : q⁻¹ * (z * q' * z⁻¹ * q') * q ∈ A := by
      have := hAn q⁻¹ (Q.inv_mem hq) _ h2
      simpa using this
    have h5 : q⁻¹ * q'⁻¹ * q * q' =
        (q⁻¹ * (z * q' * z⁻¹ * q') * q)⁻¹ * (z * q * z⁻¹ * q)⁻¹ * (z * (q * q') * z⁻¹ * (q * q')) := by
      group
    rw [h5]
    exact A.mul_mem (A.mul_mem (A.inv_mem h4) (A.inv_mem h1)) h3
  have := key q⁻¹ (Q.inv_mem hq) q'⁻¹ (Q.inv_mem hq')
  simpa using this

end CFSG.GH74.Uniqueness.SU.SU13
