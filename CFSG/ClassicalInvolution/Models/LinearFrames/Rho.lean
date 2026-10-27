module

public import CFSG.ClassicalInvolution.Generic.Weyl
public import CFSG.ClassicalInvolution.Models.LinearFrames.Generation

public section

namespace CFSG.ClassicalInvolution.Models

open CFSG.ClassicalInvolution.Generic

section Monomial

variable {K : Type} [Field K] {n : ℕ} {G : Type*} [Group G] {mat : G →* Matrix (Fin n) (Fin n) K}

theorem monomial_mem_normalizer {w : G} {σ : Equiv.Perm (Fin n)} (hw : IsMonomialFor (mat w) σ) :
    w ∈ Subgroup.normalizer (signSubgroup mat : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hd := mat_eq_diagonal hy
    have h1 : mat w * mat y * mat w⁻¹ = Matrix.diagonal fun b => entOf mat y (σ.symm b) := by
      rw [hd]
      exact hw.mul_diagonal_mul_inv (by rw [← map_mul, mul_inv_cancel, map_one]) _
    refine ⟨fun b => entOf mat y (σ.symm b), fun b => entOf_cases hy _, ?_⟩
    rw [map_mul, map_mul]
    exact h1
  · intro hy
    have := (conj_mem_signSubgroup hw hy).1
    simpa [mul_assoc] using this

theorem monomial_conj_zMat {w : G} {σ : Equiv.Perm (Fin n)} (hw : IsMonomialFor (mat w) σ)
    (T : Finset (Fin n)) :
    mat w * zMat K n T * mat w⁻¹ = zMat K n (T.map σ.toEmbedding) :=
  hw.mul_zMat_mul_inv (by rw [← map_mul, mul_inv_cancel, map_one]) T

theorem exists_not_comm_of_monomial (h2 : (2 : K) ≠ 0) {z : Pair n → G}
    (hz : ∀ T, mat (z T) = zMat K n T.1) {w : G} {σ : Equiv.Perm (Fin n)}
    (hw : IsMonomialFor (mat w) σ) {i j k : Fin n} (hσ : σ i = j) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ e ∈ signSubgroup mat, e * w ≠ w * e := by
  refine ⟨z ⟨{i, k}, Finset.card_pair hik⟩, z_mem_signSubgroup hz _, fun h => ?_⟩
  have h1 : mat w * zMat K n {i, k} * mat w⁻¹ = zMat K n {i, k} := by
    have h' := congrArg mat h
    rw [map_mul, map_mul, hz] at h'
    rw [← h', Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  have h2' := monomial_conj_zMat hw {i, k}
  rw [h1] at h2'
  have h3 := zMat_inj h2 h2'
  have hj : j ∈ ({i, k} : Finset (Fin n)) := by
    rw [h3]
    exact Finset.mem_map.mpr ⟨i, by simp, hσ⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h
  · exact hij h.symm
  · exact hjk h

end Monomial

section RhoGen

variable {F : Type*} [Field F] [Finite F] {n : ℕ} {G : Type*} [Group G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

theorem rho_apply_of_conj (Fr : ToralFrame F Ω E S) (hT : CentTrivial E S)
    {L : Pair n → Subgroup G} (hLS : ∀ T, L T ∈ S) {T₀ : Pair n} {w : G}
    (hw : w ∈ normPart (L T₀) E) (hw' : w ∉ centPart (L T₀) E) {σ : Equiv.Perm (Fin n)}
    (hconj : ∀ T', conjSub w (L T') = L (Pair.map σ T')) (T' : Pair n) :
    ((Fr.rho ⟨L T₀, hLS T₀⟩ ⟨L T', hLS T'⟩ : ↥S) : Subgroup G) = L (Pair.map σ T') := by
  rw [← Fr.act_eq_rho hT hw hw']
  exact hconj T'

end RhoGen

end CFSG.ClassicalInvolution.Models
