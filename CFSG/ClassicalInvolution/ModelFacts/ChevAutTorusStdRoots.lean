module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusAct

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.ClassicalInvolution.ModelFacts

section Pair

variable {r : ℕ}

theorem pair_add (A : Matrix (Fin r) (Fin r) ℤ) (γ δ : Fin r → ℤ) (j : Fin r) :
    pair A (γ + δ) j = pair A γ j + pair A δ j := by
  simp [pair, mul_add, Finset.sum_add_distrib]

theorem pair_zsmul (A : Matrix (Fin r) (Fin r) ℤ) (c : ℤ) (γ : Fin r → ℤ) (j : Fin r) :
    pair A (c • γ) j = c * pair A γ j := by
  simp [pair, Finset.mul_sum, mul_left_comm]

end Pair

section Lattice

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (hA : TauCeti.IsFiniteType A)
  (hlong : ∀ k, IsLongest hA ∅ (Pi.single k 1))

include hlong

theorem eq_single_or_sub_of_pair_eq (ν : Fin r) (θ : Fin r → ℤ)
    (hθ1 : ∀ j, pair A θ j = if j = ν then 1 else 0) (hθ2 : θ ν = 2) {γ : Fin r → ℤ}
    (hγ : γ ∈ roots hA ∅) (k : Fin r)
    (hoff : ∀ j, j ≠ ν → pair A γ j = pair A (Pi.single k 1) j) :
    γ = Pi.single k 1 ∨ (k = ν ∧ γ = Pi.single k 1 - θ) := by
  set m₀ : ℤ := pair A γ ν - pair A (Pi.single k 1) ν with hm₀
  have hu : γ = Pi.single k 1 + m₀ • θ := by
    have h0 : ∀ j, pair A (γ - (Pi.single k 1 + m₀ • θ)) j = 0 := by
      intro j
      rw [pair_sub, pair_add, pair_zsmul, hθ1 j]
      by_cases hj : j = ν
      · subst hj
        simp [hm₀]
      · simp [hj, hoff j hj]
    exact sub_eq_zero.1 (eq_zero_of_pair_eq_zero hA h0)
  have hd := symmetrizer_pos hA k
  have hlen := lenSq_root hA hlong hγ k
  have hsym : ∀ l, symmetrizer hA l = symmetrizer hA k := fun l => symmetrizer_const hA hlong l k
  have hxy : form hA (toRat (Pi.single k 1 : Fin r → ℤ)) (toRat θ) =
      symmetrizer hA k * (if k = ν then 1 else 0 : ℤ) := by
    rw [form_comm, form_single_right_int hA θ k, hθ1 k]
  have hyy : form hA (toRat θ) (toRat θ) = symmetrizer hA k * 2 := by
    rw [form_eq_sum]
    have : ∀ l, form hA (toRat θ) (Pi.single l 1) =
        symmetrizer hA k * (if l = ν then 1 else 0 : ℤ) := by
      intro l
      rw [← toRat_single, form_single_right_int hA θ l, hθ1 l, hsym l]
    simp only [this, toRat_apply]
    rw [Finset.sum_eq_single ν]
    · simp [hθ2]
      ring
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ ν) h
  have hxx : form hA (toRat (Pi.single k 1 : Fin r → ℤ)) (toRat (Pi.single k 1)) =
      2 * symmetrizer hA k := by
    rw [toRat_single, form_single_single]
  have hnorm : lenSq hA γ = 2 * symmetrizer hA k +
      2 * (m₀ : ℚ) * (symmetrizer hA k * (if k = ν then 1 else 0 : ℤ)) +
        (m₀ : ℚ) ^ 2 * (symmetrizer hA k * 2) := by
    have hθq : toRat (m₀ • θ) = (m₀ : ℚ) • toRat θ := by
      rw [map_zsmul]
      exact (Int.cast_smul_eq_zsmul ℚ m₀ (toRat θ)).symm
    rw [lenSq, hu, map_add, hθq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [form_comm hA (toRat θ) (toRat (Pi.single k 1)), hxy, hxx, hyy]
    ring
  rw [hlen] at hnorm
  have h1 : (m₀ : ℚ) * ((if k = ν then 1 else 0 : ℤ) + m₀) = 0 := by
    have : symmetrizer hA k * (2 * ((m₀ : ℚ) * ((if k = ν then 1 else 0 : ℤ) + m₀))) = 0 := by
      linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hd.ne'
    · linarith
  have h2 : m₀ * ((if k = ν then 1 else 0 : ℤ) + m₀) = 0 := by exact_mod_cast h1
  rcases mul_eq_zero.1 h2 with h | h
  · left
    rw [hu, h]
    simp
  · by_cases hk : k = ν
    · right
      refine ⟨hk, ?_⟩
      have : m₀ = -1 := by
        simp only [hk, ↓reduceIte] at h
        omega
      rw [hu, this]
      simp [sub_eq_add_neg]
    · left
      simp only [hk, ↓reduceIte, zero_add] at h
      rw [hu, h]
      simp

end Lattice

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
