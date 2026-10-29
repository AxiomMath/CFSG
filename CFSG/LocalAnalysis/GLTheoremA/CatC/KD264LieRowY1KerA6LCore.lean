module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

@[expose] def D4 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, -1, 0, 0; 1, -1, 0, 0; 0, 0, 0, -1; 0, 0, 1, -1]

theorem quad_mulVec {K : Type} [Field K] {T : Matrix (Fin 4) (Fin 4) K}
    (hT : T * T + T + 1 = 0) (v : Fin 4 → K) :
    T *ᵥ (T *ᵥ v) = -(v + T *ᵥ v) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M *ᵥ v) hT
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    at h
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_comm, add_left_comm, add_assoc] using h

theorem norm_eq_zero {K : Type} [Field K] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0) {c d : K}
    (hN : c ^ 2 - c * d + d ^ 2 = 0) : c = 0 ∧ d = 0 := by
  by_cases hd : d = 0
  · subst hd
    have hc : c ^ 2 = 0 := by linear_combination hN
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp hc, rfl⟩
  · exfalso
    apply hnr (-(c / d))
    have h1 : (c / d) ^ 2 - c / d + 1 = 0 := by
      field_simp
      linear_combination hN
    linear_combination h1

theorem norm_form {K : Type} [Field K] {T : Matrix (Fin 4) (Fin 4) K}
    (hT : T * T + T + 1 = 0) (c d : K) (v : Fin 4 → K) :
    (c - d) • (c • v + d • (T *ᵥ v)) - d • (T *ᵥ (c • v + d • (T *ᵥ v))) =
      (c ^ 2 - c * d + d ^ 2) • v := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, quad_mulVec hT]
  module

theorem basis4 {K : Type} [Field K] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    (T : Matrix (Fin 4) (Fin 4) K) (hT : T * T + T + 1 = 0)
    (hfix : ∀ v : Fin 4 → K, T *ᵥ v = v → v = 0) :
    ∃ S : Matrix.GeneralLinearGroup (Fin 4) K,
      T * (S : Matrix (Fin 4) (Fin 4) K) = (S : Matrix (Fin 4) (Fin 4) K) * D4 K := by
  classical
  obtain ⟨u1, hu1⟩ : ∃ v : Fin 4 → K, v ≠ 0 := by
    refine ⟨Pi.single 0 1, fun h => ?_⟩
    have := congrFun h 0
    simp at this
  obtain ⟨u2, hu2⟩ : ∃ v : Fin 4 → K, v ∉ Submodule.span K ({u1, T *ᵥ u1} : Set (Fin 4 → K)) := by
    by_contra h
    push Not at h
    have htop : Submodule.span K ({u1, T *ᵥ u1} : Set (Fin 4 → K)) = ⊤ :=
      eq_top_iff.mpr (fun v _ => h v)
    have hfin := finrank_span_le_card (R := K) ({u1, T *ᵥ u1} : Set (Fin 4 → K))
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfin
    have hc : ({u1, T *ᵥ u1} : Set (Fin 4 → K)).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  set W := Submodule.span K ({u1, T *ᵥ u1} : Set (Fin 4 → K)) with hWdef
  have hindep : ∀ a b c d : K, a • u1 + b • (T *ᵥ u1) + c • u2 + d • (T *ᵥ u2) = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
    intro a b c d h
    have hZ : c • u2 + d • (T *ᵥ u2) = -(a • u1 + b • (T *ᵥ u1)) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [← h]
      abel
    have hN2 : (c ^ 2 - c * d + d ^ 2) • u2 =
        -(((c - d) * a + d * b) • u1 + ((c - d) * b - d * a + d * b) • (T *ᵥ u1)) := by
      have h1 := norm_form hT c d u2
      rw [hZ] at h1
      rw [← h1]
      simp only [Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_smul, quad_mulVec hT]
      module
    by_cases hN : c ^ 2 - c * d + d ^ 2 = 0
    · obtain ⟨hc, hd⟩ := norm_eq_zero hnr hN
      subst hc
      subst hd
      have hW0 : a • u1 + b • (T *ᵥ u1) = 0 := by
        rw [zero_smul, zero_smul, add_zero] at h
        simpa using h
      have hab := norm_form hT a b u1
      simp only [hW0, Matrix.mulVec_zero, smul_zero, sub_zero] at hab
      have hN' : (a ^ 2 - a * b + b ^ 2) • u1 = 0 := hab.symm
      rcases smul_eq_zero.mp hN' with h0 | h0
      · obtain ⟨ha, hb⟩ := norm_eq_zero hnr h0
        exact ⟨ha, hb, rfl, rfl⟩
      · exact absurd h0 hu1
    · exfalso
      apply hu2
      have hu2e : u2 = (c ^ 2 - c * d + d ^ 2)⁻¹ •
          -(((c - d) * a + d * b) • u1 + ((c - d) * b - d * a + d * b) • (T *ᵥ u1)) := by
        rw [← hN2, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [hu2e]
      refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.add_mem _ ?_ ?_))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  let vec : Fin 4 → (Fin 4 → K) := ![u1, T *ᵥ u1, u2, T *ᵥ u2]
  let S : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => vec j i
  have hSx : ∀ x : Fin 4 → K,
      S *ᵥ x = x 0 • u1 + x 1 • (T *ᵥ u1) + x 2 • u2 + x 3 • (T *ᵥ u2) := by
    intro x
    ext i
    simp [S, vec, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  have hinj : Function.Injective (S *ᵥ ·) := by
    intro x y hxy
    have hxy' : S *ᵥ x = S *ᵥ y := hxy
    have h0 : S *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy', sub_self]
    rw [hSx] at h0
    obtain ⟨h0', h1', h2', h3'⟩ := hindep _ _ _ _ (by simpa using h0)
    funext k
    fin_cases k
    · exact sub_eq_zero.mp h0'
    · exact sub_eq_zero.mp h1'
    · exact sub_eq_zero.mp h2'
    · exact sub_eq_zero.mp h3'
  have hunit : IsUnit S := Matrix.mulVec_injective_iff_isUnit.mp hinj
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  have hcol : ∀ j : Fin 4, T *ᵥ (fun k => S k j) = S *ᵥ (fun k => D4 K k j) := by
    intro j
    fin_cases j
    · show T *ᵥ u1 = S *ᵥ (fun k => D4 K k 0)
      rw [hSx]
      simp [D4]
    · show T *ᵥ (T *ᵥ u1) = S *ᵥ (fun k => D4 K k 1)
      rw [quad_mulVec hT, hSx]
      simp [D4]
      module
    · show T *ᵥ u2 = S *ᵥ (fun k => D4 K k 2)
      rw [hSx]
      simp [D4]
    · show T *ᵥ (T *ᵥ u2) = S *ᵥ (fun k => D4 K k 3)
      rw [quad_mulVec hT, hSx]
      simp [D4]
      module
  ext i j
  exact congrFun (hcol j) i

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
