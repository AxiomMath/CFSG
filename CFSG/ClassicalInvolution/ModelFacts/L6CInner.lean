module

public import CFSG.ClassicalInvolution.ModelFacts.L6CMat
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.Separable

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix Module
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (exists_eigenbasis isCompl_eigenspaces)
open scoped MatrixGroups

variable {F : Type} [Field F]

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) F

theorem inv_smul_mul_self4 {M : 𝕄₄} {c μ : F} (hμ0 : μ ≠ 0) (hμμ : μ * μ = c)
    (hM : M * M = c • 1) : (μ⁻¹ • M) * (μ⁻¹ • M) = 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, hM, smul_smul, smul_smul]
  have : μ⁻¹ * μ⁻¹ * c = 1 := by
    rw [← hμμ]
    field_simp
  rw [this, one_smul]

theorem exists_eigen_matrix4 (hK : ringChar F ≠ 2) {B : 𝕄₄} (hB : B * B = 1) :
    ∃ (P : GL (Fin 4) F) (d : Fin 4 → F), d 0 = d 1 ∧
      B * (P : 𝕄₄) = (P : 𝕄₄) * Matrix.diagonal d := by
  have key : ∀ B' : 𝕄₄, B' * B' = 1 → 2 ≤ finrank F (LinearMap.ker (toLin' B' - 1)) →
      ∃ (P : GL (Fin 4) F) (d : Fin 4 → F), d 0 = d 1 ∧
        B' * (P : 𝕄₄) = (P : 𝕄₄) * Matrix.diagonal d := by
    intro B' hB' h2k
    obtain ⟨b, hb⟩ := exists_eigenbasis hK hB'
    set k := finrank F (LinearMap.ker (toLin' B' - 1)) with hk
    let d : Fin 4 → F := fun i => if (i : ℕ) < k then 1 else -1
    let P : GL (Fin 4) F := ⟨(Pi.basisFun F (Fin 4)).toMatrix b,
      b.toMatrix (Pi.basisFun F (Fin 4)), Basis.toMatrix_mul_toMatrix_flip _ _,
      Basis.toMatrix_mul_toMatrix_flip _ _⟩
    refine ⟨P, d, ?_, ?_⟩
    · have h0 : 0 < k := by omega
      have h1 : 1 < k := by omega
      simp [d, h0, h1]
    · ext r i
      have hP : ∀ s, (P : 𝕄₄) s i = b i s := fun s => by
        change ((Pi.basisFun F (Fin 4)).toMatrix b) s i = _
        simp [Basis.toMatrix_apply]
      have h3 := congrFun (hb i) r
      rw [Matrix.mul_diagonal, Matrix.mul_apply]
      simp only [hP]
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h3
      rw [h3]
      simp only [d]
      ring
  by_cases h2k : 2 ≤ finrank F (LinearMap.ker (toLin' B - 1))
  · exact key B hB h2k
  · have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK hB)
    rw [finrank_fin_fun] at hsum
    have hker : LinearMap.ker (toLin' (-B) - 1) = LinearMap.ker (toLin' B + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    obtain ⟨P, d, hd, hP⟩ := key (-B) (by rw [neg_mul_neg, hB]) (by rw [hker]; omega)
    refine ⟨P, fun i => -d i, by simp [hd], ?_⟩
    have hdd : Matrix.diagonal (fun i => -d i) = -Matrix.diagonal d := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hdd, Matrix.mul_neg, ← hP, Matrix.neg_mul, neg_neg]

theorem exists_inner_sq (hK : ringChar F ≠ 2) {A : 𝕄₄} {c μ : F} (hμ0 : μ ≠ 0) (hμμ : μ * μ = c)
    (hA : A * A = c • 1) :
    ∃ (P : GL (Fin 4) F) (N : 𝕄₄), A * (P : 𝕄₄) = (P : 𝕄₄) * N ∧ N * (rot4 F : 𝕄₄) =
      (rot4 F : 𝕄₄) * N := by
  set B : 𝕄₄ := μ⁻¹ • A with hB
  have hBB : B * B = 1 := inv_smul_mul_self4 hμ0 hμμ hA
  obtain ⟨P, d, hd, hP⟩ := exists_eigen_matrix4 hK hBB
  refine ⟨P, Matrix.diagonal (fun i => μ * d i), ?_, ?_⟩
  · have hAB : A = μ • B := by
      rw [hB, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
    rw [hAB, Matrix.smul_mul, hP]
    ext r i
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
    ring
  · exact diagonal_mul_rot4 (by simp [hd])

theorem mulVec_mulVec_self {A : 𝕄₄} {c : F} (hA : A * A = c • 1) (x : Fin 4 → F) :
    A *ᵥ (A *ᵥ x) = c • x := by
  rw [Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec]

section Nonsquare

variable [Finite F]

omit [Finite F] in
theorem mulVec_ne_smul {A : 𝕄₄} {c : F} (hA : A * A = c • 1) (hc : ¬ IsSquare c)
    {x : Fin 4 → F} (hx : x ≠ 0) (t : F) : A *ᵥ x ≠ t • x := by
  intro h
  have h1 := mulVec_mulVec_self hA x
  rw [h, Matrix.mulVec_smul, h, smul_smul] at h1
  have h3 : (t * t - c) • x = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h3 with h0 | h0
  · exact hc ⟨t, by linear_combination -h0⟩
  · exact hx h0

omit [Finite F] in
theorem linearIndependent_pair {A : 𝕄₄} {c : F} (hA : A * A = c • 1) (hc : ¬ IsSquare c)
    {x : Fin 4 → F} (hx : x ≠ 0) : LinearIndependent F ![x, A *ᵥ x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hx, rfl⟩
  · exfalso
    refine mulVec_ne_smul hA hc hx (-(t⁻¹ * s)) ?_
    have h3 : t • (A *ᵥ x) = -(s • x) := eq_neg_of_add_eq_zero_right hst
    calc A *ᵥ x = t⁻¹ • (t • (A *ᵥ x)) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = -(t⁻¹ * s) • x := by rw [h3, smul_neg, smul_smul, neg_smul]

theorem exists_inner_nonsq (hn1 : ¬ IsSquare (-1 : F)) (h2 : (2 : F) ≠ 0) {A : 𝕄₄} {c : F}
    (hA : A * A = c • 1) (hc : ¬ IsSquare c) :
    ∃ (P : GL (Fin 4) F) (N : 𝕄₄), A * (P : 𝕄₄) = (P : 𝕄₄) * N ∧
      N * (rot4 F : 𝕄₄) = (rot4 F : 𝕄₄) * N := by
  classical
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨u, hu⟩ := MF15.isSquare_neg_of_not hc hn1
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hc0
    linear_combination -hu
  let T : Module.End F (Fin 4 → F) := Matrix.toLin' A
  have hTx : ∀ x, T x = A *ᵥ x := fun x => rfl
  have hTT : ∀ x, T (T x) = c • x := fun x => by rw [hTx, hTx]; exact mulVec_mulVec_self hA x
  have hss : T.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := Polynomial.X ^ 2 - Polynomial.C c) ?_ ?_
    · exact (Polynomial.separable_X_pow_sub_C c (by simpa using h2) hc0).squarefree
    · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one]
      ext x
      simp [pow_two, Module.End.mul_apply, hTT]
  let v : Fin 4 → F := Pi.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v] at this
  have hli := linearIndependent_pair hA hc hv
  let U : Submodule F (Fin 4 → F) := Submodule.span F (Set.range ![v, A *ᵥ v])
  have hUfin : finrank F U = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have hvU : v ∈ U := Submodule.subset_span ⟨0, rfl⟩
  have hAvU : A *ᵥ v ∈ U := Submodule.subset_span ⟨1, rfl⟩
  have hUinv : U ∈ T.invtSubmodule := by
    rw [Module.End.mem_invtSubmodule]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · show T v ∈ U
      rw [hTx]
      exact hAvU
    · show T (A *ᵥ v) ∈ U
      rw [hTx, mulVec_mulVec_self hA]
      exact Submodule.smul_mem _ _ hvU
  obtain ⟨W, hWinv, hUW⟩ := Module.End.isSemisimple_iff.mp hss U hUinv
  have hsum := Submodule.finrank_add_eq_of_isCompl hUW
  rw [finrank_fin_fun, hUfin] at hsum
  have hWfin : finrank F W = 2 := by omega
  obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    rw [hbot, finrank_bot] at hWfin
    omega
  have hAwW : A *ᵥ w ∈ W := by
    have := ((Module.End.mem_invtSubmodule T).mp hWinv) hwW
    simpa [hTx] using this
  have hliw := linearIndependent_pair hA hc hw0
  have hWspan : Submodule.span F (Set.range ![w, A *ᵥ w]) = W := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hwW
      · exact hAwW
    · rw [finrank_span_eq_card hliw, hWfin]
      simp
  let vs : Fin 4 → Fin 4 → F := ![v, (-u⁻¹) • (A *ᵥ v), w, A *ᵥ w]
  have hvs0 : vs 0 = v := rfl
  have hvs1 : vs 1 = (-u⁻¹) • (A *ᵥ v) := rfl
  have hvs2 : vs 2 = w := rfl
  have hvs3 : vs 3 = A *ᵥ w := rfl
  have hAv : A *ᵥ v = (-u) • vs 1 := by
    rw [hvs1, smul_smul, show -u * -u⁻¹ = 1 by field_simp, one_smul]
  have hspan : Submodule.span F (Set.range vs) = ⊤ := by
    rw [eq_top_iff, ← hUW.sup_eq_top]
    refine sup_le ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span ⟨0, rfl⟩
      · show A *ᵥ v ∈ _
        rw [hAv]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    · rw [← hWspan]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Submodule.subset_span ⟨2, rfl⟩
      · exact Submodule.subset_span ⟨3, rfl⟩
  have hv1 : A *ᵥ vs 1 = u • vs 0 := by
    rw [hvs1, hvs0, Matrix.mulVec_smul, mulVec_mulVec_self hA, smul_smul]
    congr 1
    field_simp
    linear_combination hu
  have hv2 : A *ᵥ vs 3 = c • vs 2 := by
    rw [hvs3, hvs2]
    exact mulVec_mulVec_self hA w
  refine ⟨colGL vs hspan, !![0, u, 0, 0; -u, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0], ?_, ?_⟩
  · rw [coe_colGL, mul_colMat, colMat_mul]
    congr 1
    funext j
    fin_cases j
    · show A *ᵥ vs 0 = _
      simp only [Fin.sum_univ_four]
      simp
      rw [hvs0, hAv, neg_smul]
    · show A *ᵥ vs 1 = _
      simp only [Fin.sum_univ_four]
      simp [hv1]
    · show A *ᵥ vs 2 = _
      simp only [Fin.sum_univ_four]
      simp
      rw [hvs2, hvs3]
    · show A *ᵥ vs 3 = _
      simp only [Fin.sum_univ_four]
      simp [hv2]
  · have := blockDiag_mul_rot4 (F := F) 0 u !![0, c; 1, 0]
    simpa using this

end Nonsquare

theorem exists_inner [Finite F] (hn1 : ¬ IsSquare (-1 : F)) (h2 : (2 : F) ≠ 0) {A : 𝕄₄} {c : F}
    (hc0 : c ≠ 0) (hA : A * A = c • 1) :
    ∃ (P : GL (Fin 4) F) (N : 𝕄₄), A * (P : 𝕄₄) = (P : 𝕄₄) * N ∧
      N * (rot4 F : 𝕄₄) = (rot4 F : 𝕄₄) * N := by
  by_cases hsq : IsSquare c
  · obtain ⟨μ, hμ⟩ := hsq
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      exact hc0 (by simpa using hμ)
    exact exists_inner_sq (MF15.ringChar_ne_two_of_two_ne_zero h2) hμ0 hμ.symm hA
  · exact exists_inner_nonsq hn1 h2 hA hsq

end CFSG.ClassicalInvolution.ModelFacts.L6C
