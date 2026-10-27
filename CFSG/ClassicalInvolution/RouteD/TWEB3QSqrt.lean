module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Aux
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

section Torus

variable {F : Type} [Field F]

theorem torusHom_neg_one_b3 : torusHom F (-1 : Fˣ) = -1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_torusHom]

theorem blockSL_torus_mul_zero (t : Fˣ) (A : SL(2, F)) :
    blockSL F 3 2 1 (by omega) (torusHom F t) * blockSL F 3 2 0 (by omega) A =
      blockSL F 3 2 0 (by omega) (diagConj2 1 t A) *
        blockSL F 3 2 1 (by omega) (torusHom F t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_blockSL_three_one, coe_blockSL_three_zero, coe_blockSL_three_zero, coe_diagConj2,
    coe_torusHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem blockSL_torus_comm_neg_one (t : Fˣ) :
    blockSL F 3 2 1 (by omega) (torusHom F t) * blockSL F 3 2 0 (by omega) (-1) =
      blockSL F 3 2 0 (by omega) (-1) * blockSL F 3 2 1 (by omega) (torusHom F t) := by
  have h := blockSL_torus_mul_zero t (-1)
  have e : diagConj2 1 t (-1 : SL(2, F)) = -1 := by
    refine Subtype.ext ?_
    rw [coe_diagConj2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  rwa [e] at h

end Torus

section Sqrt

variable {F : Type} [Field F] {X : Type} [Group X]

theorem exists_sqrt_partner (h2 : (2 : F) ≠ 0) {i : Fˣ} (hi : i * i = -1)
    {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) {z s : X} (hz : z ∈ U)
    (hz2 : orderOf z = 2) (hs : s ∈ V) (hs2 : orderOf s = 2) :
    ∃ d ∈ V, d * d = s ∧ d * z * d⁻¹ = z ∧ conjSub d U = U := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  have hzθ : z = θ (blockSL F 3 2 0 (by omega) (-1)) :=
    eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) (by rw [← hU] at hz; exact hz) hz2
  have hsθ : s = θ (blockSL F 3 2 1 (by omega) (-1)) :=
    eq_block_neg_one h2 hker (by omega : 1 + 2 ≤ 3) (by rw [← hV] at hs; exact hs) hs2
  set D : Fˣ → SL(3, F) := fun t => blockSL F 3 2 1 (by omega) (torusHom F t) with hD
  have hDmul : ∀ t u, D t * D u = D (t * u) := fun t u => by
    simp only [hD, ← map_mul]
  have hDinv : ∀ t, (D t)⁻¹ = D t⁻¹ := fun t => by
    simp only [hD, ← map_inv]
  have hD1 : ∀ t, θ (D t) ∈ V := fun t => by
    rw [← hV]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  have hconjU : ∀ t, ∀ u ∈ U, θ (D t) * u * (θ (D t))⁻¹ ∈ U := by
    intro t u hu
    rw [← hU] at hu ⊢
    obtain ⟨b, hb, rfl⟩ := hu
    obtain ⟨A, rfl⟩ := hb
    refine ⟨blockSL F 3 2 0 (by omega) (diagConj2 1 t A), ⟨_, rfl⟩, ?_⟩
    have e : D t * blockSL F 3 2 0 (by omega) A =
        blockSL F 3 2 0 (by omega) (diagConj2 1 t A) * D t := blockSL_torus_mul_zero t A
    rw [← map_inv, ← map_mul, ← map_mul, e]
    congr 1
    group
  refine ⟨θ (D i), hD1 i, ?_, ?_, ?_⟩
  · rw [← map_mul, hDmul, hi, hsθ]
    simp only [hD, torusHom_neg_one_b3]
  · rw [hzθ, mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    congr 1
    exact blockSL_torus_comm_neg_one i
  · ext x
    rw [mem_conjSub_iff]
    have hinv : (θ (D i))⁻¹ = θ (D i⁻¹) := by rw [← map_inv, hDinv]
    constructor
    · intro hx
      have := hconjU i _ hx
      rwa [show θ (D i) * ((θ (D i))⁻¹ * x * θ (D i)) * (θ (D i))⁻¹ = x by group] at this
    · intro hx
      have := hconjU i⁻¹ x hx
      rwa [← hinv, inv_inv] at this

end Sqrt

end CFSG.ClassicalInvolution.RouteD.TWE.B3
