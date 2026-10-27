module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KGD.D4T36Torus

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4MatThree_mul : d4MatThreeA * d4MatThreeB = 1 := by decide +kernel

theorem d4MatThree_mul' : d4MatThreeB * d4MatThreeA = 1 := by decide +kernel

@[expose] def d4PermInvMat : D4Mat :=
  Matrix.of fun i j => if j = TwistTag.D4.perm i then 1 else 0

@[expose] def d4PermMat : D4Mat := !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]

theorem permLattice_symm_d4_eq (x : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm.symm x = d4PermInvMat *ᵥ x := by
  ext i
  simp [permLattice, d4PermInvMat, Matrix.mulVec, dotProduct]

theorem d4PermMat_mul : d4PermMat * d4PermInvMat = 1 := by decide +kernel

@[expose] def d4S0 : D4Mat := !![-1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def d4S1 : D4Mat := !![1, 0, 0, 0; 0, -1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def d4S3 : D4Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, -1]

theorem simple_zero_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    simple TwistTag.D4.tag 0 • v = d4S0 *ᵥ v := by
  refine weyl_smul_eq_mulVec (fun j => ?_) v
  rw [simple_smul]
  revert j
  decide +kernel

theorem simple_one_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    simple TwistTag.D4.tag 1 • v = d4S1 *ᵥ v := by
  refine weyl_smul_eq_mulVec (fun j => ?_) v
  rw [simple_smul]
  revert j
  decide +kernel

theorem simple_three_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    simple TwistTag.D4.tag 3 • v = d4S3 *ᵥ v := by
  refine weyl_smul_eq_mulVec (fun j => ?_) v
  rw [simple_smul]
  revert j
  decide +kernel

theorem weyl_inv_smul_mulVec {W : WeylGroup TwistTag.D4.tag} {M B : D4Mat} (hMB : M * B = 1)
    (h : ∀ x, W • x = M *ᵥ x) (x : Fin TwistTag.D4.tag.rank → ℤ) : W⁻¹ • x = B *ᵥ x := by
  have h1 : x = W • (B *ᵥ x) := by
    rw [h, Matrix.mulVec_mulVec, hMB, Matrix.one_mulVec]
  conv_lhs => rw [h1]
  rw [inv_smul_smul]

theorem det_d4PermMat_sub (q : ℤ) :
    Matrix.det !![q, 0, 0, -1; -1, q, 0, 0; 0, 0, q - 1, 0; 0, -1, 0, q] =
      (q - 1) * (q ^ 3 - 1) := by
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem d4PermMat_sub_det_ne_zero {q : ℕ} (hq : 2 ≤ q) :
    ((q : ℤ) • (1 : D4Mat) - d4PermMat).det ≠ 0 := by
  have hM : ((q : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) -
      !![0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0]) =
      !![(q : ℤ), 0, 0, -1; -1, q, 0, 0; 0, 0, q - 1, 0; 0, -1, 0, q] := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp
  have hdet : ((q : ℤ) • (1 : D4Mat) - d4PermMat).det = ((q : ℤ) - 1) * ((q : ℤ) ^ 3 - 1) := by
    rw [← det_d4PermMat_sub (q : ℤ), ← hM]
    rfl
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have h1 : (0 : ℤ) < (q : ℤ) - 1 := by omega
  have h2 : (0 : ℤ) < (q : ℤ) ^ 3 - 1 := by
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hq' 3
    norm_num at h3
    linarith
  rw [hdet]
  exact (mul_pos h1 h2).ne'

theorem q1_class_witness {W : WeylGroup TwistTag.D4.tag}
    (hW : (∀ x, W • x = d4MatThreeA *ᵥ x) ∨ (∀ x, W • x = d4MatThreeB *ᵥ x)) :
    ∃ u : WeylGroup TwistTag.D4.tag, ∀ x, (u * W⁻¹ * (weylTwist TwistTag.D4 u)⁻¹) • x =
      d4T36M 1 *ᵥ permLattice TwistTag.D4.perm.symm x := by
  rcases hW with hW | hW
  · refine ⟨simple TwistTag.D4.tag 1 * simple TwistTag.D4.tag 3, fun x => ?_⟩
    have hinv := weyl_inv_smul_mulVec d4MatThree_mul hW
    have hδ : weylTwist TwistTag.D4 (simple TwistTag.D4.tag 1 * simple TwistTag.D4.tag 3) =
        simple TwistTag.D4.tag 3 * simple TwistTag.D4.tag 0 := by
      rw [map_mul, weylTwist_simple, weylTwist_simple]
      rfl
    rw [hδ, mul_inv_rev, CoxeterSystem.inv_simple, CoxeterSystem.inv_simple]
    simp only [mul_smul, simple_zero_smul, simple_one_smul, simple_three_smul, hinv,
      Matrix.mulVec_mulVec, permLattice_symm_d4_eq]
    rw [show d4S1 * (d4S3 * (d4MatThreeB * (d4S0 * d4S3))) = d4T36M 1 * d4PermInvMat from by
      decide +kernel]
  · refine ⟨simple TwistTag.D4.tag 0, fun x => ?_⟩
    have hinv := weyl_inv_smul_mulVec d4MatThree_mul' hW
    have hδ : weylTwist TwistTag.D4 (simple TwistTag.D4.tag 0) = simple TwistTag.D4.tag 1 := by
      rw [weylTwist_simple]
      rfl
    rw [hδ, CoxeterSystem.inv_simple]
    simp only [mul_smul, simple_zero_smul, simple_one_smul, hinv, Matrix.mulVec_mulVec,
      permLattice_symm_d4_eq]
    rw [show d4S0 * (d4MatThreeA * d4S1) = d4T36M 1 * d4PermInvMat from by decide +kernel]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
