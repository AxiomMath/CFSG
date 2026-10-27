module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJWeyl
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJTorus

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix


section Numerics

@[expose] def jMw : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![1, 1, -1, 0; 0, 1, -1, 1; 1, 1, -1, 1; 1, 0, -1, 1]

@[expose] def jMbar : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ := !![2, -3; 1, -1]

@[expose] def jW2Mat : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ :=
  !![0, 1, -1, 1; 1, 0, -1, 1; 1, 1, -1, 1; 1, 1, -1, 0]

theorem wordMat_jWordW2 : wordMat TwistTag.D4.tag jWordW2 = jW2Mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mulVec_rank_d4 (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (x : Fin TwistTag.D4.tag.rank → ℤ) (i : Fin TwistTag.D4.tag.rank) :
    (M *ᵥ x) i = M i 0 * x 0 + M i 1 * x 1 + M i 2 * x 2 + M i 3 * x 3 := by
  rw [Matrix.mulVec, dotProduct]
  exact Fin.sum_univ_four _

theorem mulVec_rank_g2 (M : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ)
    (x : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank) :
    (M *ᵥ x) i = M i 0 * x 0 + M i 1 * x 1 := by
  rw [Matrix.mulVec, dotProduct]
  exact Fin.sum_univ_two _

theorem jW2_smul_eq (x : Fin TwistTag.D4.tag.rank → ℤ) :
    jW2 • x = jMw *ᵥ permLattice TwistTag.D4.perm.symm x := by
  rw [jW2, wordProd_smul_eq_wordMat_mulVec, wordMat_jWordW2]
  funext i
  rw [mulVec_rank_d4, mulVec_rank_d4]
  have h0 : permLattice TwistTag.D4.perm.symm x 0 = x 1 := rfl
  have h1 : permLattice TwistTag.D4.perm.symm x 1 = x 3 := rfl
  have h2 : permLattice TwistTag.D4.perm.symm x 2 = x 2 := rfl
  have h3 : permLattice TwistTag.D4.perm.symm x 3 = x 0 := rfl
  rw [h0, h1, h2, h3]
  fin_cases i
  · show (0 : ℤ) * x 0 + 1 * x 1 + (-1) * x 2 + 1 * x 3 =
      1 * x 1 + 1 * x 3 + (-1) * x 2 + 0 * x 0
    ring
  · show (1 : ℤ) * x 0 + 0 * x 1 + (-1) * x 2 + 1 * x 3 =
      0 * x 1 + 1 * x 3 + (-1) * x 2 + 1 * x 0
    ring
  · show (1 : ℤ) * x 0 + 1 * x 1 + (-1) * x 2 + 1 * x 3 =
      1 * x 1 + 1 * x 3 + (-1) * x 2 + 1 * x 0
    ring
  · show (1 : ℤ) * x 0 + 1 * x 1 + (-1) * x 2 + 0 * x 3 =
      1 * x 1 + 0 * x 3 + (-1) * x 2 + 1 * x 0
    ring

theorem jMw_proj (m : Fin TwistTag.D4.tag.rank → ℤ) :
    coinvProj (jMw *ᵥ m) = jMbar *ᵥ coinvProj m := by
  have e0 := mulVec_rank_g2 jMbar (coinvProj m) 0
  have e1 := mulVec_rank_g2 jMbar (coinvProj m) 1
  have a0 := mulVec_rank_d4 jMw m 0
  have a1 := mulVec_rank_d4 jMw m 1
  have a2 := mulVec_rank_d4 jMw m 2
  have a3 := mulVec_rank_d4 jMw m 3
  funext i
  fin_cases i
  · show (jMw *ᵥ m) 0 + (jMw *ᵥ m) 1 + (jMw *ᵥ m) 3 = (jMbar *ᵥ coinvProj m) 0
    rw [e0, a0, a1, a3]
    show ((1 : ℤ) * m 0 + 1 * m 1 + (-1) * m 2 + 0 * m 3) +
        ((0 : ℤ) * m 0 + 1 * m 1 + (-1) * m 2 + 1 * m 3) +
        ((1 : ℤ) * m 0 + 0 * m 1 + (-1) * m 2 + 1 * m 3) =
      2 * (m 0 + m 1 + m 3) + (-3) * m 2
    ring
  · show (jMw *ᵥ m) 2 = (jMbar *ᵥ coinvProj m) 1
    rw [e1, a2]
    show (1 : ℤ) * m 0 + 1 * m 1 + (-1) * m 2 + 1 * m 3 = 1 * (m 0 + m 1 + m 3) + (-1) * m 2
    ring

theorem jMbar_det_ne_zero (q : ℕ) :
    ((q : ℤ) • (1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) - jMbar).det ≠ 0 := by
  have key : ((q : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) - !![2, -3; 1, -1]).det ≠ 0 := by
    have hm : ((q : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) - !![2, -3; 1, -1]) =
        !![(q : ℤ) - 2, 3; -1, (q : ℤ) + 1] := by
      ext i j
      fin_cases i <;> fin_cases j
      · show (q : ℤ) * 1 - 2 = (q : ℤ) - 2
        ring
      · show (q : ℤ) * 0 - (-3) = 3
        ring
      · show (q : ℤ) * 0 - 1 = -1
        ring
      · show (q : ℤ) * 1 - (-1) = (q : ℤ) + 1
        ring
    rw [hm, Matrix.det_fin_two_of]
    nlinarith [sq_nonneg (2 * (q : ℤ) - 1)]
  exact key

end Numerics

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
