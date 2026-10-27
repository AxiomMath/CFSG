module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X2
public import CFSG.ClassicalInvolution.Asc77.AscCX9P

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {F : Type} [Field F]

section Blocks

@[expose] def twGL {m : F} (hm : m ≠ 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![1, -m]) (by simp [hm])

theorem coe_twGL {m : F} (hm : m ≠ 0) :
    ((twGL hm : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = diagonal ![1, -m] := rfl

theorem coe_twGL_inv {m : F} (hm : m ≠ 0) :
    (((twGL hm)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = diagonal ![1, -m⁻¹] := by
  rw [Matrix.coe_units_inv]
  refine Matrix.inv_eq_right_inv ?_
  show diagonal ![1, -m] * diagonal ![1, -m⁻¹] = 1
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp [hm]

theorem kappa_longBlock0 {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (b : SL(2, F)) :
    kappa hm hn (longBlock F 2 0 b) =
      blockSL F 4 2 0 (by norm_num) (slConjugation 2 F (twGL hm) b) := by
  apply Subtype.ext
  rw [coe_kappa, mat_longBlock, WeakCT.coe_blockSL, slConjugation_matrix, coe_twGL_inv,
    blockMat_four_zero]
  show kMat m n _ = _
  rw [coe_twGL]
  ext i j
  rw [kMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [dVec, spIdx, CFSG.LieType.Steinberg.Sp.blockMat, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hn]

theorem kappa_longBlock1 {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) (b : SL(2, F)) :
    kappa hm hn (longBlock F 2 1 b) =
      blockSL F 4 2 2 (by norm_num) (slConjugation 2 F (twGL hn) b) := by
  apply Subtype.ext
  rw [coe_kappa, mat_longBlock, WeakCT.coe_blockSL, slConjugation_matrix, coe_twGL_inv,
    blockMat_four_two]
  show kMat m n _ = _
  rw [coe_twGL]
  ext i j
  rw [kMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [dVec, spIdx, CFSG.LieType.Steinberg.Sp.blockMat, Matrix.mul_diagonal,
      Matrix.diagonal_mul, hm]

theorem range_comp_mulAut {G' : Type} [Group G'] (φ : SL(2, F) →* G') (α : MulAut SL(2, F)) :
    (φ.comp α.toMonoidHom).range = φ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr α.surjective, ← MonoidHom.range_eq_map]

theorem kappa_longRoot0 {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    (longRootSp2 F 2 0).map (kappa hm hn) = (blockSL F 4 2 0 (by norm_num)).range := by
  have h : (kappa hm hn).comp (longBlock F 2 0) =
      (blockSL F 4 2 0 (by norm_num)).comp (slConjugation 2 F (twGL hm)).toMonoidHom := by
    ext b : 1
    exact kappa_longBlock0 hm hn b
  rw [longRootSp2, ← MonoidHom.range_comp, h, range_comp_mulAut]

theorem kappa_longRoot1 {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    (longRootSp2 F 2 1).map (kappa hm hn) = (blockSL F 4 2 2 (by norm_num)).range := by
  have h : (kappa hm hn).comp (longBlock F 2 1) =
      (blockSL F 4 2 2 (by norm_num)).comp (slConjugation 2 F (twGL hn)).toMonoidHom := by
    ext b : 1
    exact kappa_longBlock1 hm hn b
  rw [longRootSp2, ← MonoidHom.range_comp, h, range_comp_mulAut]

end Blocks

section Fix

variable {Y : Type} [Group Y] [Finite Y]

theorem spM_perfect [Finite F] (h4 : 4 ≤ Nat.card F) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⁅spM (spForm m n), spM (spForm m n)⁆ = spM (spForm m n) := by
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inl (Or.inr h4))).1
  rw [← kappa_range hm hn, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact hperf.commutator_eq_top

theorem perfRes_fix_eq [Finite F] (h4 : 4 ≤ Nat.card F) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (θ : SL(4, F) →* Y) (hθ : Function.Surjective θ) (hker : θ.ker = scalars 4 F)
    (A : GL (Fin 4) F) (hA : (A : Matrix (Fin 4) (Fin 4) F) = spForm m n) (β : MulAut Y)
    (hβ : ∀ s, β (θ s) = θ (slConjugation 4 F A ((s⁻¹).transpose))) :
    Goldschmidt75.perfRes (fixSubgroup β) = (spM (spForm m n)).map θ := by
  apply le_antisymm
  ·
    have hfix : fixSubgroup β ≤ (simM (spForm m n)).map θ := by
      intro y hy
      obtain ⟨s, rfl⟩ := hθ y
      have hy' : β (θ s) = θ s := hy
      rw [hβ] at hy'
      have hs : proj 4 F (slConjugation 4 F A ((s⁻¹).transpose)) = proj 4 F s := by
        rw [proj_eq_proj_iff, ← hker, MonoidHom.mem_ker, map_mul, map_inv, hy', inv_mul_cancel]
      have := mem_simM_of_proj_eq A hs
      rw [hA] at this
      exact Subgroup.mem_map_of_mem θ this
    calc Goldschmidt75.perfRes (fixSubgroup β)
        ≤ Goldschmidt75.perfRes ((simM (spForm m n)).map θ) :=
          Goldschmidt75.le_perfRes ((Goldschmidt75.perfRes_le _).trans hfix)
            (Goldschmidt75.commutator_perfRes _)
      _ = (Goldschmidt75.perfRes (simM (spForm m n))).map θ :=
          (Goldschmidt75.map_perfRes θ _).symm
      _ ≤ (spM (spForm m n)).map θ := by
          refine Subgroup.map_mono ?_
          calc Goldschmidt75.perfRes (simM (spForm m n))
              = ⁅Goldschmidt75.perfRes (simM (spForm m n)),
                  Goldschmidt75.perfRes (simM (spForm m n))⁆ :=
                (Goldschmidt75.commutator_perfRes _).symm
            _ ≤ ⁅simM (spForm m n), simM (spForm m n)⁆ :=
                Subgroup.commutator_mono (Goldschmidt75.perfRes_le _)
                  (Goldschmidt75.perfRes_le _)
            _ ≤ spM (spForm m n) := commutator_simM_le_spM _
  ·
    refine Goldschmidt75.le_perfRes ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      show β (θ s) = θ s
      rw [hβ, slConj_eq_of_mem_spM A (by rw [hA]; exact hs)]
    · rw [← Subgroup.map_commutator, spM_perfect h4 hm hn]

end Fix

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
