module

public import CFSG.LieType.SpecialLinear.Block222.Borel.Radical
public import CFSG.LieType.SpecialLinear.Block222.Borel.Graph

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

theorem coe_borelGraph_apply (n : ℕ) (q : SpecialLinearGroup (Fin n) F) (i j : Fin n) :
    ((borelGraph n F q : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) i j =
      ((q⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
        (Fin.rev j) (Fin.rev i) := by
  rw [coe_borelGraph, revGL_inv, coe_revGL, revMatrix_mul_mul]
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply]

theorem borelGraph_mul_self (n : ℕ) : borelGraph n F * borelGraph n F = 1 := by
  ext q i j
  rw [MulAut.mul_apply, coe_borelGraph_apply]
  have hinv : ((borelGraph n F) q)⁻¹ = (borelGraph n F) (q⁻¹) :=
    (map_inv (borelGraph n F) q).symm
  rw [hinv, coe_borelGraph_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]
  rfl

theorem blk222_rev_eq {i j : Fin (c + 4)} (h : blk222 c i = blk222 c j) :
    blk222 c (Fin.rev i) = blk222 c (Fin.rev j) := by
  have hi : ((Fin.rev i : Fin (c + 4)) : ℕ) = c + 3 - (i : ℕ) := by
    rw [Fin.val_rev]; omega
  have hj : ((Fin.rev j : Fin (c + 4)) : ℕ) = c + 3 - (j : ℕ) := by
    rw [Fin.val_rev]; omega
  simp only [blk222] at h ⊢
  rw [hi, hj]
  split_ifs at h ⊢ <;> omega

theorem isBlockRadicalMat_slFieldAut (σ : F ≃+* F)
    {q : SpecialLinearGroup (Fin (c + 4)) F}
    (hq : IsBlockRadicalMat c F (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) :
    IsBlockRadicalMat c F
      ((CatalogueBHigherLinearField.slFieldAut (Fin (c + 4)) F σ q :
        SpecialLinearGroup (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) := by
  obtain ⟨hupper, hdiag, hblock⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · intro i j hji
    change σ ((q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) i j) = 0
    rw [hupper i j hji, map_zero]
  · intro i
    change σ ((q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) i i) = 1
    rw [hdiag i, map_one]
  · intro i j hij hij'
    change σ ((q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) i j) = 0
    rw [hblock i j hij hij', map_zero]

theorem isBlockRadicalMat_borelGraph {q : SpecialLinearGroup (Fin (c + 4)) F}
    (hq : IsBlockRadicalMat c F (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) :
    IsBlockRadicalMat c F
      ((borelGraph (c + 4) F q : SpecialLinearGroup (Fin (c + 4)) F) :
        Matrix (Fin (c + 4)) (Fin (c + 4)) F) := by
  have hqQ : q ∈ blockRadical222 c F := (mem_blockRadical222_iff (c := c) (F := F)).mpr hq
  have hqinv : q⁻¹ ∈ blockRadical222 c F := (blockRadical222 c F).inv_mem hqQ
  obtain ⟨hupper, hdiag, hblock⟩ := (mem_blockRadical222_iff (c := c) (F := F)).mp hqinv
  refine ⟨?_, ?_, ?_⟩
  · intro i j hji
    rw [coe_borelGraph_apply]
    refine hupper _ _ ?_
    rw [Fin.rev_lt_rev]
    exact hji
  · intro i
    rw [coe_borelGraph_apply]
    exact hdiag _
  · intro i j hij hij'
    rw [coe_borelGraph_apply]
    refine hblock _ _ (blk222_rev_eq c hij).symm ?_
    intro h
    exact hij' (Fin.rev_injective h).symm


theorem isBlockRadicalMat_slConjugation (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A)
    {q : SpecialLinearGroup (Fin (c + 4)) F}
    (hq : IsBlockRadicalMat c F (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) :
    IsBlockRadicalMat c F
      ((CatalogueBHigherLinearAction.slConjugation (c + 4) F A q :
        SpecialLinearGroup (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F) := by
  obtain ⟨B, E, hqdec⟩ := exists_reindex_eq_upForm_of_isBlockRadicalMat (c := c) (F := F) hq
  let R := Matrix.reindexAlgEquiv F F (e222 c).symm
  have hAdec := reindexAlgEquiv_eq_fromBlocks' c F A hA
  have hAinvdec := reindexAlgEquiv_eq_fromBlocks' c F A⁻¹ (isUpperGL_inv (F := F) (A := A) hA)
  let A1 : Matrix (Fin 2) (Fin 2) F := blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A12 : Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
    blockMat12 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A2 : Matrix (Fin c) (Fin c) F :=
    blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A23 : Matrix (Fin c) (Fin 2) F :=
    blockMat22b c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A3 : Matrix (Fin 2) (Fin 2) F :=
    blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A1i : Matrix (Fin 2) (Fin 2) F :=
    blockMat11 c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A12i : Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
    blockMat12 c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A2i : Matrix (Fin c) (Fin c) F :=
    blockMat22a c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A23i : Matrix (Fin c) (Fin 2) F :=
    blockMat22b c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let A3i : Matrix (Fin 2) (Fin 2) F :=
    blockMat33 c F ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let U : Matrix (Fin 2 ⊕ (Fin c ⊕ Fin 2)) (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F :=
    Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) B 0
      (Matrix.fromBlocks (1 : Matrix (Fin c) (Fin c) F) E (0 : Matrix (Fin 2) (Fin c) F)
        (1 : Matrix (Fin 2) (Fin 2) F))
  let Bnew : Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
    A1 * A12i + (A1 * B + A12 * Matrix.fromBlocks (1 : Matrix (Fin c) (Fin c) F) E
      (0 : Matrix (Fin 2) (Fin c) F) (1 : Matrix (Fin 2) (Fin 2) F)) *
      Matrix.fromBlocks A2i A23i (0 : Matrix (Fin 2) (Fin c) F) A3i
  let Enew : Matrix (Fin c) (Fin 2) F :=
    A2 * A23i + (A2 * E + A23) * A3i
  have hmem : CatalogueBHigherLinearAction.slConjugation (c + 4) F A q ∈
      blockRadical222 c F := by
    refine mem_blockRadical222_of_reindex_eq_upForm (c := c) (F := F) (B := Bnew) (E := Enew) ?_
    rw [LinearFlag.coe_slConjugation]
    change R ((A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
        (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) *
        ((A⁻¹ : GL (Fin (c + 4)) F) : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) =
      upFormMat c F Bnew Enew
    rw [map_mul, map_mul, hAdec, hqdec, hAinvdec]
    simp only [upFormMat, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      blockMat11_mul_blockMat11_inv c F A hA,
      blockMat22a_mul_blockMat22a_inv c F A hA,
      blockMat33_mul_blockMat33_inv c F A hA, Bnew, Enew,
      A1, A12, A2, A23, A12i, A2i, A23i, A3i]
  exact (mem_blockRadical222_iff (c := c) (F := F)).mp hmem



theorem map_slFieldAut_blockRadical222 (σ : F ≃+* F) :
    (blockRadical222 c F).map
        (CatalogueBHigherLinearField.slFieldAut (Fin (c + 4)) F σ).toMonoidHom =
      blockRadical222 c F := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact (mem_blockRadical222_iff (c := c) (F := F)).mpr
      (isBlockRadicalMat_slFieldAut c F σ ((mem_blockRadical222_iff (c := c) (F := F)).mp hq))
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨
      CatalogueBHigherLinearField.slFieldAut (Fin (c + 4)) F σ⁻¹ q, ?_, ?_⟩
    · exact (mem_blockRadical222_iff (c := c) (F := F)).mpr
        (isBlockRadicalMat_slFieldAut c F σ⁻¹ ((mem_blockRadical222_iff (c := c) (F := F)).mp hq))
    · have hcomp : CatalogueBHigherLinearField.slFieldAut (Fin (c + 4)) F σ *
          CatalogueBHigherLinearField.slFieldAut (Fin (c + 4)) F σ⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      simp

theorem map_slConjugation_blockRadical222 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A) :
    (blockRadical222 c F).map
        (CatalogueBHigherLinearAction.slConjugation (c + 4) F A).toMonoidHom =
      blockRadical222 c F := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact (mem_blockRadical222_iff (c := c) (F := F)).mpr
      (isBlockRadicalMat_slConjugation c F A hA
        ((mem_blockRadical222_iff (c := c) (F := F)).mp hq))
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨
      CatalogueBHigherLinearAction.slConjugation (c + 4) F A⁻¹ q, ?_, ?_⟩
    · exact (mem_blockRadical222_iff (c := c) (F := F)).mpr
        (isBlockRadicalMat_slConjugation c F A⁻¹ (isUpperGL_inv (F := F) (A := A) hA)
          ((mem_blockRadical222_iff (c := c) (F := F)).mp hq))
    · have hcomp : CatalogueBHigherLinearAction.slConjugation (c + 4) F A *
          CatalogueBHigherLinearAction.slConjugation (c + 4) F A⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      simp

theorem map_borelGraph_blockRadical222 :
    (blockRadical222 c F).map (borelGraph (c + 4) F).toMonoidHom =
      blockRadical222 c F := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro q hq
    exact (mem_blockRadical222_iff (c := c) (F := F)).mpr
      (isBlockRadicalMat_borelGraph c F ((mem_blockRadical222_iff (c := c) (F := F)).mp hq))
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨borelGraph (c + 4) F q, ?_, ?_⟩
    · exact (mem_blockRadical222_iff (c := c) (F := F)).mpr
        (isBlockRadicalMat_borelGraph c F ((mem_blockRadical222_iff (c := c) (F := F)).mp hq))
    · simpa [MulAut.mul_apply] using
        congrArg (fun f => f q) (borelGraph_mul_self (c + 4) (F := F))

theorem map_borelGraph_pow_blockRadical222 (ε : ℕ) :
    (blockRadical222 c F).map ((borelGraph (c + 4) F) ^ ε).toMonoidHom =
      blockRadical222 c F := by
  induction ε with
  | zero =>
      rw [pow_zero]
      rw [show MulEquiv.toMonoidHom (1 : MulAut (SpecialLinearGroup (Fin (c + 4)) F)) =
          MonoidHom.id _ from MonoidHom.ext fun x => MulAut.one_apply _ x]
      rw [Subgroup.map_id]
  | succ n ih =>
      rw [pow_succ]
      rw [show (((borelGraph (c + 4) F) ^ n * borelGraph (c + 4) F)).toMonoidHom =
          ((borelGraph (c + 4) F) ^ n).toMonoidHom.comp
            (borelGraph (c + 4) F).toMonoidHom from rfl]
      rw [← Subgroup.map_map, map_borelGraph_blockRadical222 c F, ih]

theorem map_stdAut_zero_blockRadical222 (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) :
    (blockRadical222 c F).map
        (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom =
      blockRadical222 c F := by
  rw [show (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom =
      (CatalogueBHigherLinearAction.slConjugation (c + 4) F A).toMonoidHom.comp
        (CatalogueBHigherLinearField.slFieldAut (Fin (c + 4)) F σ).toMonoidHom from by
    rw [CFSG.QuasithinUnique.K1.stdAut, pow_zero, mul_one]
    rfl,
    ← Subgroup.map_map, map_slFieldAut_blockRadical222 c F σ,
    map_slConjugation_blockRadical222 c F A hA]

theorem blockRadical222_map_borelStd (A : GL (Fin (c + 4)) F) (hA : IsUpperGL A)
    (σ : F ≃+* F) (ε : ℕ) :
    (blockRadical222 c F).map (borelStd (c + 4) F A σ ε).toMonoidHom =
      blockRadical222 c F := by
  rw [borelStd]
  rw [show ((CFSG.QuasithinUnique.K1.stdAut A σ 0 * borelGraph (c + 4) F ^ ε)).toMonoidHom =
      (CFSG.QuasithinUnique.K1.stdAut A σ 0).toMonoidHom.comp
        ((borelGraph (c + 4) F ^ ε)).toMonoidHom from rfl]
  rw [← Subgroup.map_map, map_borelGraph_pow_blockRadical222 c F ε,
    map_stdAut_zero_blockRadical222 c F A hA σ]


end

end CFSG.LieType.SpecialLinear
