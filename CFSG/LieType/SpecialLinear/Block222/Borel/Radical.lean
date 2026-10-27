module

public import CFSG.LieType.SpecialLinear.Block222.Radicals
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.LieType.SpecialLinear.Block222.Borel.Blocks

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag.BinaryParabolic

noncomputable section

variable (c : ℕ) (F : Type) [Field F]

abbrev upUnitMat (E : Matrix (Fin c) (Fin 2) F) :
    Matrix (Fin c ⊕ Fin 2) (Fin c ⊕ Fin 2) F :=
  Matrix.fromBlocks (1 : Matrix (Fin c) (Fin c) F) E (0 : Matrix (Fin 2) (Fin c) F)
    (1 : Matrix (Fin 2) (Fin 2) F)

theorem upUnitMat_mul (E E' : Matrix (Fin c) (Fin 2) F) :
    upUnitMat c F E * upUnitMat c F E' = upUnitMat c F (E' + E) := by
  rw [upUnitMat, upUnitMat, upUnitMat, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero]

theorem upFormMat_mul (B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F) (E : Matrix (Fin c) (Fin 2) F)
    (B' : Matrix (Fin 2) (Fin c ⊕ Fin 2) F) (E' : Matrix (Fin c) (Fin 2) F) :
    upFormMat c F B E * upFormMat c F B' E' =
      upFormMat c F (B' + B * upUnitMat c F E') (E' + E) := by
  rw [upFormMat, upFormMat, upFormMat, Matrix.fromBlocks_multiply]
  rw [show upUnitMat c F E * upUnitMat c F E' = upUnitMat c F (E' + E)
    from upUnitMat_mul c F E E']
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
    add_zero]

theorem upFormSL_mul (B E B' E') :
    upFormSL c F B E * upFormSL c F B' E' =
      upFormSL c F (B' + B * upUnitMat c F E') (E' + E) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_upFormSL, coe_upFormSL, coe_upFormSL]
  exact upFormMat_mul c F B E B' E'

theorem upFormSL_zero : upFormSL c F 0 0 = 1 := by
  apply Subtype.ext
  rw [coe_upFormSL, Matrix.SpecialLinearGroup.coe_one]
  ext x y
  rcases x with a | (s | k) <;> rcases y with b | (t | l) <;>
    simp [upFormMat, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]

theorem upFormSL_inv (B E) :
    (upFormSL c F B E)⁻¹ = upFormSL c F (-(B * upUnitMat c F (-E))) (-E) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [upFormSL_mul]
  have hB : -(B * upUnitMat c F (-E)) + B * upUnitMat c F (-E) = 0 := neg_add_cancel _
  have hE : -E + E = 0 := neg_add_cancel E
  rw [hB, hE, upFormSL_zero]

theorem mem_blockRadicalSum222_iff {x : SpecialLinearGroup (Fin 2 ⊕ (Fin c ⊕ Fin 2)) F} :
    x ∈ blockRadicalSum222 c F ↔ ∃ B E, x = upFormSL c F B E := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun y _ => ∃ B E, y = upFormSL c F B E) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨B, E, rfl⟩
      exact ⟨B, E, rfl⟩
    · exact ⟨0, 0, (upFormSL_zero c F).symm⟩
    · rintro x y _ _ ⟨B, E, rfl⟩ ⟨B', E', rfl⟩
      exact ⟨_, _, upFormSL_mul c F B E B' E'⟩
    · rintro x _ ⟨B, E, rfl⟩
      exact ⟨_, _, upFormSL_inv c F B E⟩
  · rintro ⟨B, E, rfl⟩
    exact upFormSL_mem c F B E

theorem mem_blockRadical222_iff_upForm {x : SpecialLinearGroup (Fin (c + 4)) F} :
    x ∈ blockRadical222 c F ↔
      ∃ B E, x = reindexSL c F (upFormSL c F B E) := by
  rw [blockRadical222, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨B, E, rfl⟩ := (mem_blockRadicalSum222_iff c F).mp hy
    exact ⟨B, E, rfl⟩
  · rintro ⟨B, E, rfl⟩
    exact ⟨upFormSL c F B E, upFormSL_mem c F B E, rfl⟩

@[expose] def IsBlockRadicalMat (M : Matrix (Fin (c + 4)) (Fin (c + 4)) F) : Prop :=
  (∀ i j : Fin (c + 4), j < i → M i j = 0) ∧
    (∀ i : Fin (c + 4), M i i = 1) ∧
      (∀ i j : Fin (c + 4), blk222 c i = blk222 c j → i ≠ j → M i j = 0)

variable {c F}

theorem blockMat11_eq_one {M : Matrix (Fin (c + 4)) (Fin (c + 4)) F}
    (hdiag : ∀ i, M i i = 1)
    (hblock : ∀ i j, blk222 c i = blk222 c j → i ≠ j → M i j = 0) :
    blockMat11 c F M = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    exact hdiag _
  · rw [Matrix.one_apply_ne hij]
    exact hblock _ _ (by rw [blk222_e222, blk222_e222]; rfl) (by
      intro h; exact hij (Sum.inl_injective ((e222 c).injective h)))

theorem blockMat22a_eq_one {M : Matrix (Fin (c + 4)) (Fin (c + 4)) F}
    (hdiag : ∀ i, M i i = 1)
    (hblock : ∀ i j, blk222 c i = blk222 c j → i ≠ j → M i j = 0) :
    blockMat22a c F M = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    exact hdiag _
  · rw [Matrix.one_apply_ne hij]
    exact hblock _ _ (by rw [blk222_e222, blk222_e222]; rfl) (by
      intro h; exact hij (Sum.inl_injective (Sum.inr_injective ((e222 c).injective h))))

theorem blockMat33_eq_one {M : Matrix (Fin (c + 4)) (Fin (c + 4)) F}
    (hdiag : ∀ i, M i i = 1)
    (hblock : ∀ i j, blk222 c i = blk222 c j → i ≠ j → M i j = 0) :
    blockMat33 c F M = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq]
    exact hdiag _
  · rw [Matrix.one_apply_ne hij]
    exact hblock _ _ (by rw [blk222_e222, blk222_e222]; rfl) (by
      intro h; exact hij (Sum.inr_injective (Sum.inr_injective ((e222 c).injective h))))




section Characterization

variable {c : ℕ} {F : Type} [Field F]

theorem mem_blockRadical222_iff {x : SpecialLinearGroup (Fin (c + 4)) F} :
    x ∈ blockRadical222 c F ↔ IsBlockRadicalMat c F (x : Matrix (Fin (c + 4)) (Fin (c + 4)) F) := by
  constructor
  · intro hx
    obtain ⟨B, E, rfl⟩ := (mem_blockRadical222_iff_upForm c F).mp hx
    refine ⟨?_, ?_, ?_⟩
    · intro i j hji
      rw [reindexSL_apply]
      refine upFormSL_off c F B E ?_ ?_
      · have hle : blkSum222 c ((e222 c).symm i) ≥ blkSum222 c ((e222 c).symm j) := by
          rw [show blkSum222 c ((e222 c).symm i) = blk222 c i from
              (blk222_e222 c ((e222 c).symm i)).symm.trans (by rw [Equiv.apply_symm_apply]),
            show blkSum222 c ((e222 c).symm j) = blk222 c j from
              (blk222_e222 c ((e222 c).symm j)).symm.trans (by rw [Equiv.apply_symm_apply])]
          exact blk222_le_of_le (c := c) (le_of_lt hji)
        exact hle
      · intro h
        exact absurd ((e222 c).symm.injective h) (ne_of_gt hji)
    · intro i
      rw [reindexSL_apply]
      exact upFormSL_diag c F B E _
    · intro i j hblk hij
      rw [reindexSL_apply]
      refine upFormSL_off c F B E ?_ ?_
      · have hle : blkSum222 c ((e222 c).symm i) = blkSum222 c ((e222 c).symm j) := by
          rw [show blkSum222 c ((e222 c).symm i) = blk222 c i from
              (blk222_e222 c ((e222 c).symm i)).symm.trans (by rw [Equiv.apply_symm_apply]),
            show blkSum222 c ((e222 c).symm j) = blk222 c j from
              (blk222_e222 c ((e222 c).symm j)).symm.trans (by rw [Equiv.apply_symm_apply])]
          exact hblk
        exact le_of_eq hle.symm
      · intro h
        exact absurd ((e222 c).symm.injective h) hij
  · rintro ⟨hupper, hdiag, hblock⟩
    let A : GL (Fin (c + 4)) F := Matrix.SpecialLinearGroup.toGL x
    have hA : IsUpperGL A := hupper
    have hdec := reindexAlgEquiv_eq_fromBlocks' c F A hA
    have hAval : (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
        (x : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :=
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix x
    have h11 : blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
      refine blockMat11_eq_one (c := c) ?_ ?_
      · intro i; rw [hAval]; exact hdiag i
      · intro i j hij hij'; rw [hAval]; exact hblock i j hij hij'
    have h22a : blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
      refine blockMat22a_eq_one (c := c) ?_ ?_
      · intro i; rw [hAval]; exact hdiag i
      · intro i j hij hij'; rw [hAval]; exact hblock i j hij hij'
    have h33 : blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
      refine blockMat33_eq_one (c := c) ?_ ?_
      · intro i; rw [hAval]; exact hdiag i
      · intro i j hij hij'; rw [hAval]; exact hblock i j hij hij'
    let B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
      blockMat12 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
    let E : Matrix (Fin c) (Fin 2) F :=
      blockMat22b c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
    have hup : upFormMat c F B E =
        (Matrix.reindexAlgEquiv F F (e222 c).symm)
          (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) := by
      rw [hdec]
      simp only [upFormMat, h11, h22a, h33, B, E]
    have hxeq : x = reindexSL c F (upFormSL c F B E) := by
      apply Subtype.ext
      rw [coe_reindexSL]
      calc (x : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
          = (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) := hAval.symm
        _ = (Matrix.reindexAlgEquiv F F (e222 c))
              ((Matrix.reindexAlgEquiv F F (e222 c).symm)
                (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) :=
            (AlgEquiv.apply_symm_apply _ _).symm
        _ = (Matrix.reindexAlgEquiv F F (e222 c)) (upFormMat c F B E) := by rw [hup]
    exact (mem_blockRadical222_iff_upForm c F).mpr ⟨B, E, hxeq⟩


section Reindex

theorem exists_reindex_eq_upForm_of_isBlockRadicalMat
    {q : SpecialLinearGroup (Fin (c + 4)) F}
    (hq : IsBlockRadicalMat c F (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) :
    ∃ B E, (Matrix.reindexAlgEquiv F F (e222 c).symm)
        (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = upFormMat c F B E := by
  obtain ⟨hupper, hdiag, hblock⟩ := hq
  let A : GL (Fin (c + 4)) F := Matrix.SpecialLinearGroup.toGL q
  have hA : IsUpperGL A := hupper
  have hdec := reindexAlgEquiv_eq_fromBlocks' c F A hA
  have hAval : (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) =
      (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) :=
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix q
  have h11 : blockMat11 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
    refine blockMat11_eq_one (c := c) ?_ ?_
    · intro i; rw [hAval]; exact hdiag i
    · intro i j hij hij'; rw [hAval]; exact hblock i j hij hij'
  have h22a : blockMat22a c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
    refine blockMat22a_eq_one (c := c) ?_ ?_
    · intro i; rw [hAval]; exact hdiag i
    · intro i j hij hij'; rw [hAval]; exact hblock i j hij hij'
  have h33 : blockMat33 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = 1 := by
    refine blockMat33_eq_one (c := c) ?_ ?_
    · intro i; rw [hAval]; exact hdiag i
    · intro i j hij hij'; rw [hAval]; exact hblock i j hij hij'
  let B : Matrix (Fin 2) (Fin c ⊕ Fin 2) F :=
    blockMat12 c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  let E : Matrix (Fin c) (Fin 2) F :=
    blockMat22b c F (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
  have hup : upFormMat c F B E =
      (Matrix.reindexAlgEquiv F F (e222 c).symm)
        (A : Matrix (Fin (c + 4)) (Fin (c + 4)) F) := by
    rw [hdec]
    simp only [upFormMat, h11, h22a, h33, B, E]
  refine ⟨B, E, ?_⟩
  rw [← hAval, ← hup]

theorem mem_blockRadical222_of_reindex_eq_upForm {q : SpecialLinearGroup (Fin (c + 4)) F}
    {B E} (h : (Matrix.reindexAlgEquiv F F (e222 c).symm)
        (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F) = upFormMat c F B E) :
    q ∈ blockRadical222 c F := by
  refine (mem_blockRadical222_iff_upForm c F).mpr ⟨B, E, ?_⟩
  apply Subtype.ext
  rw [coe_reindexSL]
  calc (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F)
      = (Matrix.reindexAlgEquiv F F (e222 c))
          ((Matrix.reindexAlgEquiv F F (e222 c).symm)
            (q : Matrix (Fin (c + 4)) (Fin (c + 4)) F)) :=
        (AlgEquiv.apply_symm_apply _ _).symm
    _ = (Matrix.reindexAlgEquiv F F (e222 c)) (upFormMat c F B E) := by rw [h]

end Reindex


end Characterization

end

end CFSG.LieType.SpecialLinear
