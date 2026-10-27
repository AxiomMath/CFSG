module

public import CFSG.GH74.L5U5.ModelsInvolution
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_apply_blockIdx blockIdx)
open scoped MatrixGroups

section BlockMat

variable {F : Type} [Field F]

theorem e4_symm_zero : e4.symm (0 : Fin 4) = Sum.inl 0 := rfl

theorem e4_symm_one : e4.symm (1 : Fin 4) = Sum.inl 1 := rfl

theorem e4_symm_two : e4.symm (2 : Fin 4) = Sum.inr 0 := rfl

theorem e4_symm_three : e4.symm (3 : Fin 4) = Sum.inr 1 := rfl

theorem blk4_apply (X Y : Matrix (Fin 2) (Fin 2) F) (a b : Fin 4) :
    blk4 X Y a b = fromBlocks X 0 0 Y (e4.symm a) (e4.symm b) := rfl

theorem blockMat_four_zero (A : Matrix (Fin 2) (Fin 2) F) : blockMat 4 0 A = blk4 A 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, blk4_apply, e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three]

theorem blockMat_four_two (A : Matrix (Fin 2) (Fin 2) F) : blockMat 4 2 A = blk4 1 A := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, blk4_apply, e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three]

end BlockMat

section Transport

variable {F : Type} [Field F]

theorem linearBlockStandardPair_map' {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    LinearBlockStandardPair F (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem weakCTSystem_map_equiv {X Y : Type} [Group X] [Group Y] {n : ℕ}
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (h : WeakCTSystem F n U W)
    (e : X ≃* Y) :
    WeakCTSystem F n (fun i => (U i).map e.toMonoidHom)
      (fun i j => (W i j).map e.toMonoidHom) where
  iso i := by
    obtain ⟨φ⟩ := h.iso i
    exact ⟨φ.trans ((U i).equivMapOfInjective e.toMonoidHom e.injective)⟩
  join i j hij := by rw [h.join i j hij, Subgroup.map_sup]
  comm i j hij := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h.comm i j hij x hx y hy]
  pair i j hj := linearBlockStandardPair_map' (h.pair i j hj) e.toMonoidHom e.injective
  gen := by
    rw [← Subgroup.map_iSup, h.gen]
    exact Subgroup.map_top_of_surjective _ e.surjective

end Transport

section Linear

variable {F : Type} [Field F]

theorem coe_equiv_blockSL2_zero (A : SL(2, F)) :
    ((specialLinearGroupEquivStatedSL 4 F (blockSL2 F 3 0 A) : ↥(StatedSL 4 F)) :
      GL (Fin 4) F) = blkL F (SpecialLinearGroup.toGL A) := by
  apply Units.ext
  change ((blockSL F 4 2 0 (by omega) A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = _
  rw [coe_blockSL, blockMat_four_zero]
  rfl

theorem coe_equiv_blockSL2_two (A : SL(2, F)) :
    ((specialLinearGroupEquivStatedSL 4 F (blockSL2 F 3 2 A) : ↥(StatedSL 4 F)) :
      GL (Fin 4) F) = blkR F (SpecialLinearGroup.toGL A) := by
  apply Units.ext
  change ((blockSL F 4 2 2 (by omega) A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = _
  rw [coe_blockSL, blockMat_four_two]
  rfl

theorem toGL_mem_lin_H2 (A : SL(2, F)) : SpecialLinearGroup.toGL A ∈ (ModelData.lin F).H2 :=
  ((ModelData.lin F).mem_H2 _).2 ⟨Subgroup.mem_top _, A.2⟩

theorem exists_toGL_of_mem_lin_H2 {a : GL (Fin 2) F} (ha : a ∈ (ModelData.lin F).H2) :
    ∃ A : SL(2, F), SpecialLinearGroup.toGL A = a :=
  ⟨⟨(a : Matrix (Fin 2) (Fin 2) F), ((ModelData.lin F).mem_H2 a |>.1 ha).2⟩, Units.ext rfl⟩

theorem lin_J2_eq :
    (ModelData.lin F).J2 =
      (blockSL2 F 3 0).range.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, hga⟩ := ModelData.mem_J2.1 hg
    obtain ⟨A, rfl⟩ := exists_toGL_of_mem_lin_H2 ha
    refine Subgroup.mem_map.2 ⟨blockSL2 F 3 0 A, ⟨A, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((specialLinearGroupEquivStatedSL 4 F (blockSL2 F 3 0 A) : ↥(StatedSL 4 F)) :
      GL (Fin 4) F) = _
    rw [coe_equiv_blockSL2_zero, hga]
  · intro hg
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
    refine ModelData.mem_J2.2 ⟨SpecialLinearGroup.toGL A, toGL_mem_lin_H2 A, ?_⟩
    exact coe_equiv_blockSL2_zero A

theorem lin_J4_eq :
    (ModelData.lin F).J4 =
      (blockSL2 F 3 2).range.map (specialLinearGroupEquivStatedSL 4 F).toMonoidHom := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, hga⟩ := ModelData.mem_J4.1 hg
    obtain ⟨A, rfl⟩ := exists_toGL_of_mem_lin_H2 ha
    refine Subgroup.mem_map.2 ⟨blockSL2 F 3 2 A, ⟨A, rfl⟩, ?_⟩
    apply Subtype.ext
    change ((specialLinearGroupEquivStatedSL 4 F (blockSL2 F 3 2 A) : ↥(StatedSL 4 F)) :
      GL (Fin 4) F) = _
    rw [coe_equiv_blockSL2_two, hga]
  · intro hg
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
    refine ModelData.mem_J4.2 ⟨SpecialLinearGroup.toGL A, toGL_mem_lin_H2 A, ?_⟩
    exact coe_equiv_blockSL2_two A

end Linear

section Middle

variable {F : Type} [Field F]

theorem blockMat_neg_one_eq_diagonal (m j : ℕ) :
    blockMat m j (-1 : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal (fun a : Fin m => if j ≤ a.val ∧ a.val < j + 2 then (-1 : F) else 1) := by
  ext a b
  rw [blockMat_apply, Matrix.diagonal_apply]
  by_cases hb : (j ≤ a.val ∧ a.val < j + 2) ∧ (j ≤ b.val ∧ b.val < j + 2)
  · rw [dite_eq_left hb]
    by_cases hab : a = b
    · subst hab
      simp [hb.1]
    · have : (⟨a.val - j, by omega⟩ : Fin 2) ≠ ⟨b.val - j, by omega⟩ := by
        intro h
        apply hab
        apply Fin.ext
        have := congrArg Fin.val h
        simp only at this
        omega
      simp [hab, this]
  · rw [dite_eq_right hb]
    by_cases hab : a = b
    · subst hab
      have : ¬ (j ≤ a.val ∧ a.val < j + 2) := fun h => hb ⟨h, h⟩
      simp [this]
    · simp [hab]

theorem blockMat_neg_one_comm (m i j : ℕ) :
    blockMat m i (-1 : Matrix (Fin 2) (Fin 2) F) * blockMat m j (-1 : Matrix (Fin 2) (Fin 2) F) =
      blockMat m j (-1 : Matrix (Fin 2) (Fin 2) F) *
        blockMat m i (-1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [blockMat_neg_one_eq_diagonal, blockMat_neg_one_eq_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem coe_neg_one_sl2 : ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]

theorem blockSL2_neg_one_comm (i j : Fin 3) :
    blockSL2 F 3 i (-1) * blockSL2 F 3 j (-1) = blockSL2 F 3 j (-1) * blockSL2 F 3 i (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change blockMat 4 i ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      blockMat 4 j ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    blockMat 4 j ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      blockMat 4 i ((-1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  rw [coe_neg_one_sl2]
  exact blockMat_neg_one_comm 4 i j

@[expose] def elem12 : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_blockSL2_zero (A : SL(2, F)) :
    ((blockSL2 F 3 0 A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blockMat 4 0 (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem coe_blockSL2_one (A : SL(2, F)) :
    ((blockSL2 F 3 1 A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blockMat 4 1 (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem coe_blockSL2_two (A : SL(2, F)) :
    ((blockSL2 F 3 2 A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      blockMat 4 2 (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem blockMat_zero_neg_one_not_comm (h2 : (2 : F) ≠ 0) (A : Matrix (Fin 2) (Fin 2) F)
    (hA : A 0 1 = 1) :
    blockMat 4 0 (-1 : Matrix (Fin 2) (Fin 2) F) * blockMat 4 1 A ≠
      blockMat 4 1 A * blockMat 4 0 (-1 : Matrix (Fin 2) (Fin 2) F) := by
  intro h
  have h' := congrFun (congrFun h 1) 2
  rw [blockMat_neg_one_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] at h'
  have e12 : blockMat 4 1 A 1 2 = 1 := by
    have := blockMat_apply_blockIdx (m := 4) (i := 1) (k := 2) (by omega) A 0 1
    exact this.trans hA
  rw [e12] at h'
  simp at h'
  exact h2 (by linear_combination (-1 : F) * h')

theorem blockSL2_zero_neg_one_not_comm (h2 : (2 : F) ≠ 0) :
    blockSL2 F 3 0 (-1) * blockSL2 F 3 1 elem12 ≠ blockSL2 F 3 1 elem12 * blockSL2 F 3 0 (-1) := by
  intro h
  have h' := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_zero, coe_blockSL2_one,
    coe_neg_one_sl2] at h'
  exact blockMat_zero_neg_one_not_comm h2 _ (by simp [elem12]) h'

end Middle

section SystemLin

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem toGL_neg_one_sl2 : (SpecialLinearGroup.toGL (-1 : SL(2, F))) = (-1 : GL (Fin 2) F) := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_neg_one_sl2, Units.val_neg, Units.val_one]

omit [Finite F] in
theorem equiv_blockSL2_zero_neg_one :
    specialLinearGroupEquivStatedSL 4 F (blockSL2 F 3 0 (-1)) = (ModelData.lin F).yK := by
  apply Subtype.ext
  rw [coe_equiv_blockSL2_zero, toGL_neg_one_sl2]
  rfl

theorem comm_of_center {K : Type} [Group K] {x y z : K} (hx : x ∈ Subgroup.center K)
    (h : y * z = z * y) : x * y * z = z * (x * y) := by
  have hz : z * x = x * z := Subgroup.mem_center_iff.1 hx z
  calc x * y * z = x * (y * z) := mul_assoc _ _ _
    _ = x * (z * y) := by rw [h]
    _ = (x * z) * y := (mul_assoc _ _ _).symm
    _ = (z * x) * y := by rw [hz]
    _ = z * (x * y) := mul_assoc _ _ _

theorem exists_system_lin {K : Type} [Group K] (hF : Nat.card F % 4 = 3)
    (e : K ≃* StatedSL 4 F) :
    ∃ (x y z₃ : K) (J₂ J₃ J₄ : Subgroup K) (U : Fin 3 → Subgroup K)
      (W : Fin 3 → Fin 3 → Subgroup K),
      IsFrame F x y J₂ J₄ ∧ WeakCTSystem F 3 U W ∧ U 0 = J₂ ∧ U 1 = J₃ ∧ U 2 = J₄ ∧
      z₃ ∈ J₃ ∧ orderOf z₃ = 2 ∧ y * z₃ = z₃ * y ∧ x * y * z₃ = z₃ * (x * y) ∧
      ¬ (∀ b ∈ J₃, y * b = b * y) := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 := two_ne_zero_of_odd_card (F := F) hodd
  have hfr := isFrame_of_model (ModelData.lin F) h2 e (lin_sl2_equiv_H2 F)
  let Φ : SL(4, F) ≃* K := (specialLinearGroupEquivStatedSL 4 F).trans e.symm
  have hsys := weakCTSystem_map_equiv (weakCTSystem_standard (K := F) 3) Φ
  have hy : e.symm (ModelData.lin F).yK = Φ (blockSL2 F 3 0 (-1)) := by
    change e.symm _ = e.symm (specialLinearGroupEquivStatedSL 4 F (blockSL2 F 3 0 (-1)))
    rw [equiv_blockSL2_zero_neg_one]
  have hcomm₃ : e.symm (ModelData.lin F).yK * Φ (blockSL2 F 3 1 (-1)) =
      Φ (blockSL2 F 3 1 (-1)) * e.symm (ModelData.lin F).yK := by
    rw [hy, ← map_mul, ← map_mul, blockSL2_neg_one_comm 0 1]
  refine ⟨e.symm (ModelData.lin F).xK, e.symm (ModelData.lin F).yK, Φ (blockSL2 F 3 1 (-1)),
    (ModelData.lin F).J2.map e.symm.toMonoidHom, (blockSL2 F 3 1).range.map Φ.toMonoidHom,
    (ModelData.lin F).J4.map e.symm.toMonoidHom, fun i => (blockSL2 F 3 i).range.map Φ.toMonoidHom,
    fun i j => ((blockSL2 F 3 i).range ⊔ (blockSL2 F 3 j).range).map Φ.toMonoidHom,
    hfr, hsys, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (blockSL2 F 3 0).range.map Φ.toMonoidHom = _
    rw [lin_J2_eq, Subgroup.map_map]
    rfl
  · change (blockSL2 F 3 2).range.map Φ.toMonoidHom = _
    rw [lin_J4_eq, Subgroup.map_map]
    rfl
  · exact Subgroup.mem_map.2 ⟨blockSL2 F 3 1 (-1), ⟨-1, rfl⟩, rfl⟩
  · rw [MulEquiv.orderOf_eq, orderOf_injective _ (blockSL2_injective 3 1)]
    exact CFSG.ClassicalInvolution.sl2_orderOf_neg_one hodd
  · exact hcomm₃
  · exact comm_of_center hfr.x_mem_center hcomm₃
  · intro hall
    have hb : Φ (blockSL2 F 3 1 elem12) ∈ (blockSL2 F 3 1).range.map Φ.toMonoidHom :=
      Subgroup.mem_map.2 ⟨blockSL2 F 3 1 elem12, ⟨elem12, rfl⟩, rfl⟩
    have := hall _ hb
    rw [hy, ← map_mul, ← map_mul] at this
    exact blockSL2_zero_neg_one_not_comm h2 (Φ.injective this)

end SystemLin

section StandardPairThree

variable {F : Type} [Field F]

theorem exists_standard_pair_lin {K₃ : Type} [Group K₃] (e : K₃ ≃* StatedSL 3 F) :
    ∃ J_a J_b : Subgroup K₃, J_a ⊔ J_b = ⊤ ∧ LinearBlockStandardPair F (J_a ⊔ J_b) J_a J_b ∧
      Nonempty (SL(2, F) ≃* J_a) ∧ Nonempty (SL(2, F) ≃* J_b) := by
  let Φ : SL(3, F) ≃* K₃ := (specialLinearGroupEquivStatedSL 3 F).trans e.symm
  have hsys := weakCTSystem_map_equiv (weakCTSystem_standard (K := F) 2) Φ
  refine ⟨(blockSL2 F 2 0).range.map Φ.toMonoidHom, (blockSL2 F 2 1).range.map Φ.toMonoidHom,
    ?_, ?_, hsys.iso 0, hsys.iso 1⟩
  · rw [← Subgroup.map_sup]
    have hgen : (blockSL2 F 2 0).range ⊔ (blockSL2 F 2 1).range = ⊤ := B12_sup_B23
    rw [hgen]
    exact Subgroup.map_top_of_surjective _ Φ.surjective
  · have h01 := hsys.pair 0 1 rfl
    have hj := hsys.join 0 1 (by decide)
    rw [hj] at h01
    exact h01

end StandardPairThree

end CFSG.GH74.L5U5
