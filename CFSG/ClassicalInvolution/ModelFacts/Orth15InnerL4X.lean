module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4Mat

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable (F : Type) [Field F]

@[expose] noncomputable def R0 : Subgroup SL(4, F) := (blockSL F 4 2 0 (by norm_num)).range

@[expose] noncomputable def R0' : Subgroup SL(4, F) := (blockSL F 4 2 2 (by norm_num)).range

@[expose] noncomputable def x0 : SL(4, F) := rootInv F (show 2 ≤ 4 by norm_num)

@[expose] noncomputable def u0 : SL(4, F) :=
  blockSL F 4 2 0 (by norm_num) r0 * blockSL F 4 2 2 (by norm_num) r0

@[expose] def zneg : SL(4, F) := ⟨-1, by rw [Matrix.det_neg, Matrix.det_one]; norm_num⟩

variable {F}

theorem coe_x0 : ((x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [x0, coe_rootInv, negBlock_four]

theorem coe_u0 : ((u0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [u0, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL, coe_r0, blockMat_four_zero,
    blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem coe_zneg : ((zneg F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := rfl

theorem zneg_mem_center : zneg F ∈ Subgroup.center SL(4, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num [Fintype.card_fin], ?_⟩
  rw [coe_zneg, Matrix.scalar_apply]
  ext i j
  by_cases h : i = j <;> simp [h]

theorem x0_mul_self : x0 F * x0 F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_x0, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem u0_mul_self : u0 F * u0 F = zneg F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_u0, coe_zneg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem x0_mul_u0 : x0 F * u0 F = u0 F * x0 F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_x0, coe_u0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem x0_inv : (x0 F)⁻¹ = x0 F := inv_eq_of_mul_eq_one_right x0_mul_self

theorem coe_x0_eq_negBlock : ((x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = negBlock F 4 0 :=
  coe_rootInv _

theorem negBlock_two_eq_neg : negBlock F 4 2 = -negBlock F 4 0 := by
  rw [negBlock_four_two, negBlock_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blockSL_comm (A B : SL(2, F)) :
    blockSL F 4 2 0 (by norm_num) A * blockSL F 4 2 2 (by norm_num) B =
      blockSL F 4 2 2 (by norm_num) B * blockSL F 4 2 0 (by norm_num) A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL,
    coe_blockSL, blockMat_four_zero, blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem R0_comm_R0' {a b : SL(4, F)} (ha : a ∈ R0 F) (hb : b ∈ R0' F) : a * b = b * a := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  exact blockSL_comm A B

theorem blockSL_zero_comm_x0 (A : SL(2, F)) :
    blockSL F 4 2 0 (by norm_num) A * x0 F = x0 F * blockSL F 4 2 0 (by norm_num) A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_x0, coe_blockSL,
    blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem blockSL_two_comm_x0 (A : SL(2, F)) :
    blockSL F 4 2 2 (by norm_num) A * x0 F = x0 F * blockSL F 4 2 2 (by norm_num) A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_x0, coe_blockSL,
    blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem R0_le_centralizer : R0 F ≤ Subgroup.centralizer ({x0 F} : Set SL(4, F)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (blockSL_zero_comm_x0 A).symm

theorem R0'_le_centralizer : R0' F ≤ Subgroup.centralizer ({x0 F} : Set SL(4, F)) := by
  rintro _ ⟨A, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (blockSL_two_comm_x0 A).symm

theorem x0_mem_R0 : x0 F ∈ R0 F := ⟨-1, rfl⟩

theorem u0_mem : u0 F ∈ R0 F ⊔ R0' F :=
  Subgroup.mul_mem_sup ⟨r0, rfl⟩ ⟨r0, rfl⟩

theorem conj_x0_cases {g : SL(4, F)}
    (hg : g * x0 F * g⁻¹ * (x0 F)⁻¹ ∈ Subgroup.center SL(4, F)) :
    g * x0 F * g⁻¹ = x0 F ∨ g * x0 F * g⁻¹ = zneg F * x0 F := by
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hyy : (g * x0 F * g⁻¹) * (g * x0 F * g⁻¹) = 1 := by
    calc (g * x0 F * g⁻¹) * (g * x0 F * g⁻¹) = g * (x0 F * x0 F) * g⁻¹ := by group
      _ = 1 := by rw [x0_mul_self]; group
  have hy : ((g * x0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      r • ((x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : ((g * x0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        ((g * x0 F * g⁻¹ * (x0 F)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
          ((x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [h1, ← hrA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hxx : ((x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
      ((x0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, x0_mul_self, Matrix.SpecialLinearGroup.coe_one]
  have hr2 : r * r = 1 := by
    have h1 : ((g * x0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
        ((g * x0 F * g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
          (r * r) • (1 : Matrix _ _ F) := by
      rw [hy, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, hyy, Matrix.SpecialLinearGroup.coe_one] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · left
    apply Subtype.ext
    rw [hy, hr1, one_smul]
  · right
    apply Subtype.ext
    rw [hy, hr1, neg_one_smul, Matrix.SpecialLinearGroup.coe_mul, coe_zneg, neg_one_mul]

theorem map_conj_fix (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g * x0 F * g⁻¹ = x0 F) :
    (R0 F).map (MulAut.conj g).toMonoidHom = R0 F ∧
      (R0' F).map (MulAut.conj g).toMonoidHom = R0' F := by
  have hm : (g : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 0 * ((g⁻¹ : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = negBlock F 4 0 := by
    rw [← coe_x0_eq_negBlock, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hg]
  have hm' : (g : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 2 * ((g⁻¹ : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = negBlock F 4 2 := by
    rw [negBlock_two_eq_neg, Matrix.mul_neg, Matrix.neg_mul, hm]
  refine ⟨?_, ?_⟩
  · rw [R0, range_blockSL_eq_longRootGroup h2 (by norm_num : 0 + 2 ≤ 4), ← longRootGroup_conj, hm]
  · rw [R0', range_blockSL_eq_longRootGroup h2 (by norm_num : 2 + 2 ≤ 4), ← longRootGroup_conj, hm']

theorem map_conj_swap (h2 : (2 : F) ≠ 0) {g : SL(4, F)} (hg : g * x0 F * g⁻¹ = zneg F * x0 F) :
    (R0 F).map (MulAut.conj g).toMonoidHom = R0' F ∧
      (R0' F).map (MulAut.conj g).toMonoidHom = R0 F := by
  have hm : (g : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 0 * ((g⁻¹ : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = negBlock F 4 2 := by
    rw [← coe_x0_eq_negBlock, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_mul, coe_zneg,
      neg_one_mul, coe_x0_eq_negBlock, negBlock_two_eq_neg]
  have hm' : (g : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 2 * ((g⁻¹ : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = negBlock F 4 0 := by
    rw [negBlock_two_eq_neg, Matrix.mul_neg, Matrix.neg_mul, hm, negBlock_two_eq_neg, neg_neg]
  refine ⟨?_, ?_⟩
  · rw [R0, range_blockSL_eq_longRootGroup h2 (by norm_num : 0 + 2 ≤ 4), ← longRootGroup_conj, hm]
    exact (range_blockSL_eq_longRootGroup h2 (by norm_num : 2 + 2 ≤ 4)).symm
  · rw [R0', range_blockSL_eq_longRootGroup h2 (by norm_num : 2 + 2 ≤ 4), ← longRootGroup_conj, hm']
    exact (range_blockSL_eq_longRootGroup h2 (by norm_num : 0 + 2 ≤ 4)).symm

theorem sup_le_normalizer_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ⊔ B ≤ Subgroup.normalizer (A : Set G) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have e : b * a * b⁻¹ = a := by
      rw [← h a ha b hb]
      group
    rw [e]
    exact ha
  · intro ha'
    have e : b * a * b⁻¹ = a := by
      have h1 := h _ ha' b⁻¹ (B.inv_mem hb)
      calc b * a * b⁻¹ = (b * a * b⁻¹ * b⁻¹) * b := by group
        _ = (b⁻¹ * (b * a * b⁻¹)) * b := by rw [h1]
        _ = a := by group
    rwa [e] at ha'

theorem slayer_x0 (h2 : (2 : F) ≠ 0) [Finite F] (h4 : 4 ≤ Nat.card F) :
    SLayer (x0 F) (R0 F ⊔ R0' F) := by
  have hq : CFSG.IsQuasisimple SL(2, F) := isQuasisimple_sl2 h4
  have : Group.IsPerfect SL(2, F) := hq.1
  have hperf0 : Group.IsPerfect (R0 F) := Group.IsPerfect.range (blockSL F 4 2 0 (by norm_num))
  have hperf2 : Group.IsPerfect (R0' F) := Group.IsPerfect.range (blockSL F 4 2 2 (by norm_num))
  have hq0 : CFSG.IsQuasisimple ↥(R0 F) :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (blockSL_injective (by norm_num))) hq
  have hq2 : CFSG.IsQuasisimple ↥(R0' F) :=
    isQuasisimple_of_equiv (MonoidHom.ofInjective (blockSL_injective (by norm_num))) hq
  have hn0 := sup_le_normalizer_of_comm (A := R0 F) (B := R0' F) fun a ha b hb =>
    R0_comm_R0' ha hb
  have hn2 := sup_le_normalizer_of_comm (A := R0' F) (B := R0 F) fun a ha b hb =>
    (R0_comm_R0' hb ha).symm
  rw [sup_comm] at hn2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have := sup_le R0_le_centralizer R0'_le_centralizer hp
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this (x0 F) rfl).symm
  · intro g hg p hp
    have hmem : g * p * g⁻¹ ∈ (R0 F ⊔ R0' F).map (MulAut.conj g).toMonoidHom := ⟨p, hp, rfl⟩
    rw [Subgroup.map_sup] at hmem
    rcases conj_x0_cases hg with h | h
    · obtain ⟨e1, e2⟩ := map_conj_fix h2 h
      rwa [e1, e2] at hmem
    · obtain ⟨e1, e2⟩ := map_conj_swap h2 h
      rwa [e1, e2, sup_comm] at hmem
  · refine sup_le ?_ ?_
    · exact (Subgroup.commutator_eq_self (H := R0 F)).symm.le.trans
        (Subgroup.commutator_mono le_sup_left le_sup_left)
    · exact (Subgroup.commutator_eq_self (H := R0' F)).symm.le.trans
        (Subgroup.commutator_mono le_sup_right le_sup_right)
  · refine ⟨{R0 F, R0' F}, ?_, ?_⟩
    · intro H hH
      rcases hH with rfl | hH
      · exact ⟨le_sup_left, hq0, fun p hp h hh => (Subgroup.mem_normalizer_iff.mp (hn0 hp) h).mp hh⟩
      · rw [Set.mem_singleton_iff] at hH
        subst hH
        exact ⟨le_sup_right, hq2, fun p hp h hh =>
          (Subgroup.mem_normalizer_iff.mp (hn2 hp) h).mp hh⟩
    · exact sup_le (le_iSup₂_of_le (R0 F) (Set.mem_insert _ _) le_rfl)
        (le_iSup₂_of_le (R0' F) (Set.mem_insert_of_mem _ rfl) le_rfl)

@[expose] noncomputable def blk (A B : SL(2, F)) : SL(4, F) :=
  blockSL F 4 2 0 (by norm_num) A * blockSL F 4 2 2 (by norm_num) B

theorem coe_blk (A B : SL(2, F)) : ((blk A B : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1] := by
  rw [blk, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL, blockMat_four_zero,
    blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem blk_mem (A B : SL(2, F)) : blk A B ∈ R0 F ⊔ R0' F :=
  Subgroup.mul_mem_sup ⟨A, rfl⟩ ⟨B, rfl⟩

theorem u0_eq_blk : u0 F = blk r0 r0 := rfl

variable (F) in
@[expose] noncomputable def t0 : SL(4, F) := x0 F * u0 F

theorem coe_t0 : ((t0 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [t0, Matrix.SpecialLinearGroup.coe_mul, coe_x0, coe_u0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem t0_mem : t0 F ∈ R0 F ⊔ R0' F :=
  (R0 F ⊔ R0' F).mul_mem (Subgroup.mem_sup_left x0_mem_R0) u0_mem

variable (F) in
@[expose] def U1 : SL(4, F) :=
  ⟨!![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1],
    by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩

theorem coe_U1 : ((U1 F : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1] := rfl

theorem slConj_eq_of_mul_eq (G : GL (Fin 4) F) {x y : SL(4, F)}
    (h : (G : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) =
      (y : Matrix (Fin 4) (Fin 4) F) * (G : Matrix (Fin 4) (Fin 4) F)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F G x = y := by
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix, h,
    Matrix.mul_assoc]
  have : (G : Matrix (Fin 4) (Fin 4) F) * ((G⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 :=
    Units.mul_inv G
  show _ * (_ * _) = _
  rw [this, Matrix.mul_one]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
