module

public import CFSG.GH74.L5U5.Models
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelSp

open Matrix CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

section Iso

variable {F : Type} [Field F]

variable (F) in
abbrev J2m : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

@[expose] def isoGL {n : ℕ} (J : Matrix (Fin n) (Fin n) F) : Subgroup (GL (Fin n) F) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) F)ᵀ * J * (A : Matrix (Fin n) (Fin n) F) = J}
  mul_mem' {A B} hA hB := by
    have hA' : (A : Matrix (Fin n) (Fin n) F)ᵀ * J * (A : Matrix (Fin n) (Fin n) F) = J := hA
    have hB' : (B : Matrix (Fin n) (Fin n) F)ᵀ * J * (B : Matrix (Fin n) (Fin n) F) = J := hB
    change ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * J *
      ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = J
    have e : ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F))ᵀ * J *
        ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) =
        (B : Matrix (Fin n) (Fin n) F)ᵀ *
          ((A : Matrix (Fin n) (Fin n) F)ᵀ * J * (A : Matrix (Fin n) (Fin n) F)) *
            (B : Matrix (Fin n) (Fin n) F) := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [Units.val_mul, e, hA', hB']
  one_mem' := by
    change ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * J *
      ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = J
    simp
  inv_mem' {A} hA := by
    have hA' : (A : Matrix (Fin n) (Fin n) F)ᵀ * J * (A : Matrix (Fin n) (Fin n) F) = J := hA
    have hAB : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    change ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * J *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = J
    have key : ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)ᵀ *
        ((A : Matrix (Fin n) (Fin n) F)ᵀ * J * (A : Matrix _ _ F)) *
          ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F) =
        ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F))ᵀ * J *
          ((A : Matrix _ _ F) * ((A⁻¹ : GL (Fin n) F) : Matrix _ _ F)) := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hA', hAB, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at key
    exact key

theorem mem_isoGL {n : ℕ} {J : Matrix (Fin n) (Fin n) F} {A : GL (Fin n) F} :
    A ∈ isoGL J ↔
      (A : Matrix (Fin n) (Fin n) F)ᵀ * J * (A : Matrix (Fin n) (Fin n) F) = J :=
  Iff.rfl

theorem transpose_mul_J2m_mul (A : Matrix (Fin 2) (Fin 2) F) :
    Aᵀ * J2m F * A = A.det • J2m F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, transpose_apply, of_apply,
      cons_val', cons_val_fin_one, Fin.sum_univ_two, cons_val_zero, cons_val_one, mul_zero, mul_neg,
      mul_one, zero_add, neg_mul, add_zero, det_fin_two, Matrix.smul_apply, smul_eq_mul,
      neg_sub] <;> ring

theorem mem_isoGL_J2m {a : GL (Fin 2) F} :
    a ∈ isoGL (J2m F) ↔ (a : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [mem_isoGL, transpose_mul_J2m_mul]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simpa using this
  · intro h
    rw [h, one_smul]

theorem isoGL_J2m_eq_detOne : isoGL (J2m F) = detOne F 2 :=
  Subgroup.ext fun _ => mem_isoGL_J2m

theorem blk4_transpose (X Y : Matrix (Fin 2) (Fin 2) F) : (blk4 X Y)ᵀ = blk4 Xᵀ Yᵀ :=
  diagBlock_transpose X Y

theorem diagGL_mem_isoGL_iff (a b : GL (Fin 2) F) :
    diagGL a b ∈ isoGL (blk4 (J2m F) (J2m F)) ↔ a ∈ isoGL (J2m F) ∧ b ∈ isoGL (J2m F) := by
  rw [mem_isoGL, mem_isoGL, mem_isoGL, coe_diagGL, blk4_transpose, blk4_mul, blk4_mul]
  constructor
  · intro h
    exact blk4_inj h
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem wMat_transpose : (wMat : Matrix (Fin 4) (Fin 4) F)ᵀ = wMat := by
  rw [wMat, Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex, fromBlocks_transpose]
  simp

theorem swapGL_mem_isoGL : swapGL F ∈ isoGL (blk4 (J2m F) (J2m F)) := by
  rw [mem_isoGL, coe_swapGL, wMat_transpose, wMat_mul_blk4_mul_wMat]

theorem neg_one_mem_isoGL_J2m : (-1 : GL (Fin 2) F) ∈ isoGL (J2m F) := by
  rw [mem_isoGL_J2m]
  simp [Matrix.det_neg]

end Iso

section Model

variable (F : Type) [Field F]

@[expose] def _root_.CFSG.GH74.L5U5.ModelData.sp : ModelData F where
  U2 := isoGL (J2m F)
  U4 := isoGL (blk4 (J2m F) (J2m F))
  K4 := isoGL (blk4 (J2m F) (J2m F)) ⊓ detOne F 4
  H2 := isoGL (J2m F) ⊓ detOne F 2
  mem_K4 g := by rw [Subgroup.mem_inf, mem_detOne]
  mem_H2 g := by rw [Subgroup.mem_inf, mem_detOne]
  diag_mem_iff := diagGL_mem_isoGL_iff
  neg_mem := neg_one_mem_isoGL_J2m
  swap_mem := swapGL_mem_isoGL

variable {F}

theorem sp_U2 : (ModelData.sp F).U2 = isoGL (J2m F) := rfl

theorem sp_U4 : (ModelData.sp F).U4 = isoGL (blk4 (J2m F) (J2m F)) := rfl

theorem sp_K4 : (ModelData.sp F).K4 = isoGL (blk4 (J2m F) (J2m F)) ⊓ detOne F 4 := rfl

theorem sp_H2 : (ModelData.sp F).H2 = isoGL (J2m F) ⊓ detOne F 2 := rfl

theorem mem_U2_sp {a : GL (Fin 2) F} :
    a ∈ (ModelData.sp F).U2 ↔ (a : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  mem_isoGL_J2m

theorem H2_sp_eq_U2 : (ModelData.sp F).H2 = (ModelData.sp F).U2 :=
  Subgroup.ext fun a => by
    rw [(ModelData.sp F).mem_H2, mem_U2_sp, and_self]

end Model

section Reindex

variable {F : Type} [Field F]

@[expose] def sigma : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun
    | Sum.inl 0 => 0
    | Sum.inr 0 => 1
    | Sum.inl 1 => 2
    | Sum.inr 1 => 3
  invFun
    | 0 => Sum.inl 0
    | 1 => Sum.inr 0
    | 2 => Sum.inl 1
    | 3 => Sum.inr 1
  left_inv := by decide
  right_inv := by decide

theorem e4_symm_zero : e4.symm 0 = Sum.inl 0 := by decide

theorem e4_symm_one : e4.symm 1 = Sum.inl 1 := by decide

theorem e4_symm_two : e4.symm 2 = Sum.inr 0 := by decide

theorem e4_symm_three : e4.symm 3 = Sum.inr 1 := by decide

theorem reindex_gram :
    Matrix.reindex sigma sigma (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      blk4 (J2m F) (J2m F) := by
  ext a b
  rw [blk4_eq_reindex]
  fin_cases a <;> fin_cases b <;> simp [Matrix.reindex_apply, Matrix.submatrix_apply, sigma,
    e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three, Matrix.fromBlocks]

variable (F) in
@[expose] noncomputable def glSigma : GL (Fin 2 ⊕ Fin 2) F ≃* GL (Fin 4) F :=
  Units.mapEquiv (Matrix.reindexAlgEquiv F F sigma).toMulEquiv

theorem coe_glSigma (g : GL (Fin 2 ⊕ Fin 2) F) :
    ((glSigma F g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.reindex sigma sigma (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :=
  rfl

theorem glSigma_scalar (u : Fˣ) :
    glSigma F (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 4) u := by
  ext i j
  rw [coe_glSigma, Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar,
    scalar_apply, scalar_apply, reindex_apply, submatrix_diagonal_equiv]
  rfl

theorem mem_statedSp_iff {g : GL (Fin 2 ⊕ Fin 2) F} :
    g ∈ StatedSp 2 F ↔
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = fromBlocks 0 1 (-1) 0 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

theorem glSigma_mem_isoGL_iff (g : GL (Fin 2 ⊕ Fin 2) F) :
    glSigma F g ∈ isoGL (blk4 (J2m F) (J2m F)) ↔ g ∈ StatedSp 2 F := by
  rw [mem_statedSp_iff, mem_isoGL, coe_glSigma, ← reindex_gram]
  have e : ∀ X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      Matrix.reindex sigma sigma X = Matrix.reindexAlgEquiv F F sigma X := fun X =>
    (congrFun (Matrix.coe_reindexAlgEquiv F F sigma) X).symm
  rw [Matrix.transpose_reindex, e, e, e, ← map_mul, ← map_mul]
  exact (Matrix.reindexAlgEquiv F F sigma).injective.eq_iff

theorem det_eq_one_of_mem_isoGL {g : GL (Fin 4) F} (hg : g ∈ isoGL (blk4 (J2m F) (J2m F))) :
    (g : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  obtain ⟨h, rfl⟩ := (glSigma F).surjective g
  have hh : h ∈ StatedSp 2 F := (glSigma_mem_isoGL_iff h).1 hg
  rw [coe_glSigma, Matrix.det_reindex_self]
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic,
    TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup] at hh
  exact SymplecticGroup.det_eq_one hh

theorem K4_sp_eq : (ModelData.sp F).K4 = isoGL (blk4 (J2m F) (J2m F)) :=
  inf_eq_left.2 fun _ hg => det_eq_one_of_mem_isoGL hg

theorem mem_K4_sp {g : GL (Fin 4) F} :
    g ∈ (ModelData.sp F).K4 ↔ g ∈ isoGL (blk4 (J2m F) (J2m F)) := by
  rw [K4_sp_eq]

theorem map_statedSp :
    (StatedSp 2 F).map (glSigma F).toMonoidHom = (ModelData.sp F).K4 := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_K4_sp, ← glSigma_mem_isoGL_iff, MulEquiv.apply_symm_apply]

@[expose] noncomputable def spMulEquiv : StatedSp 2 F ≃* ↥(ModelData.sp F).K4 :=
  ((glSigma F).subgroupMap (StatedSp 2 F)).trans (MulEquiv.subgroupCongr map_statedSp)

theorem coe_spMulEquiv (g : StatedSp 2 F) :
    ((spMulEquiv g : ↥(ModelData.sp F).K4) : GL (Fin 4) F) =
      glSigma F (g : GL (Fin 2 ⊕ Fin 2) F) :=
  rfl

theorem coe_spMulEquiv_symm (g : ↥(ModelData.sp F).K4) :
    ((spMulEquiv.symm g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      (glSigma F).symm (g : GL (Fin 4) F) := by
  apply (glSigma F).injective
  rw [MulEquiv.apply_symm_apply, ← coe_spMulEquiv, MulEquiv.apply_symm_apply]

theorem map_scalars_spMulEquiv :
    ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F)).map spMulEquiv.toMonoidHom =
      (StatedScalars (Fin 4) F).subgroupOf (ModelData.sp F).K4 := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    coe_spMulEquiv_symm]
  simp only [StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← glSigma_scalar, hc, MulEquiv.apply_symm_apply]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← hc, ← glSigma_scalar, MulEquiv.symm_apply_apply]

variable (F) in
@[expose] noncomputable def spEquiv :
    StatedProj (StatedSp 2 F) ≃* StatedProj (ModelData.sp F).K4 :=
  QuotientGroup.congr _ _ spMulEquiv map_scalars_spMulEquiv

theorem spEquiv_mk (g : StatedSp 2 F) :
    spEquiv F (QuotientGroup.mk g) = QuotientGroup.mk (spMulEquiv g) :=
  rfl

theorem natCard_K4_sp : Nat.card ↥(ModelData.sp F).K4 = Nat.card (StatedSp 2 F) :=
  (Nat.card_congr (spMulEquiv (F := F)).toEquiv).symm

end Reindex

section Centralizer

variable {F : Type} [Field F]

theorem diagGL_comm_yGL (a b : GL (Fin 2) F) : diagGL a b * yGL F = yGL F * diagGL a b := by
  rw [yGL, diagGL_mul, diagGL_mul]
  simp only [mul_neg, neg_mul, mul_one, one_mul]

theorem det_mul_det_inv (a : GL (Fin 2) F) :
    (a : Matrix (Fin 2) (Fin 2) F).det * ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      1 := by
  rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]

theorem card_centralizer_yK (M : ModelData F) (h2 : (2 : F) ≠ 0) :
    Nat.card ↥(Subgroup.centralizer ({M.yK} : Set ↥M.K4)) = Nat.card ↥M.U2 * Nat.card ↥M.H2 := by
  have hmemK : ∀ (a : ↥M.U2) (c : ↥M.H2),
      diagGL (a : GL (Fin 2) F) ((c : GL (Fin 2) F) * (a : GL (Fin 2) F)⁻¹) ∈ M.K4 := by
    intro a c
    obtain ⟨hc1, hc2⟩ := (M.mem_H2 _).1 c.2
    rw [M.diagGL_mem_K4_iff]
    refine ⟨a.2, M.U2.mul_mem hc1 (M.U2.inv_mem a.2), ?_⟩
    rw [Units.val_mul, det_mul, hc2, one_mul]
    exact det_mul_det_inv _
  have hmemC : ∀ (a : ↥M.U2) (c : ↥M.H2),
      (⟨_, hmemK a c⟩ : ↥M.K4) ∈ Subgroup.centralizer ({M.yK} : Set ↥M.K4) := by
    intro a c
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subtype.ext (diagGL_comm_yGL _ _).symm
  let Ψ : ↥M.U2 × ↥M.H2 → ↥(Subgroup.centralizer ({M.yK} : Set ↥M.K4)) :=
    fun p => ⟨⟨_, hmemK p.1 p.2⟩, hmemC p.1 p.2⟩
  have hΨ : Function.Bijective Ψ := by
    constructor
    · rintro ⟨a, c⟩ ⟨a', c'⟩ h
      have h1 := congrArg
        (fun x : ↥(Subgroup.centralizer ({M.yK} : Set ↥M.K4)) => ((x : ↥M.K4) : GL (Fin 4) F)) h
      obtain ⟨ha, hc⟩ := diagGL_inj h1
      have ha' : (a : GL (Fin 2) F) = a' := ha
      rw [ha'] at hc
      have hc' := mul_right_cancel hc
      exact Prod.ext (Subtype.ext ha') (Subtype.ext hc')
    · intro g
      have hc : (g : ↥M.K4) * M.yK = M.yK * g :=
        (Subgroup.mem_centralizer_iff.1 g.2 M.yK rfl).symm
      have hc' : ((g : ↥M.K4) : GL (Fin 4) F) * yGL F = yGL F * ((g : ↥M.K4) : GL (Fin 4) F) :=
        congrArg Subtype.val hc
      obtain ⟨a, b, hg, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 (g : ↥M.K4).2 hc'
      have hba : b * a ∈ M.H2 := by
        refine (M.mem_H2 _).2 ⟨M.U2.mul_mem hb ha, ?_⟩
        rw [Units.val_mul, det_mul, mul_comm]
        exact hdet
      refine ⟨(⟨a, ha⟩, ⟨b * a, hba⟩), Subtype.ext (Subtype.ext ?_)⟩
      change diagGL a (b * a * a⁻¹) = _
      rw [mul_inv_cancel_right, hg]
  rw [Nat.card_congr (Equiv.ofBijective Ψ hΨ).symm, Nat.card_prod]

end Centralizer

section Orders

variable {F : Type} [Field F] [Finite F]

theorem card_K4_sp :
    Nat.card ↥(ModelData.sp F).K4 =
      Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  rw [← Nat.card_congr (spMulEquiv (F := F)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp 2]
  have e : (∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1)) =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) := by
    have e : Finset.Icc 1 2 = {1, 2} := by decide
    rw [e]; simp
  rw [e]; norm_num

theorem card_U2_sp : Nat.card ↥(ModelData.sp F).U2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [sp_U2, isoGL_J2m_eq_detOne, ← statedSL_eq_detOne,
    ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv]
  exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F

theorem card_H2_sp : Nat.card ↥(ModelData.sp F).H2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [H2_sp_eq_U2]
  exact card_U2_sp

theorem odd_card_of_two_ne_zero (h2 : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  have h := FiniteField.even_card_iff_char_two (F := F)
  rw [← Nat.card_eq_fintype_card] at h
  exact Nat.odd_iff.2 (by have := h.not.1 hchar; omega)

theorem odd_index_sp (h2 : (2 : F) ≠ 0) :
    ∃ m : ℕ, Odd m ∧ Nat.card ↥(ModelData.sp F).K4 =
      2 * Nat.card ↥(Subgroup.centralizer ({(ModelData.sp F).yK} :
        Set ↥(ModelData.sp F).K4)) * m := by
  obtain ⟨k, hk⟩ := odd_card_of_two_ne_zero h2
  rw [card_K4_sp, card_centralizer_yK _ h2, card_U2_sp, card_H2_sp, hk]
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * k ^ 2 + 4 * k := by
    have : (2 * k + 1) ^ 2 = 4 * k ^ 2 + 4 * k + 1 := by ring
    omega
  have h4 : (2 * k + 1) ^ 4 - 1 = (4 * k ^ 2 + 4 * k) * (4 * k ^ 2 + 4 * k + 2) := by
    have : (2 * k + 1) ^ 4 = (4 * k ^ 2 + 4 * k) * (4 * k ^ 2 + 4 * k + 2) + 1 := by ring
    omega
  refine ⟨(2 * k + 1) ^ 2 * (2 * k ^ 2 + 2 * k + 1), ?_, ?_⟩
  · exact (Odd.pow ⟨k, rfl⟩).mul ⟨k ^ 2 + k, by ring⟩
  · rw [h1, h4]
    ring

end Orders

section Quaternion

variable {F : Type} [Field F]

theorem H2_sp_eq_statedSL : (ModelData.sp F).H2 = StatedSL 2 F := by
  rw [H2_sp_eq_U2, sp_U2, isoGL_J2m_eq_detOne, statedSL_eq_detOne]

variable (F) in
@[expose] noncomputable def sp_sl2_equiv_H2 :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(ModelData.sp F).H2 :=
  (specialLinearGroupEquivStatedSL 2 F).trans (MulEquiv.subgroupCongr H2_sp_eq_statedSL.symm)

variable [Finite F]

theorem exists_rho_sp (h2 : (2 : F) ≠ 0) :
    ∃ (a b : F) (h : a ^ 2 + b ^ 2 = -1), ∀ g,
      ((SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).comp
        (quatHom h)) g ∈ (ModelData.sp F).H2 := by
  obtain ⟨a, b, h⟩ :=
    (odd_field_two_dimensional_quaternion_matrices (ringChar_ne_two_of_two_ne_zero h2)).1
  refine ⟨a, b, h, fun g => ?_⟩
  refine ((ModelData.sp F).mem_H2 _).2 ⟨?_, (quatHom h g).2⟩
  rw [mem_U2_sp]
  exact (quatHom h g).2

theorem exists_rho_sp' (h2 : (2 : F) ≠ 0) :
    ∃ ρ : Q8 →* GL (Fin 2) F, (∀ g, ρ g ∈ (ModelData.sp F).H2) ∧ Function.Injective ρ ∧
      ρ (QuaternionGroup.a 2) = -1 := by
  obtain ⟨a, b, h, hρ⟩ := exists_rho_sp h2
  refine ⟨(SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).comp
    (quatHom h), hρ, ?_, ?_⟩
  · exact SpecialLinearGroup.toGL_injective.comp
      (quatHom_injective (ringChar_ne_two_of_two_ne_zero h2) h)
  · apply Units.ext
    change ((quatHom h (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) F)) = _
    rw [quatHom_a_two h]
    simp

theorem exists_q8q8_swap_sp (h2 : (2 : F) ≠ 0) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ (ModelData.sp F).K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F ∧
      ∀ g h : Q8, swapGL F * φ (g, h) * (swapGL F)⁻¹ = φ (h, g) := by
  obtain ⟨ρ, h1, h2', h3⟩ := exists_rho_sp' h2
  exact (ModelData.sp F).exists_q8q8_swap h1 h2' h3

end Quaternion

end CFSG.GH74.GLS.Stage2.Final.ModelSp
