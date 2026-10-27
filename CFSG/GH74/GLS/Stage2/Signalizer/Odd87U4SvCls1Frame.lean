module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassUa
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvCls1Fix

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace U4C1

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open scoped MatrixGroups commutatorElement

section Frame

variable {p f : ℕ} {K : Type} [Field K]

theorem u4_exists_frame (h : UnitaryFieldData p f K) (hp : p ≠ 2) {A : GL (HypIndex 2 0) K}
    (hA : A ∈ hypUnitary h 2 0) {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1) (hN : h.norm l = 1)
    (hdim : finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) = 2) :
    ∃ v : Fin 2 ⊕ Fin 2 → HypIndex 2 0 → K,
      (∀ i j, hypForm h 2 0 (v i) (v j) = if i = j then 1 else 0) ∧
      ∀ i, (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v i =
        Sum.elim (fun _ => l) (fun _ => -l) i • v i := by
  have hAA' := mulVecLin_mul_self hAA
  rw [← coe_unitaryOfHyp h hA] at hAA'
  obtain ⟨horth, hsepP, hsepM, -⟩ := exists_split_centralizer_equiv hp (hypForm_isSymm h)
    (hypForm_separatingLeft h) hl0 hAA' hN
  rw [coe_unitaryOfHyp] at horth hsepP hsepM hAA'
  have hc : IsCompl (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)))
      (eigenMinus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) :=
    isCompl_ker_sub_one_ker_add_one (two_ne_zero_of_odd h hp) (invSMulOp_mul_self hl0 hAA')
  have hdim' := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_hypIndex_fun] at hdim'
  have hP : ∀ v ∈ eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = l • v :=
    fun v hv => mulVec_eq_of_mem_eigenPlus hl0 hv
  have hM : ∀ v ∈ eigenMinus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K)),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = (-l) • v :=
    fun v hv => mulVec_eq_of_mem_eigenMinus hl0 hv
  obtain ⟨a, haW, ha⟩ :=
    CFSG.ComponentClassification.CatFactsL4U4.InvClassU.exists_orthonormal_of_finrank h hsepP hdim
  obtain ⟨b, hbW, hb⟩ :=
    CFSG.ComponentClassification.CatFactsL4U4.InvClassU.exists_orthonormal_of_finrank h hsepM
      (k := 2) (by omega)
  refine ⟨Sum.elim a b, CFSG.ComponentClassification.CatFactsL4U4.InvClassU.orthonormal_elim h ha hb
    fun i j => horth _ (haW i) _ (hbW j), ?_⟩
  rintro (i | i)
  · exact hP _ (haW i)
  · exact hM _ (hbW i)

end Frame

section FrameP

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def u4Vm (w : Fin 4 → HypIndex 2 0 → K) : Matrix (HypIndex 2 0) (Fin 4) K :=
  Matrix.of fun a i => w i a

@[expose] def u4C (γ : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 2⁻¹, 0; γ, 0, -(γ * 2⁻¹), 0; 0, 1, 0, 2⁻¹; 0, γ, 0, -(γ * 2⁻¹)]

theorem u4C_gram {γ : K} (hγ : h.norm γ = -1) (h2 : (2 : K) ≠ 0) :
    ((u4C γ).map h.bar)ᵀ * u4C γ = J4 := by
  have hγ' : γ * h.bar γ = -1 := hγ
  have hb2 : h.bar (2 : K)⁻¹ = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4C, J4, Matrix.map_apply, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four,
      map_mul, map_neg, hb2] <;> field_simp <;>
    first | ring1 | linear_combination hγ' | linear_combination (-1 : K) * hγ'

theorem u4D_mul_C (l γ : K) :
    (Matrix.diagonal ![l, l, -l, -l] : Matrix (Fin 4) (Fin 4) K) * u4C γ = u4C γ * (l • u4A0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u4C, u4A0, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_four] <;> ring

end FrameP

section FrameQ

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u4Vm_gram (w : Fin 4 → HypIndex 2 0 → K)
    (hon : ∀ i j, hypForm h 2 0 (w i) (w j) = if i = j then 1 else 0) :
    ((u4Vm w).map h.bar)ᵀ * hypGram 2 0 K * u4Vm w = 1 := by
  ext i j
  have h1 := gramForm_mulVec h (hypGram 2 0 K) (u4Vm w) (Pi.single i 1) (Pi.single j 1)
  rw [gramForm_single] at h1
  have e : ∀ k : Fin 4, u4Vm w *ᵥ (Pi.single k 1 : Fin 4 → K) = w k := fun k => by
    ext a
    simp [u4Vm, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, e] at h1
  rw [← h1, Matrix.one_apply]
  exact hon i j

@[expose] def u4P (w : Fin 4 → HypIndex 2 0 → K) (γ : K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K :=
  (u4Vm w * u4C γ).submatrix id hyp4

theorem u4P_gram (w : Fin 4 → HypIndex 2 0 → K)
    (hon : ∀ i j, hypForm h 2 0 (w i) (w j) = if i = j then 1 else 0) {γ : K}
    (hγ : h.norm γ = -1) (h2 : (2 : K) ≠ 0) :
    ((u4P w γ).map h.bar)ᵀ * hypGram 2 0 K * u4P w γ = hypGram 2 0 K := by
  have key : ∀ N : Matrix (HypIndex 2 0) (Fin 4) K,
      ((N.submatrix id hyp4).map h.bar)ᵀ * hypGram 2 0 K * N.submatrix id hyp4 =
        ((N.map h.bar)ᵀ * hypGram 2 0 K * N).submatrix hyp4 hyp4 := by
    intro N
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [u4P, key]
  have h3 : ((u4Vm w * u4C γ).map h.bar)ᵀ * hypGram 2 0 K * (u4Vm w * u4C γ) = J4 := by
    rw [Matrix.map_mul, transpose_mul]
    calc ((u4C γ).map h.bar)ᵀ * ((u4Vm w).map h.bar)ᵀ * hypGram 2 0 K * (u4Vm w * u4C γ)
        = ((u4C γ).map h.bar)ᵀ * (((u4Vm w).map h.bar)ᵀ * hypGram 2 0 K * u4Vm w) * u4C γ := by
          simp only [Matrix.mul_assoc]
      _ = J4 := by rw [u4Vm_gram h w hon, Matrix.mul_one, u4C_gram h hγ h2]
  rw [h3, ← toHyp_J4]
  rfl

theorem u4P_comm (w : Fin 4 → HypIndex 2 0 → K) (γ l : K) {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hAw : A * u4Vm w = u4Vm w * Matrix.diagonal ![l, l, -l, -l]) :
    A * u4P w γ = u4P w γ * (l • toHyp (u4A0 : Matrix (Fin 4) (Fin 4) K)) := by
  set N : Matrix (HypIndex 2 0) (Fin 4) K := u4Vm w * u4C γ with hN
  set M4 : Matrix (Fin 4) (Fin 4) K := l • u4A0 with hM4
  have h1 : A * N = N * M4 := by
    calc A * N = (A * u4Vm w) * u4C γ := (Matrix.mul_assoc _ _ _).symm
      _ = (u4Vm w * Matrix.diagonal ![l, l, -l, -l]) * u4C γ := by rw [hAw]
      _ = u4Vm w * (Matrix.diagonal ![l, l, -l, -l] * u4C γ) := Matrix.mul_assoc _ _ _
      _ = u4Vm w * (u4C γ * M4) := by rw [u4D_mul_C]
      _ = N * M4 := (Matrix.mul_assoc _ _ _).symm
  have e1 : A * N.submatrix id hyp4 = (A * N).submatrix id hyp4 := by
    ext a b
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  have e2 : N.submatrix id hyp4 * (l • toHyp (u4A0 : Matrix (Fin 4) (Fin 4) K)) =
      (N * M4).submatrix id hyp4 := by
    have : l • toHyp (u4A0 : Matrix (Fin 4) (Fin 4) K) = M4.submatrix hyp4 hyp4 := by
      ext a b
      simp [toHyp, hM4]
    rw [this, Matrix.submatrix_mul_equiv]
  rw [u4P, e1, e2, h1]

end FrameQ

section FrameThm

variable {p f : ℕ} {K : Type} [Field K]

theorem u4_exists_P (h : UnitaryFieldData p f K) (hp : p ≠ 2) {A : GL (HypIndex 2 0) K}
    (hA : A ∈ hypUnitary h 2 0) {l : K} (hl0 : l ≠ 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * A = (l ^ 2) • 1) (hN : h.norm l = 1)
    (hdim : finrank K (eigenPlus l (mulVecLin (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K))) = 2) :
    ∃ P : ↥(hypUnitary h 2 0),
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((P : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        ((P : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          (l • toHyp (u4A0 : Matrix (Fin 4) (Fin 4) K)) := by
  obtain ⟨v, hv, hAv⟩ := u4_exists_frame h hp hA hl0 hAA hN hdim
  obtain ⟨γ, hγ⟩ := OddUnitaryInvolutionSylow.exists_norm_eq_neg_one h
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp
  set w : Fin 4 → HypIndex 2 0 → K :=
    ![v (Sum.inl 0), v (Sum.inl 1), v (Sum.inr 0), v (Sum.inr 1)] with hw
  have hon : ∀ i j, hypForm h 2 0 (w i) (w j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hw, hv]
  have hAw : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) * u4Vm w =
      u4Vm w * Matrix.diagonal ![l, l, -l, -l] := by
    ext a i
    have hi : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w i = ![l, l, -l, -l] i • w i := by
      fin_cases i <;> simp [hw, hAv]
    rw [Matrix.mul_diagonal]
    have := congrFun hi a
    simpa [Matrix.mul_apply, u4Vm, Matrix.mulVec, dotProduct, mul_comm] using this
  have hP := u4P_gram h w hon hγ h2
  have hdet : (u4P w γ).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hP
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact det_hypGram_ne_zero h1.symm
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (u4P w γ) hdet, ?_⟩, ?_⟩
  · rw [mem_hypUnitary, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hP
  · simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact u4P_comm w γ l hAw

theorem u4_alpha0_eq (h : UnitaryFieldData p f K) {A P : ↥(hypUnitary h 2 0)} {l : K} (hl0 : l ≠ 0)
    (hN : h.norm l = 1)
    (hP : ((A : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        ((P : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      ((P : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (l • toHyp (u4A0 : Matrix (Fin 4) (Fin 4) K))) :
    u4Alpha0 h = hypPhi h P⁻¹ * hypPhi h A * (hypPhi h P⁻¹)⁻¹ := by
  have hz : (GeneralLinearGroup.scalar (HypIndex 2 0) (Units.mk0 l hl0) : GL (HypIndex 2 0) K) ∈
      hypUnitary h 2 0 := by
    rw [mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram h, Units.val_mk0, hN, one_smul]
  have hA0 : ((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K) ∈ hypUnitary h 2 0 :=
    mem_hypUnitary.2 (mem_hypSU.1 (u4A0El h).2).1
  have key : P⁻¹ * A * P⁻¹⁻¹ = (⟨_, hz⟩ : ↥(hypUnitary h 2 0)) * ⟨_, hA0⟩ := by
    apply Subtype.ext
    have hGL : (A : GL (HypIndex 2 0) K) * P = P *
        (GeneralLinearGroup.scalar (HypIndex 2 0) (Units.mk0 l hl0) *
          ((u4A0El h : hypSU h 2 0) : GL (HypIndex 2 0) K)) := by
      apply Units.ext
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, u4A0El, coe_hypOf, Units.val_mk0]
      rw [hP, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    change (P : GL (HypIndex 2 0) K)⁻¹ * (A : GL (HypIndex 2 0) K) * (P : GL (HypIndex 2 0) K)⁻¹⁻¹ = _
    rw [inv_inv, mul_assoc, hGL, inv_mul_cancel_left]
    rfl
  have hz1 : hypPhi h ⟨_, hz⟩ = 1 :=
    (semilinearAutHom_eq_one_iff h (by norm_num) (by norm_num) (by norm_num) _).2
      ⟨rfl, Units.mk0 l hl0, rfl⟩
  have h1 : hypPhi h P⁻¹ * hypPhi h A * (hypPhi h P⁻¹)⁻¹ = hypPhi h (P⁻¹ * A * P⁻¹⁻¹) := by
    simp only [map_mul, map_inv, inv_inv]
  rw [h1, key, map_mul, hz1, one_mul]
  rfl

end FrameThm

end U4C1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
