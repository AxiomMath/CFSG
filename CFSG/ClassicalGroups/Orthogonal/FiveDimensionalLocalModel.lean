module

public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.GH74.GLS.IVK.Proofs2.Sp48O2
public import CFSG.ClassicalGroups.Orthogonal.BasisCheck
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareBasic

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel

open Matrix QuadraticMap
open scoped commutatorElement
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

structure FrameData (Q : QuadraticForm K V) where
  e : Module.Basis (Fin 5) K V
  orth : ∀ i j : Fin 5, i ≠ j → polar Q (e i) (e j) = 0
  norm : ∀ i : Fin 5, (i : ℕ) < 4 → Q (e i) = 1
  last : Q (e 4) ≠ 0
  nondeg : (polarBilin Q).Nondegenerate

theorem exists_frameData [Finite K] (hK : Odd (Nat.card K))
    (h5 : Module.finrank K V = 5) (Q : QuadraticForm K V)
    (hB : (polarBilin Q).Nondegenerate) : Nonempty (FrameData Q) := by
  obtain ⟨e, horth, hnorm, hlast⟩ :=
    CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hK (d := 5) h5 (by omega) Q hB
      one_ne_zero
  exact ⟨e, horth, fun i hi => hnorm i (by omega), hlast, hB⟩

private def idxEquiv : (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)) ≃ Fin 5 :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)).trans
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5)

@[simp] private theorem idxEquiv_symm_zero : idxEquiv.symm (0 : Fin 5) = Sum.inl 0 := by decide
@[simp] private theorem idxEquiv_symm_one : idxEquiv.symm (1 : Fin 5) = Sum.inl 1 := by decide
@[simp] private theorem idxEquiv_symm_two :
    idxEquiv.symm (2 : Fin 5) = Sum.inr (Sum.inl 0) := by decide
@[simp] private theorem idxEquiv_symm_three :
    idxEquiv.symm (3 : Fin 5) = Sum.inr (Sum.inl 1) := by decide
@[simp] private theorem idxEquiv_symm_four :
    idxEquiv.symm (4 : Fin 5) = Sum.inr (Sum.inr 0) := by decide
@[simp] private theorem finSum23_symm_zero :
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).symm 0 = Sum.inl 0 := by decide
@[simp] private theorem finSum23_symm_one :
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).symm 1 = Sum.inl 1 := by decide
@[simp] private theorem finSum23_symm_two :
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).symm 2 = Sum.inr 0 := by decide
@[simp] private theorem finSum23_symm_three :
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).symm 3 = Sum.inr 1 := by decide
@[simp] private theorem finSum23_symm_four :
    (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).symm 4 = Sum.inr 2 := by decide
@[simp] private theorem finSum21_symm_zero :
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm 0 = Sum.inl 0 := by decide
@[simp] private theorem finSum21_symm_one :
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm 1 = Sum.inl 1 := by decide
@[simp] private theorem finSum21_symm_two :
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3).symm 2 = Sum.inr 0 := by decide

private def glToLinEquiv (n : Type*) [Fintype n] [DecidableEq n] :
    GL n K ≃* ((n → K) ≃ₗ[K] (n → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K))

private theorem glToLinEquiv_apply (n : Type*) [Fintype n] [DecidableEq n]
    (A : GL n K) (v : n → K) :
    glToLinEquiv (K := K) n A v = (A : Matrix n n K) *ᵥ v := rfl

private def betaMatIdx (d1 d2 : GL (Fin 2) K) :
    Matrix (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)) (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)) K :=
  Matrix.fromBlocks (d1 : Matrix (Fin 2) (Fin 2) K) 0 0
    (Matrix.fromBlocks (d2 : Matrix (Fin 2) (Fin 2) K) 0 0
      (((d1 : Matrix (Fin 2) (Fin 2) K).det * (d2 : Matrix (Fin 2) (Fin 2) K).det) •
        (1 : Matrix (Fin 1) (Fin 1) K)))

private def betaMat5 (d1 d2 : GL (Fin 2) K) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.reindex idxEquiv idxEquiv (betaMatIdx d1 d2)

private theorem betaMatIdx_det (d1 d2 : GL (Fin 2) K) :
    (betaMatIdx d1 d2).det =
      (d1 : Matrix (Fin 2) (Fin 2) K).det * (d2 : Matrix (Fin 2) (Fin 2) K).det *
        ((d1 : Matrix (Fin 2) (Fin 2) K).det * (d2 : Matrix (Fin 2) (Fin 2) K).det) := by
  rw [betaMatIdx, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_smul, Matrix.det_one]
  simp
  ring

private def betaGL (d1 d2 : GL (Fin 2) K) : GL (Fin 5) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (betaMat5 d1 d2) (by
    rw [betaMat5, Matrix.det_reindex]
    have hsign : Equiv.Perm.sign (idxEquiv.trans idxEquiv.symm) = 1 := by
      rw [show idxEquiv.trans idxEquiv.symm = Equiv.refl (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)) from by
        ext x; simp]
      rfl
    rw [hsign]
    norm_num
    rw [betaMatIdx_det]
    exact mul_ne_zero (mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero d1)
      (Matrix.GeneralLinearGroup.det_ne_zero d2))
      (mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero d1)
        (Matrix.GeneralLinearGroup.det_ne_zero d2)))

def betaCoord (d1 d2 : GL (Fin 2) K) : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  glToLinEquiv (K := K) (Fin 5) (betaGL d1 d2)

namespace FrameData

variable (F : FrameData Q)

theorem two_ne_zero (F : FrameData Q) : (2 : K) ≠ 0 := by
  intro h2
  have hp : polar Q (F.e 0) (F.e 0) = 0 := by
    rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, F.norm 0 (by norm_num),
      h2, mul_one]
  have h0 : F.e 0 = 0 := by
    apply F.nondeg.1
    intro y
    rw [← F.e.sum_repr y, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = 0
    · subst hj
      rw [map_smul]
      change (F.e.repr y) 0 • polar Q (F.e 0) (F.e 0) = 0
      rw [hp, smul_zero]
    · rw [map_smul]
      change (F.e.repr y) j • polar Q (F.e 0) (F.e j) = 0
      rw [F.orth 0 j (by intro h; exact hj h.symm), smul_zero]
  exact F.e.ne_zero 0 h0

@[expose] def coord : V ≃ₗ[K] (Fin 5 → K) := F.e.equivFun

@[simp] theorem coord_e (i : Fin 5) : F.coord (F.e i) = Pi.single i 1 := by
  simp [coord, Module.Basis.equivFun_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single]

@[simp] theorem coord_symm_single (i : Fin 5) : F.coord.symm (Pi.single i 1) = F.e i := by
  rw [← F.coord_e i, LinearEquiv.symm_apply_apply]

@[expose] def coordForm : QuadraticForm K (Fin 5 → K) := Q.comp F.coord.symm

theorem coordForm_single (i : Fin 5) : F.coordForm (Pi.single i 1) = Q (F.e i) := by
  simp [coordForm, coord, Module.Basis.equivFun_symm_apply]

theorem coordForm_single_of_lt (i : Fin 5) (hi : (i : ℕ) < 4) :
    F.coordForm (Pi.single i 1) = 1 := by
  rw [F.coordForm_single, F.norm i hi]

theorem coordForm_single_four : F.coordForm (Pi.single 4 1) = Q (F.e 4) :=
  F.coordForm_single 4

theorem polar_coordForm_single_eq_zero {i j : Fin 5} (hij : i ≠ j) :
    polar F.coordForm (Pi.single i 1) (Pi.single j 1) = 0 := by
  have h : polar F.coordForm (Pi.single i 1) (Pi.single j 1) =
      polar Q (F.coord.symm (Pi.single i 1)) (F.coord.symm (Pi.single j 1)) := by
    simp [coordForm, QuadraticMap.polar]
  rw [h, F.coord_symm_single, F.coord_symm_single]
  exact F.orth i j hij

@[expose] def tFun (F : FrameData Q) (i : Fin 5) : Fin 5 → K :=
  if (i : ℕ) < 2 then -Pi.single i 1 else Pi.single i 1

@[expose] def tLin : (Fin 5 → K) →ₗ[K] (Fin 5 → K) :=
  (Pi.basisFun K (Fin 5)).constr K F.tFun

theorem tLin_single (i : Fin 5) :
    F.tLin (Pi.single i 1) = if (i : ℕ) < 2 then -Pi.single i 1 else Pi.single i 1 := by
  have h := Module.Basis.constr_basis (Pi.basisFun K (Fin 5)) K F.tFun i
  simpa only [tLin, tFun, Pi.basisFun_apply] using h

theorem tLin_comp_self : F.tLin.comp F.tLin = LinearMap.id := by
  apply (Pi.basisFun K (Fin 5)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearMap.id_apply]
  rw [F.tLin_single]
  by_cases hi : (i : ℕ) < 2 <;> simp [hi, F.tLin_single]

@[expose] def tCoord : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  LinearEquiv.ofInvolutive F.tLin fun x => LinearMap.congr_fun F.tLin_comp_self x

@[expose] def zFun (F : FrameData Q) (i : Fin 5) : Fin 5 → K :=
  if (i : ℕ) < 4 then -Pi.single i 1 else Pi.single i 1

@[expose] def zLin : (Fin 5 → K) →ₗ[K] (Fin 5 → K) :=
  (Pi.basisFun K (Fin 5)).constr K F.zFun

theorem zLin_single (i : Fin 5) :
    F.zLin (Pi.single i 1) = if (i : ℕ) < 4 then -Pi.single i 1 else Pi.single i 1 := by
  have h := Module.Basis.constr_basis (Pi.basisFun K (Fin 5)) K F.zFun i
  simpa only [zLin, zFun, Pi.basisFun_apply] using h

theorem zLin_comp_self : F.zLin.comp F.zLin = LinearMap.id := by
  apply (Pi.basisFun K (Fin 5)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearMap.id_apply]
  rw [F.zLin_single]
  by_cases hi : (i : ℕ) < 4 <;> simp [hi, F.zLin_single]

@[expose] def zCoord : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  LinearEquiv.ofInvolutive F.zLin fun x => LinearMap.congr_fun F.zLin_comp_self x

@[expose] def sFun (F : FrameData Q) (i : Fin 5) : Fin 5 → K :=
  if i = 0 then Pi.single 2 1 else
    if i = 1 then Pi.single 3 1 else
      if i = 2 then Pi.single 0 1 else
        if i = 3 then Pi.single 1 1 else Pi.single 4 1

@[expose] def sLin : (Fin 5 → K) →ₗ[K] (Fin 5 → K) :=
  (Pi.basisFun K (Fin 5)).constr K F.sFun

theorem sLin_single (i : Fin 5) :
    F.sLin (Pi.single i 1) = if i = 0 then Pi.single 2 1 else
      if i = 1 then Pi.single 3 1 else
        if i = 2 then Pi.single 0 1 else
          if i = 3 then Pi.single 1 1 else Pi.single 4 1 := by
  have h := Module.Basis.constr_basis (Pi.basisFun K (Fin 5)) K F.sFun i
  simpa only [sLin, sFun, Pi.basisFun_apply] using h

theorem sLin_comp_self : F.sLin.comp F.sLin = LinearMap.id := by
  apply (Pi.basisFun K (Fin 5)).ext
  intro i
  simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearMap.id_apply]
  rw [F.sLin_single]
  fin_cases i <;> simp [F.sLin_single]

@[expose] def sCoord : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  LinearEquiv.ofInvolutive F.sLin fun x => LinearMap.congr_fun F.sLin_comp_self x


theorem tCoord_apply (x : Fin 5 → K) : F.tCoord x = F.tLin x := rfl

theorem zCoord_apply (x : Fin 5 → K) : F.zCoord x = F.zLin x := rfl

theorem sCoord_apply (x : Fin 5 → K) : F.sCoord x = F.sLin x := rfl

private theorem tCoord_mem : F.tCoord ∈ TauCeti.QuadraticMap.orthogonalGroup F.coordForm := by
  refine CFSG.ClassicalGroups.Orthogonal.mem_orthogonalGroup_of_basis F.coordForm F.tCoord ?_ ?_
  · intro i
    rw [F.tCoord_apply, F.tLin_single]
    fin_cases i <;> simp [F.coordForm_single_of_lt, F.coordForm_single, F.norm]
  · intro i j
    rw [F.tCoord_apply, F.tLin_single, F.tCoord_apply, F.tLin_single]
    fin_cases i <;> fin_cases j <;>
      simp [F.coordForm_single_of_lt, F.coordForm_single, F.norm,
        F.polar_coordForm_single_eq_zero, QuadraticMap.polar_neg_left,
        QuadraticMap.polar_neg_right]

private theorem zCoord_mem : F.zCoord ∈ TauCeti.QuadraticMap.orthogonalGroup F.coordForm := by
  refine CFSG.ClassicalGroups.Orthogonal.mem_orthogonalGroup_of_basis F.coordForm F.zCoord ?_ ?_
  · intro i
    rw [F.zCoord_apply, F.zLin_single]
    fin_cases i <;> simp [F.coordForm_single_of_lt, F.coordForm_single, F.norm]
  · intro i j
    rw [F.zCoord_apply, F.zLin_single, F.zCoord_apply, F.zLin_single]
    fin_cases i <;> fin_cases j <;>
      simp [F.coordForm_single_of_lt, F.coordForm_single, F.norm,
        F.polar_coordForm_single_eq_zero, QuadraticMap.polar_neg_left,
        QuadraticMap.polar_neg_right]

private theorem sCoord_mem : F.sCoord ∈ TauCeti.QuadraticMap.orthogonalGroup F.coordForm := by
  refine CFSG.ClassicalGroups.Orthogonal.mem_orthogonalGroup_of_basis F.coordForm F.sCoord ?_ ?_
  · intro i
    rw [F.sCoord_apply, F.sLin_single]
    fin_cases i <;> simp [F.coordForm_single_of_lt, F.coordForm_single, F.norm]
  · intro i j
    rw [F.sCoord_apply, F.sLin_single, F.sCoord_apply, F.sLin_single]
    fin_cases i <;> fin_cases j <;>
      simp [F.coordForm_single_of_lt, F.coordForm_single, F.norm,
        F.polar_coordForm_single_eq_zero]

@[expose] def conjCoord (g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) : V ≃ₗ[K] V :=
  F.coord.trans (g.trans F.coord.symm)

theorem conjCoord_apply (g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) (v : V) :
    F.conjCoord g v = F.coord.symm (g (F.coord v)) := rfl

@[simp] theorem conjCoord_e (g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) (i : Fin 5) :
    F.conjCoord g (F.e i) = F.coord.symm (g (Pi.single i 1)) := by
  simp [conjCoord_apply]

theorem conjCoord_mem {g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup F.coordForm) :
    F.conjCoord g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [F.conjCoord_apply]
  have h1 : Q (F.coord.symm (g (F.coord v))) = F.coordForm (g (F.coord v)) := rfl
  have h2 : Q v = F.coordForm (F.coord v) := by simp [coordForm]
  rw [h1, h2, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg]

theorem det_conjCoord_eq (g : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K)) :
    LinearEquiv.det (F.conjCoord g) = LinearEquiv.det g := by
  rw [conjCoord, ← LinearEquiv.trans_assoc]
  simpa using LinearEquiv.det_conj (f := g) (e := F.coord.symm)

@[expose] def t : V ≃ₗ[K] V := F.conjCoord F.tCoord

@[expose] def z : V ≃ₗ[K] V := F.conjCoord F.zCoord

@[expose] def s : V ≃ₗ[K] V := F.conjCoord F.sCoord

theorem t_mem : F.t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  F.conjCoord_mem F.tCoord_mem

theorem z_mem : F.z ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  F.conjCoord_mem F.zCoord_mem

theorem s_mem : F.s ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  F.conjCoord_mem F.sCoord_mem

@[simp] theorem t_e (i : Fin 5) :
    F.t (F.e i) = if (i : ℕ) < 2 then -F.e i else F.e i := by
  rw [t, F.conjCoord_e, F.tCoord_apply, F.tLin_single]
  by_cases hi : (i : ℕ) < 2
  · rw [if_pos hi, map_neg, F.coord_symm_single]
    simp [hi]
  · rw [if_neg hi, F.coord_symm_single]
    simp [hi]

@[simp] theorem z_e (i : Fin 5) :
    F.z (F.e i) = if (i : ℕ) < 4 then -F.e i else F.e i := by
  rw [z, F.conjCoord_e, F.zCoord_apply, F.zLin_single]
  by_cases hi : (i : ℕ) < 4
  · rw [if_pos hi, map_neg, F.coord_symm_single]
    simp [hi]
  · rw [if_neg hi, F.coord_symm_single]
    simp [hi]

@[simp] theorem s_e (i : Fin 5) :
    F.s (F.e i) = if i = 0 then F.e 2 else
      if i = 1 then F.e 3 else
        if i = 2 then F.e 0 else
          if i = 3 then F.e 1 else F.e 4 := by
  rw [s, F.conjCoord_e, F.sCoord_apply, F.sLin_single]
  fin_cases i <;> simp


theorem reflect_e_self (i : Fin 5) : reflect Q (F.e i) (F.e i) = -F.e i := by
  have hv : Q (F.e i) ≠ 0 := by
    by_cases hi : (i : ℕ) < 4
    · rw [F.norm i hi]; exact one_ne_zero
    · have : i = 4 := by ext; omega
      rw [this]; exact F.last
  let _ : Invertible (Q (F.e i)) := invertibleOfNonzero hv
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    TauCeti.QuadraticMap.reflection_apply_self]

theorem reflect_e_of_ne {i j : Fin 5} (hij : i ≠ j) :
    reflect Q (F.e i) (F.e j) = F.e j := by
  have hv : Q (F.e i) ≠ 0 := by
    by_cases hi : (i : ℕ) < 4
    · rw [F.norm i hi]; exact one_ne_zero
    · have : i = 4 := by ext; omega
      rw [this]; exact F.last
  let _ : Invertible (Q (F.e i)) := invertibleOfNonzero hv
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q (F.e i) (F.orth i j hij)]

theorem q_e0_sub_e2 : Q (F.e 0 - F.e 2) = 2 := by
  have h : Q (F.e 0 - F.e 2) = Q (F.e 0) + Q (F.e 2) - polar Q (F.e 0) (F.e 2) := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, polar_neg_right]
    ring
  rw [h, F.norm 0 (by norm_num), F.norm 2 (by norm_num), F.orth 0 2 (by norm_num)]
  norm_num

theorem q_e1_sub_e3 : Q (F.e 1 - F.e 3) = 2 := by
  have h : Q (F.e 1 - F.e 3) = Q (F.e 1) + Q (F.e 3) - polar Q (F.e 1) (F.e 3) := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, polar_neg_right]
    ring
  rw [h, F.norm 1 (by norm_num), F.norm 3 (by norm_num), F.orth 1 3 (by norm_num)]
  norm_num

theorem polar_e0sub_e2_e0 : polar Q (F.e 0 - F.e 2) (F.e 0) = 2 := by
  rw [QuadraticMap.polar_sub_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    F.norm 0 (by norm_num), F.orth 2 0 (by norm_num)]
  norm_num

theorem polar_e0sub_e2_e2 : polar Q (F.e 0 - F.e 2) (F.e 2) = -2 := by
  rw [QuadraticMap.polar_sub_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    F.orth 0 2 (by norm_num), F.norm 2 (by norm_num)]
  norm_num

theorem polar_e1sub_e3_e1 : polar Q (F.e 1 - F.e 3) (F.e 1) = 2 := by
  rw [QuadraticMap.polar_sub_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    F.norm 1 (by norm_num), F.orth 3 1 (by norm_num)]
  norm_num

theorem polar_e1sub_e3_e3 : polar Q (F.e 1 - F.e 3) (F.e 3) = -2 := by
  rw [QuadraticMap.polar_sub_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    F.orth 1 3 (by norm_num), F.norm 3 (by norm_num)]
  norm_num

theorem reflect_e_zero_two_zero : reflect Q (F.e 0 - F.e 2) (F.e 0) = F.e 2 := by
  let _ : Invertible (Q (F.e 0 - F.e 2)) :=
    invertibleOfNonzero (by rw [F.q_e0_sub_e2]; exact F.two_ne_zero)
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq Q (F.e 0) (F.e 2)
      (by rw [F.norm 0 (by norm_num), F.norm 2 (by norm_num)])]

theorem reflect_e_zero_two_two : reflect Q (F.e 0 - F.e 2) (F.e 2) = F.e 0 := by
  have h := congrArg (fun g : V ≃ₗ[K] V => g (F.e 0))
    (CFSG.ClassicalGroups.Orthogonal.reflect_mul_self Q (F.e 0 - F.e 2))
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at h
  rw [F.reflect_e_zero_two_zero] at h
  exact h

theorem reflect_e_zero_two_of_ne {i : Fin 5} (hi0 : i ≠ 0) (hi2 : i ≠ 2) :
    reflect Q (F.e 0 - F.e 2) (F.e i) = F.e i := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero]
  rw [QuadraticMap.polar_sub_left, F.orth 0 i (by intro h; exact hi0 h.symm),
    F.orth 2 i (by intro h; exact hi2 h.symm)]
  simp

theorem reflect_e_one_three_one : reflect Q (F.e 1 - F.e 3) (F.e 1) = F.e 3 := by
  let _ : Invertible (Q (F.e 1 - F.e 3)) :=
    invertibleOfNonzero (by rw [F.q_e1_sub_e3]; exact F.two_ne_zero)
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq Q (F.e 1) (F.e 3)
      (by rw [F.norm 1 (by norm_num), F.norm 3 (by norm_num)])]

theorem reflect_e_one_three_three : reflect Q (F.e 1 - F.e 3) (F.e 3) = F.e 1 := by
  have h := congrArg (fun g : V ≃ₗ[K] V => g (F.e 1))
    (CFSG.ClassicalGroups.Orthogonal.reflect_mul_self Q (F.e 1 - F.e 3))
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at h
  rw [F.reflect_e_one_three_one] at h
  exact h

theorem reflect_e_one_three_of_ne {i : Fin 5} (hi1 : i ≠ 1) (hi3 : i ≠ 3) :
    reflect Q (F.e 1 - F.e 3) (F.e i) = F.e i := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero]
  rw [QuadraticMap.polar_sub_left, F.orth 1 i (by intro h; exact hi1 h.symm),
    F.orth 3 i (by intro h; exact hi3 h.symm)]
  simp

theorem t_eq_reflect_mul : F.t = reflect Q (F.e 0) * reflect Q (F.e 1) := by
  refine LinearEquiv.ext fun x => ?_
  have h : (F.t : V →ₗ[K] V) =
      ((reflect Q (F.e 0) * reflect Q (F.e 1) : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.t (F.e i) = (reflect Q (F.e 0) * reflect Q (F.e 1)) (F.e i)
    rw [F.t_e, LinearEquiv.mul_apply]
    fin_cases i <;>
      simp [F.reflect_e_self, F.reflect_e_of_ne, F.t_e]
  exact LinearMap.congr_fun h x

theorem s_eq_reflect_mul :
    F.s = reflect Q (F.e 0 - F.e 2) * reflect Q (F.e 1 - F.e 3) := by
  refine LinearEquiv.ext fun x => ?_
  have h : (F.s : V →ₗ[K] V) =
      ((reflect Q (F.e 0 - F.e 2) * reflect Q (F.e 1 - F.e 3) : V ≃ₗ[K] V) :
        V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.s (F.e i) =
      (reflect Q (F.e 0 - F.e 2) * reflect Q (F.e 1 - F.e 3)) (F.e i)
    rw [F.s_e, LinearEquiv.mul_apply]
    fin_cases i <;>
      simp [F.reflect_e_zero_two_zero, F.reflect_e_zero_two_two,
        F.reflect_e_zero_two_of_ne, F.reflect_e_one_three_one, F.reflect_e_one_three_three,
        F.reflect_e_one_three_of_ne, F.s_e]
  exact LinearMap.congr_fun h x


theorem det_reflect (F : FrameData Q) (v : V) (hv : Q v ≠ 0) : LinearEquiv.det (reflect Q v) = -1 := by
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    TauCeti.QuadraticMap.det_reflection]

theorem det_reflect_e (i : Fin 5) : LinearEquiv.det (reflect Q (F.e i)) = -1 := by
  apply F.det_reflect
  by_cases hi : (i : ℕ) < 4
  · rw [F.norm i hi]; exact one_ne_zero
  · have : i = 4 := by ext; omega
    rw [this]; exact F.last

theorem t_det : LinearEquiv.det F.t = 1 := by
  rw [F.t_eq_reflect_mul, map_mul, F.det_reflect_e 0, F.det_reflect_e 1]
  norm_num

theorem s_det : LinearEquiv.det F.s = 1 := by
  rw [F.s_eq_reflect_mul, map_mul]
  rw [F.det_reflect (F.e 0 - F.e 2) (by rw [F.q_e0_sub_e2]; exact F.two_ne_zero),
    F.det_reflect (F.e 1 - F.e 3) (by rw [F.q_e1_sub_e3]; exact F.two_ne_zero)]
  norm_num

theorem z_eq_mul_conj : F.z = F.t * (F.s * F.t * F.s) := by
  refine LinearEquiv.ext fun x => ?_
  have h : (F.z : V →ₗ[K] V) = (F.t * (F.s * F.t * F.s) : V ≃ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.z (F.e i) = (F.t * (F.s * F.t * F.s)) (F.e i)
    rw [F.z_e]
    fin_cases i <;> simp [F.t_e, F.s_e, LinearEquiv.mul_apply]
  exact LinearMap.congr_fun h x

theorem z_det : LinearEquiv.det F.z = 1 := by
  rw [F.z_eq_mul_conj]
  simp only [map_mul, F.t_det, F.s_det]
  norm_num

abbrev tO : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨F.t, F.t_mem⟩

abbrev zO : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨F.z, F.z_mem⟩

abbrev sO : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨F.s, F.s_mem⟩

theorem t_so : F.tO ∈ Q.specialOrthogonalWithin := by
  rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
  simpa [tO] using F.t_det

theorem z_so : F.zO ∈ Q.specialOrthogonalWithin := by
  rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
  simpa [zO] using F.z_det

theorem s_so : F.sO ∈ Q.specialOrthogonalWithin := by
  rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
  simpa [sO] using F.s_det

@[expose] def tSO : Q.specialOrthogonalWithin := ⟨F.tO, F.t_so⟩

@[expose] def zSO : Q.specialOrthogonalWithin := ⟨F.zO, F.z_so⟩

@[expose] def sSO : Q.specialOrthogonalWithin := ⟨F.sO, F.s_so⟩


theorem t_mul_self : F.t * F.t = 1 := by
  have h : ((F.t * F.t : V ≃ₗ[K] V) : V →ₗ[K] V) = ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.t (F.t (F.e i)) = F.e i
    rw [F.t_e]
    by_cases hi : (i : ℕ) < 2
    · rw [if_pos hi, map_neg, F.t_e, if_pos hi, neg_neg]
    · rw [if_neg hi, F.t_e, if_neg hi]
  exact LinearEquiv.ext fun x => LinearMap.congr_fun h x

theorem z_mul_self : F.z * F.z = 1 := by
  have h : ((F.z * F.z : V ≃ₗ[K] V) : V →ₗ[K] V) = ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.z (F.z (F.e i)) = F.e i
    rw [F.z_e]
    by_cases hi : (i : ℕ) < 4
    · rw [if_pos hi, map_neg, F.z_e, if_pos hi, neg_neg]
    · rw [if_neg hi, F.z_e, if_neg hi]
  exact LinearEquiv.ext fun x => LinearMap.congr_fun h x

theorem s_mul_self : F.s * F.s = 1 := by
  have h : ((F.s * F.s : V ≃ₗ[K] V) : V →ₗ[K] V) = ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.s (F.s (F.e i)) = F.e i
    rw [F.s_e]
    fin_cases i <;> simp [F.s_e]
  exact LinearEquiv.ext fun x => LinearMap.congr_fun h x

theorem q_e0sub_e1 : Q (F.e 0 - F.e 1) = 2 := by
  have h : Q (F.e 0 - F.e 1) = Q (F.e 0) + Q (F.e 1) - polar Q (F.e 0) (F.e 1) := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, polar_neg_right]
    ring
  rw [h, F.norm 0 (by norm_num), F.norm 1 (by norm_num), F.orth 0 1 (by norm_num)]
  norm_num

theorem polar_e0sub_e1_e0 : polar Q (F.e 0 - F.e 1) (F.e 0) = 2 := by
  rw [QuadraticMap.polar_sub_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    F.norm 0 (by norm_num), F.orth 1 0 (by norm_num)]
  norm_num

theorem reflect_e0sub_e1_e0 : reflect Q (F.e 0 - F.e 1) (F.e 0) = F.e 1 := by
  let _ : Invertible (Q (F.e 0 - F.e 1)) :=
    invertibleOfNonzero (by rw [F.q_e0sub_e1]; exact F.two_ne_zero)
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection,
    TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq Q (F.e 0) (F.e 1)
      (by rw [F.norm 0 (by norm_num), F.norm 1 (by norm_num)])]

theorem t_mem_commutator :
    F.t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  let a : V ≃ₗ[K] V := reflect Q (F.e 0)
  let h : V ≃ₗ[K] V := reflect Q (F.e 0 - F.e 1)
  have hconj : h * a * h = reflect Q (F.e 1) := by
    have hh := CFSG.ClassicalGroups.Orthogonal.reflect_conj
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q (F.e 0 - F.e 1)) (F.e 0)
    rw [F.reflect_e0sub_e1_e0] at hh
    rwa [CFSG.ClassicalGroups.Orthogonal.reflect_inv] at hh
  have hcomm : ⁅a, h⁆ = F.t := by
    rw [commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
      CFSG.ClassicalGroups.Orthogonal.reflect_inv]
    calc a * h * a * h = a * (h * a * h) := by group
      _ = a * reflect Q (F.e 1) := by rw [hconj]
      _ = F.t := by rw [F.t_eq_reflect_mul]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q (F.e 0))
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q (F.e 0 - F.e 1))


theorem polar_vSub_wSub : polar Q (F.e 0 - F.e 2) (F.e 1 - F.e 3) = 0 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_sub_right, F.orth 0 1 (by norm_num), F.orth 0 3 (by norm_num),
    F.orth 2 1 (by norm_num), F.orth 2 3 (by norm_num)]
  ring

theorem q_uSub : Q ((F.e 0 - F.e 2) - (F.e 1 - F.e 3)) = 4 := by
  have h : Q ((F.e 0 - F.e 2) - (F.e 1 - F.e 3)) =
      Q (F.e 0 - F.e 2) + Q (F.e 1 - F.e 3) -
        polar Q (F.e 0 - F.e 2) (F.e 1 - F.e 3) := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q, polar_neg_right]
    ring
  rw [h, F.q_e0_sub_e2, F.q_e1_sub_e3, F.polar_vSub_wSub]
  norm_num

theorem polar_uSub_vSub : polar Q ((F.e 0 - F.e 2) - (F.e 1 - F.e 3)) (F.e 0 - F.e 2) = 4 := by
  rw [QuadraticMap.polar_sub_left, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
    F.q_e0_sub_e2, show polar Q (F.e 1 - F.e 3) (F.e 0 - F.e 2) = 0 from by
      rw [polar_comm, F.polar_vSub_wSub]]
  norm_num

theorem reflect_uSub_vSub :
    reflect Q ((F.e 0 - F.e 2) - (F.e 1 - F.e 3)) (F.e 0 - F.e 2) = F.e 1 - F.e 3 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero F.two_ne_zero F.two_ne_zero
  have hv : Q ((F.e 0 - F.e 2) - (F.e 1 - F.e 3)) ≠ 0 := by
    rw [F.q_uSub]; exact h4
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hv, F.polar_uSub_vSub, F.q_uSub]
  have h44 : (4 : K) / 4 = 1 := div_self h4
  rw [h44, one_smul]
  abel

theorem s_mem_commutator :
    F.s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  let a : V ≃ₗ[K] V := reflect Q (F.e 0 - F.e 2)
  let h : V ≃ₗ[K] V := reflect Q ((F.e 0 - F.e 2) - (F.e 1 - F.e 3))
  have hconj : h * a * h = reflect Q (F.e 1 - F.e 3) := by
    have hh := CFSG.ClassicalGroups.Orthogonal.reflect_conj
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q
        ((F.e 0 - F.e 2) - (F.e 1 - F.e 3))) (F.e 0 - F.e 2)
    rw [F.reflect_uSub_vSub] at hh
    rwa [CFSG.ClassicalGroups.Orthogonal.reflect_inv] at hh
  have hcomm : ⁅a, h⁆ = F.s := by
    rw [commutatorElement_def, CFSG.ClassicalGroups.Orthogonal.reflect_inv,
      CFSG.ClassicalGroups.Orthogonal.reflect_inv]
    calc a * h * a * h = a * (h * a * h) := by group
      _ = a * reflect Q (F.e 1 - F.e 3) := by rw [hconj]
      _ = F.s := by rw [F.s_eq_reflect_mul]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q (F.e 0 - F.e 2))
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup Q
      ((F.e 0 - F.e 2) - (F.e 1 - F.e 3)))

theorem z_mem_commutator :
    F.z ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  let L := ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  have hs : F.s * F.t * F.s ∈ L := by
    have hcomm : ⁅F.s, F.t⁆ = F.s * F.t * F.s * F.t := by
      rw [commutatorElement_def,
        show F.s⁻¹ = F.s from inv_eq_of_mul_eq_one_right F.s_mul_self,
        show F.t⁻¹ = F.t from inv_eq_of_mul_eq_one_right F.t_mul_self]
    have hmem : ⁅F.s, F.t⁆ ∈ L :=
      Subgroup.commutator_mem_commutator F.s_mem F.t_mem
    have heq : F.s * F.t * F.s = ⁅F.s, F.t⁆ * F.t := by
      symm
      calc ⁅F.s, F.t⁆ * F.t = (F.s * F.t * F.s * F.t) * F.t := by rw [hcomm]
        _ = F.s * F.t * F.s * (F.t * F.t) := by group
        _ = F.s * F.t * F.s := by rw [F.t_mul_self, mul_one]
    rw [heq]
    exact L.mul_mem hmem F.t_mem_commutator
  rw [F.z_eq_mul_conj]
  exact Subgroup.mul_mem L F.t_mem_commutator hs


private theorem betaCoord_single_zero (d1 d2 : GL (Fin 2) K) :
    betaCoord d1 d2 (Pi.single 0 1) =
      (d1 : Matrix (Fin 2) (Fin 2) K) 0 0 • Pi.single 0 1 +
        (d1 : Matrix (Fin 2) (Fin 2) K) 1 0 • Pi.single 1 1 := by
  ext j
  rw [betaCoord, glToLinEquiv_apply]
  fin_cases j <;> simp [betaGL, betaMat5, betaMatIdx, Matrix.mulVec, Matrix.reindex_apply,
    Matrix.fromBlocks, Pi.single_apply]

private theorem betaCoord_single_one (d1 d2 : GL (Fin 2) K) :
    betaCoord d1 d2 (Pi.single 1 1) =
      (d1 : Matrix (Fin 2) (Fin 2) K) 0 1 • Pi.single 0 1 +
        (d1 : Matrix (Fin 2) (Fin 2) K) 1 1 • Pi.single 1 1 := by
  ext j
  rw [betaCoord, glToLinEquiv_apply]
  fin_cases j <;> simp [betaGL, betaMat5, betaMatIdx, Matrix.mulVec, Matrix.reindex_apply,
    Matrix.fromBlocks, Pi.single_apply]

private theorem betaCoord_single_two (d1 d2 : GL (Fin 2) K) :
    betaCoord d1 d2 (Pi.single 2 1) =
      (d2 : Matrix (Fin 2) (Fin 2) K) 0 0 • Pi.single 2 1 +
        (d2 : Matrix (Fin 2) (Fin 2) K) 1 0 • Pi.single 3 1 := by
  ext j
  rw [betaCoord, glToLinEquiv_apply]
  fin_cases j <;> simp [betaGL, betaMat5, betaMatIdx, Matrix.mulVec, Matrix.reindex_apply,
    Matrix.fromBlocks, Pi.single_apply]

private theorem betaCoord_single_three (d1 d2 : GL (Fin 2) K) :
    betaCoord d1 d2 (Pi.single 3 1) =
      (d2 : Matrix (Fin 2) (Fin 2) K) 0 1 • Pi.single 2 1 +
        (d2 : Matrix (Fin 2) (Fin 2) K) 1 1 • Pi.single 3 1 := by
  ext j
  rw [betaCoord, glToLinEquiv_apply]
  fin_cases j <;> simp [betaGL, betaMat5, betaMatIdx, Matrix.mulVec, Matrix.reindex_apply,
    Matrix.fromBlocks, Pi.single_apply]

private theorem betaCoord_single_four (d1 d2 : GL (Fin 2) K) :
    betaCoord d1 d2 (Pi.single 4 1) =
      ((d1 : Matrix (Fin 2) (Fin 2) K).det * (d2 : Matrix (Fin 2) (Fin 2) K).det) •
        Pi.single 4 1 := by
  ext j
  rw [betaCoord, glToLinEquiv_apply]
  fin_cases j <;> simp [betaGL, betaMat5, betaMatIdx, Matrix.mulVec, Matrix.reindex_apply,
    Matrix.fromBlocks, Pi.single_apply]

theorem O2_entry_00 (d : O2 K) :
    ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) d.property
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using h

theorem O2_entry_01 (d : O2 K) :
    ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 +
      ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) d.property
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using h

theorem O2_entry_11 (d : O2 K) :
    ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 +
      ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) d.property
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using h

theorem O2_det_sq (d : O2 K) :
    ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
      ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M.det) d.property
  simpa [Matrix.det_mul, Matrix.det_transpose] using h

private theorem coordForm_plane01 (a b : K) :
    F.coordForm (a • Pi.single 0 1 + b • Pi.single 1 1) = a ^ 2 + b ^ 2 := by
  rw [QuadraticMap.map_add F.coordForm, QuadraticMap.map_smul F.coordForm,
    QuadraticMap.map_smul F.coordForm,
    F.coordForm_single_of_lt 0 (by norm_num), F.coordForm_single_of_lt 1 (by norm_num)]
  simp [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    F.polar_coordForm_single_eq_zero (i := 0) (j := 1) (by norm_num)]
  ring

private theorem coordForm_plane23 (a b : K) :
    F.coordForm (a • Pi.single 2 1 + b • Pi.single 3 1) = a ^ 2 + b ^ 2 := by
  rw [QuadraticMap.map_add F.coordForm, QuadraticMap.map_smul F.coordForm,
    QuadraticMap.map_smul F.coordForm,
    F.coordForm_single_of_lt 2 (by norm_num), F.coordForm_single_of_lt 3 (by norm_num)]
  simp [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
    F.polar_coordForm_single_eq_zero (i := 2) (j := 3) (by norm_num)]
  ring

private theorem coordForm_line4 (c : K) :
    F.coordForm (c • Pi.single 4 1) = c ^ 2 * Q (F.e 4) := by
  rw [QuadraticMap.map_smul F.coordForm, F.coordForm_single_four]
  ring

theorem betaCoord_single (d1 d2 : GL (Fin 2) K) (i : Fin 5) :
    betaCoord d1 d2 (Pi.single i 1) =
      if i = 0 then
        (d1 : Matrix (Fin 2) (Fin 2) K) 0 0 • Pi.single 0 1 +
          (d1 : Matrix (Fin 2) (Fin 2) K) 1 0 • Pi.single 1 1
      else if i = 1 then
        (d1 : Matrix (Fin 2) (Fin 2) K) 0 1 • Pi.single 0 1 +
          (d1 : Matrix (Fin 2) (Fin 2) K) 1 1 • Pi.single 1 1
      else if i = 2 then
        (d2 : Matrix (Fin 2) (Fin 2) K) 0 0 • Pi.single 2 1 +
          (d2 : Matrix (Fin 2) (Fin 2) K) 1 0 • Pi.single 3 1
      else if i = 3 then
        (d2 : Matrix (Fin 2) (Fin 2) K) 0 1 • Pi.single 2 1 +
          (d2 : Matrix (Fin 2) (Fin 2) K) 1 1 • Pi.single 3 1
      else
        ((d1 : Matrix (Fin 2) (Fin 2) K).det * (d2 : Matrix (Fin 2) (Fin 2) K).det) •
          Pi.single 4 1 := by
  fin_cases i <;> simp [betaCoord_single_zero, betaCoord_single_one, betaCoord_single_two,
    betaCoord_single_three, betaCoord_single_four]

theorem O2_entry_10 (d : O2 K) :
    ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 *
        ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  rw [add_comm, ← O2_entry_01 d]
  ring

private theorem betaCoord_mem (d1 d2 : O2 K) :
    betaCoord (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K) ∈
      TauCeti.QuadraticMap.orthogonalGroup F.coordForm := by
  refine CFSG.ClassicalGroups.Orthogonal.mem_orthogonalGroup_of_basis F.coordForm _ ?_ ?_
  · intro i
    rw [betaCoord_single]
    fin_cases i <;>
      simp [F.coordForm_plane01, F.coordForm_plane23, F.coordForm_line4,
        F.coordForm_single_of_lt, F.coordForm_single_four, pow_two,
        O2_entry_00 d1, O2_entry_11 d1, O2_entry_00 d2, O2_entry_11 d2,
        O2_det_sq d1, O2_det_sq d2]
    · have hc : (((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
          ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) *
          (((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
            ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
        rw [mul_mul_mul_comm, O2_det_sq d1, O2_det_sq d2, one_mul]
      rw [hc, one_mul]
  · intro i j
    rw [betaCoord_single, betaCoord_single]
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
        F.coordForm_single_of_lt, F.coordForm_single_four,
        F.coordForm_plane01, F.coordForm_plane23, F.coordForm_line4, pow_two,
        F.polar_coordForm_single_eq_zero, QuadraticMap.polar_self,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul,
        O2_entry_00 d1, O2_entry_01 d1, O2_entry_10 d1, O2_entry_11 d1,
        O2_entry_00 d2, O2_entry_01 d2, O2_entry_10 d2, O2_entry_11 d2,
        O2_det_sq d1, O2_det_sq d2]
    all_goals try linear_combination 2 * O2_entry_01 d1
    all_goals try linear_combination 2 * O2_entry_10 d1
    all_goals try linear_combination 2 * O2_entry_01 d2
    all_goals try linear_combination 2 * O2_entry_10 d2
    left
    have hc : (((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) *
        (((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
          ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
      rw [mul_mul_mul_comm, O2_det_sq d1, O2_det_sq d2, one_mul]
    rw [hc]
    ring

def beta (d1 d2 : O2 K) : V ≃ₗ[K] V :=
  F.conjCoord (betaCoord (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K))

@[simp] theorem beta_e_zero (d1 d2 : O2 K) :
    F.beta d1 d2 (F.e 0) =
      ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 • F.e 0 +
        ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 • F.e 1 := by
  rw [beta, F.conjCoord_e, betaCoord_single_zero, map_add, map_smul, map_smul]
  simp [F.coord_symm_single]

@[simp] theorem beta_e_one (d1 d2 : O2 K) :
    F.beta d1 d2 (F.e 1) =
      ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 • F.e 0 +
        ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 • F.e 1 := by
  rw [beta, F.conjCoord_e, betaCoord_single_one, map_add, map_smul, map_smul]
  simp [F.coord_symm_single]

@[simp] theorem beta_e_two (d1 d2 : O2 K) :
    F.beta d1 d2 (F.e 2) =
      ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 • F.e 2 +
        ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 • F.e 3 := by
  rw [beta, F.conjCoord_e, betaCoord_single_two, map_add, map_smul, map_smul]
  simp [F.coord_symm_single]

@[simp] theorem beta_e_three (d1 d2 : O2 K) :
    F.beta d1 d2 (F.e 3) =
      ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 • F.e 2 +
        ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 • F.e 3 := by
  rw [beta, F.conjCoord_e, betaCoord_single_three, map_add, map_smul, map_smul]
  simp [F.coord_symm_single]

@[simp] theorem beta_e_four (d1 d2 : O2 K) :
    F.beta d1 d2 (F.e 4) =
      (((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
        ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) • F.e 4 := by
  rw [beta, F.conjCoord_e, betaCoord_single_four, map_smul]
  simp [F.coord_symm_single]

theorem beta_injective : Function.Injective (fun p : O2 K × O2 K => F.beta p.1 p.2) := by
  rintro ⟨d1, d2⟩ ⟨e1, e2⟩ h
  have h0 := congrArg (fun g => F.coord (g (F.e 0))) h
  have h1 := congrArg (fun g => F.coord (g (F.e 1))) h
  have h2 := congrArg (fun g => F.coord (g (F.e 2))) h
  have h3 := congrArg (fun g => F.coord (g (F.e 3))) h
  simp [F.beta_e_zero, F.beta_e_one, F.beta_e_two, F.beta_e_three, map_add, map_smul,
    Pi.smul_apply, Pi.add_apply] at h0 h1 h2 h3
  have hd00 : ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((e1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have := congrArg (fun f : Fin 5 → K => f 0) h0
    simpa using this
  have hd10 : ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((e1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    have := congrArg (fun f : Fin 5 → K => f 1) h0
    simpa using this
  have hd01 : ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((e1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    have := congrArg (fun f : Fin 5 → K => f 0) h1
    simpa using this
  have hd11 : ((d1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((e1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have := congrArg (fun f : Fin 5 → K => f 1) h1
    simpa using this
  have he00 : ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((e2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    have := congrArg (fun f : Fin 5 → K => f 2) h2
    simpa using this
  have he10 : ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      ((e2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    have := congrArg (fun f : Fin 5 → K => f 3) h2
    simpa using this
  have he01 : ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      ((e2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    have := congrArg (fun f : Fin 5 → K => f 2) h3
    simpa using this
  have he11 : ((d2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((e2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have := congrArg (fun f : Fin 5 → K => f 3) h3
    simpa using this
  have hd1 : (d1 : GL (Fin 2) K) = (e1 : GL (Fin 2) K) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  have hd2 : (d2 : GL (Fin 2) K) = (e2 : GL (Fin 2) K) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  exact Prod.ext (Subtype.ext hd1) (Subtype.ext hd2)

private theorem det_betaCoord (d1 d2 : O2 K) :
    LinearEquiv.det (betaCoord (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K)) = 1 := by
  have hmat : LinearMap.toMatrix'
      (betaCoord (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K)).toLinearMap =
      ((betaGL (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, betaCoord, glToLinEquiv_apply, Matrix.mulVec,
      Pi.single_apply]
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix'
    (betaCoord (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K)).toLinearMap, hmat]
  rw [show ((betaGL (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = betaMat5 (d1 : GL (Fin 2) K) (d2 : GL (Fin 2) K) from
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _]
  rw [betaMat5, Matrix.det_reindex]
  have hsign : Equiv.Perm.sign (idxEquiv.trans idxEquiv.symm) = 1 := by
    rw [show idxEquiv.trans idxEquiv.symm = Equiv.refl (Fin 2 ⊕ (Fin 2 ⊕ Fin 1)) from by
      ext x; simp]
    rfl
  rw [hsign, betaMatIdx_det]
  norm_num
  rw [mul_mul_mul_comm, O2_det_sq d1, O2_det_sq d2, one_mul]

theorem beta_mem (d1 d2 : O2 K) :
    F.beta d1 d2 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  F.conjCoord_mem (betaCoord_mem (F := F) d1 d2)

abbrev betaO (F : FrameData Q) (d1 d2 : O2 K) : TauCeti.QuadraticMap.orthogonalGroup Q :=
  ⟨F.beta d1 d2, F.beta_mem d1 d2⟩

theorem beta_so (d1 d2 : O2 K) : F.betaO d1 d2 ∈ Q.specialOrthogonalWithin := by
  rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
  have hdet : LinearEquiv.det (F.beta d1 d2) = 1 := by
    rw [beta, F.det_conjCoord_eq, det_betaCoord]
  simpa [betaO] using hdet

abbrev betaSO (F : FrameData Q) (d1 d2 : O2 K) : Q.specialOrthogonalWithin :=
  ⟨F.betaO d1 d2, F.beta_so d1 d2⟩



theorem beta_mul (d1 d2 e1 e2 : O2 K) :
    F.beta d1 d2 * F.beta e1 e2 = F.beta (d1 * e1) (d2 * e2) := by
  apply LinearEquiv.ext
  intro x
  have h : ((F.beta d1 d2 * F.beta e1 e2 : V ≃ₗ[K] V) : V →ₗ[K] V) =
      ((F.beta (d1 * e1) (d2 * e2) : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.beta d1 d2 (F.beta e1 e2 (F.e i)) = F.beta (d1 * e1) (d2 * e2) (F.e i)
    fin_cases i <;>
      simp [F.beta_e_zero, F.beta_e_one, F.beta_e_two, F.beta_e_three, F.beta_e_four,
        map_add, map_smul, Matrix.mul_apply, Fin.sum_univ_two, Subgroup.coe_mul,
        Matrix.det_mul]
    all_goals module
  exact LinearMap.congr_fun h x

theorem beta_one : F.beta (1 : O2 K) (1 : O2 K) = 1 := by
  apply LinearEquiv.ext
  intro x
  have h : ((F.beta (1 : O2 K) (1 : O2 K) : V ≃ₗ[K] V) : V →ₗ[K] V) =
      ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.beta (1 : O2 K) (1 : O2 K) (F.e i) = F.e i
    fin_cases i <;>
      simp [F.beta_e_zero, F.beta_e_one, F.beta_e_two, F.beta_e_three, F.beta_e_four]
  exact LinearMap.congr_fun h x

theorem betaO_mul (d1 d2 e1 e2 : O2 K) :
    F.betaO d1 d2 * F.betaO e1 e2 = F.betaO (d1 * e1) (d2 * e2) := by
  apply Subtype.ext
  exact F.beta_mul d1 d2 e1 e2

theorem betaO_one : F.betaO (1 : O2 K) (1 : O2 K) = 1 := by
  apply Subtype.ext
  exact F.beta_one

theorem s_beta_s (d1 d2 : O2 K) :
    F.s * F.beta d1 d2 * F.s = F.beta d2 d1 := by
  apply LinearEquiv.ext
  intro x
  have h : ((F.s * F.beta d1 d2 * F.s : V ≃ₗ[K] V) : V →ₗ[K] V) =
      ((F.beta d2 d1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    apply F.e.ext
    intro i
    change F.s (F.beta d1 d2 (F.s (F.e i))) = F.beta d2 d1 (F.e i)
    fin_cases i <;>
      simp [F.s_e, F.beta_e_zero, F.beta_e_one, F.beta_e_two, F.beta_e_three,
        F.beta_e_four, map_add, map_smul]
    all_goals module
  exact LinearMap.congr_fun h x

theorem sO_mul_self : F.sO * F.sO = 1 := by
  apply Subtype.ext
  exact F.s_mul_self

theorem sO_betaO_conj (d1 d2 : O2 K) :
    F.sO * F.betaO d1 d2 * F.sO⁻¹ = F.betaO d2 d1 := by
  have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
  rw [hs]
  apply Subtype.ext
  exact F.s_beta_s d1 d2


@[expose] def sigmaO2 : O2 K :=
  ⟨Sp48.O2Plane.sig K, Sp48.O2Plane.sig_mem_O2⟩

theorem sigmaO2_coe : (sigmaO2 (K := K) : GL (Fin 2) K) = Sp48.O2Plane.sig K := rfl

theorem sigmaO2_mul_self : sigmaO2 (K := K) * sigmaO2 = 1 := by
  apply Subtype.ext
  exact Sp48.O2Plane.sig_mul_self

theorem betaO_inv_left (F : FrameData Q) (d : O2 K) :
    (F.betaO d (1 : O2 K))⁻¹ = F.betaO d⁻¹ 1 := by
  apply inv_eq_of_mul_eq_one_right
  simpa [F.betaO_one] using F.betaO_mul d 1 d⁻¹ 1

theorem betaO_inv_right (F : FrameData Q) (d : O2 K) :
    (F.betaO (1 : O2 K) d)⁻¹ = F.betaO 1 d⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  simpa [F.betaO_one] using F.betaO_mul 1 d 1 d⁻¹

theorem sO_betaO_conj' (F : FrameData Q) (d1 d2 : O2 K) :
    F.sO * F.betaO d1 d2 * F.sO = F.betaO d2 d1 := by
  have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
  simpa [hs] using F.sO_betaO_conj d1 d2

theorem commutator_betaO_left (F : FrameData Q) (d : O2 K) :
    ⁅F.betaO d (1 : O2 K), F.sO⁆ = F.betaO d d⁻¹ := by
  rw [commutatorElement_def, F.betaO_inv_left]
  calc F.betaO d 1 * F.sO * F.betaO d⁻¹ 1 * F.sO
      = F.betaO d 1 * (F.sO * F.betaO d⁻¹ 1 * F.sO) := by group
    _ = F.betaO d 1 * F.betaO 1 d⁻¹ := by rw [F.sO_betaO_conj']
    _ = F.betaO d d⁻¹ := by
        rw [F.betaO_mul]
        congr 2 <;> simp

theorem conj_sigma_eq (r : O2 K) (hr : (r : GL (Fin 2) K) ∈ Sp48.O2Plane.SO2 K) :
    sigmaO2 * r * sigmaO2 = r⁻¹ := by
  have hsr : sigmaO2 * r * sigmaO2 * r = 1 := by
    apply Subtype.ext
    exact Sp48.O2Plane.sig_mul_mul_sig_mul_SO2 hr
  calc sigmaO2 * r * sigmaO2
      = (sigmaO2 * r * sigmaO2 * r) * r⁻¹ := by group
    _ = 1 * r⁻¹ := by rw [hsr]
    _ = r⁻¹ := one_mul _

theorem conj_sigma_inv_eq (r : O2 K) (hr : (r : GL (Fin 2) K) ∈ Sp48.O2Plane.SO2 K) :
    sigmaO2 * r⁻¹ * sigmaO2 = r := by
  have h1 := conj_sigma_eq r hr
  calc sigmaO2 * r⁻¹ * sigmaO2
      = sigmaO2 * (sigmaO2 * r * sigmaO2) * sigmaO2 := by rw [← h1]
    _ = (sigmaO2 * sigmaO2) * r * (sigmaO2 * sigmaO2) := by group
    _ = r := by rw [sigmaO2_mul_self]; simp

theorem commutator_betaO_sigma (F : FrameData Q) (r : O2 K)
    (hr : (r : GL (Fin 2) K) ∈ Sp48.O2Plane.SO2 K) :
    ⁅F.betaO (1 : O2 K) r, F.betaO 1 (sigmaO2 (K := K))⁆ = F.betaO 1 (r * r) := by
  have hcomm : r * sigmaO2 * r⁻¹ * sigmaO2 = r * r := by
    calc r * sigmaO2 * r⁻¹ * sigmaO2
        = r * (sigmaO2 * r⁻¹ * sigmaO2) := by group
      _ = r * r := by rw [conj_sigma_inv_eq r hr]
  rw [commutatorElement_def, F.betaO_inv_right, F.betaO_inv_right]
  rw [F.betaO_mul, F.betaO_mul, F.betaO_mul]
  simp only [one_mul, mul_one]
  rw [inv_eq_of_mul_eq_one_right sigmaO2_mul_self]
  rw [hcomm]

theorem betaO_diag_rotation (F : FrameData Q) (r : O2 K)
    (hr : (r : GL (Fin 2) K) ∈ Sp48.O2Plane.SO2 K) :
    (F.betaO r r : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hleft : (F.betaO r r⁻¹ : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [← F.commutator_betaO_left r]
    exact Subgroup.commutator_mem_commutator (F.betaO r 1).property F.sO.property
  have hright : (F.betaO (1 : O2 K) (r * r) : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    rw [← F.commutator_betaO_sigma r hr]
    exact Subgroup.commutator_mem_commutator (F.betaO 1 r).property
      (F.betaO 1 (sigmaO2 (K := K))).property
  have hmul : F.betaO r r = F.betaO r r⁻¹ * F.betaO 1 (r * r) := by
    rw [F.betaO_mul]
    congr 2
    · simp
    · group
  rw [hmul]
  exact Subgroup.mul_mem _ hleft hright

theorem betaO_diag_sigma (F : FrameData Q) :
    (F.betaO (sigmaO2 (K := K)) sigmaO2 : V ≃ₗ[K] V) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hcomm : F.betaO (sigmaO2 (K := K)) sigmaO2 =
      ⁅F.betaO (sigmaO2 (K := K)) 1, F.sO⁆ := by
    rw [F.commutator_betaO_left (sigmaO2 (K := K)),
      inv_eq_of_mul_eq_one_right sigmaO2_mul_self]
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (F.betaO sigmaO2 1).property F.sO.property

theorem betaO_diag_mem_commutator (F : FrameData Q) (d : O2 K) :
    (F.betaO d d : V ≃ₗ[K] V) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rcases Sp48.O2Plane.O2_cases (F := K) d.property with hd | hd
  · exact F.betaO_diag_rotation d hd
  · let r : O2 K :=
      ⟨Sp48.O2Plane.sig K * (d : GL (Fin 2) K), Sp48.O2Plane.SO2_le_O2 hd⟩
    have hd_eq : d = sigmaO2 * r := by
      apply Subtype.ext
      dsimp only [sigmaO2, r]
      simp only [Subgroup.coe_mul, Subgroup.coe_mk]
      rw [← mul_assoc, Sp48.O2Plane.sig_mul_self, one_mul]
    rw [hd_eq, ← F.betaO_mul]
    exact Subgroup.mul_mem _ F.betaO_diag_sigma (F.betaO_diag_rotation r hd)



@[expose] def betaHom : (O2 K × O2 K) →* TauCeti.QuadraticMap.orthogonalGroup Q where
  toFun p := F.betaO p.1 p.2
  map_one' := F.betaO_one
  map_mul' p q := by
    simpa using (F.betaO_mul p.1 p.2 q.1 q.2).symm

theorem betaHom_apply (p : O2 K × O2 K) : F.betaHom p = F.betaO p.1 p.2 := rfl

theorem betaHom_injective : Function.Injective F.betaHom := by
  intro p q h
  apply F.beta_injective
  exact congrArg Subtype.val h

end FrameData

end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
