module

public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore
public import TauCeti.Algebra.Group.Units.Basic

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Matrix CFSG Subgroup TauCeti QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def isoHom (Q : QuadraticForm K (Fin d → K)) :
    matrixIsometries Q →* TauCeti.QuadraticMap.orthogonalGroup Q where
  toFun A := ⟨matrixLinearIso (A : GL (Fin d) K), A.2⟩
  map_one' := Subtype.ext (map_one matrixLinearIso)
  map_mul' A B := Subtype.ext (map_mul matrixLinearIso (A : GL (Fin d) K) B)

theorem coe_isoHom_apply (Q : QuadraticForm K (Fin d → K)) (A : matrixIsometries Q)
    (v : Fin d → K) : ((isoHom Q A : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin d → K) ≃ₗ[K] (Fin d → K)) v = ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v :=
  rfl

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem polar_oQ_diagGL (x y : Fin d → K) :
    polar (oQ (diagGL hw)) x y = 2 * ∑ i, w i * x i * y i := by
  simp only [polar, oQ_apply, coe_diagGL, mulVec_diagonal, dotProduct, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  funext i
  ring

theorem oQ_diagGL_single (i : Fin d) : oQ (diagGL hw) (Pi.single i 1) = w i := by
  rw [oQ_apply, coe_diagGL]
  simp [dotProduct, Matrix.mulVec, Matrix.diagonal_apply, Pi.single_apply]

theorem signGL_mem_matrixIsometries (h2 : (2 : K) ≠ 0) (T : Finset (Fin d)) :
    signGL K T ∈ matrixIsometries (oQ (diagGL hw)) := by
  rw [matrixIsometries_oQ h2 _ (diagGL_transpose hw)]
  exact signGL_mem hw T

theorem isoHom_signGL_single (h2 : (2 : K) ≠ 0) (i : Fin d) :
    ((isoHom (oQ (diagGL hw)) ⟨signGL K {i}, signGL_mem_matrixIsometries hw h2 {i}⟩ :
      TauCeti.QuadraticMap.orthogonalGroup (oQ (diagGL hw))) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) = reflect (oQ (diagGL hw)) (Pi.single i 1) := by
  have hQ : oQ (diagGL hw) (Pi.single i 1) ≠ 0 := by rw [oQ_diagGL_single hw]; exact hw i
  refine LinearEquiv.ext fun x => ?_
  rw [coe_isoHom_apply, reflect_apply hQ, polar_oQ_diagGL hw, oQ_diagGL_single hw,
    Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  funext j
  simp only [coe_signGL, signMat, mulVec_diagonal, Finset.mem_singleton, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = i
  · subst hj
    simp only [ite_true, Pi.single_eq_same, mul_one]
    field_simp [hw j]
    ring
  · simp [hj]

theorem signGL_empty' : signGL K (∅ : Finset (Fin d)) = 1 := by
  apply Units.ext
  rw [coe_signGL, Units.val_one]
  ext i j
  simp [signMat, diagonal_apply, Matrix.one_apply]

theorem signGL_insert {i : Fin d} {T : Finset (Fin d)} (hiT : i ∉ T) :
    signGL K (insert i T) = signGL K {i} * signGL K T := by
  apply Units.ext
  rw [Units.val_mul, coe_signGL, coe_signGL, coe_signGL, signMat, signMat, signMat,
    diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp [hiT]
  · simp [hk]

variable [Finite K]

theorem detSpinorNorm_isoHom_signGL (hK : ringChar K ≠ 2)
    (hQ : (oQ (diagGL hw)).Nondegenerate) (T : Finset (Fin d)) :
    let _ : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
    ClassicalInvolution.detSpinorNorm hQ
        (isoHom (oQ (diagGL hw)) ⟨signGL K T, signGL_mem_matrixIsometries hw
          (Ring.two_ne_zero hK) T⟩) =
      ((-1) ^ T.card, squareClassHom (∏ i ∈ T, Units.mk0 (w i) (hw i))) := by
  intro _
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  classical
  induction T using Finset.induction_on with
  | empty =>
    have e : (⟨signGL K ∅, signGL_mem_matrixIsometries hw h2 ∅⟩ :
        matrixIsometries (oQ (diagGL hw))) = 1 := Subtype.ext signGL_empty'
    rw [e, map_one, map_one, Finset.card_empty, pow_zero, Finset.prod_empty, map_one]
    rfl
  | insert i T hiT ih =>
    have e : (⟨signGL K (insert i T), signGL_mem_matrixIsometries hw h2 _⟩ :
        matrixIsometries (oQ (diagGL hw))) =
        ⟨signGL K {i}, signGL_mem_matrixIsometries hw h2 {i}⟩ *
          ⟨signGL K T, signGL_mem_matrixIsometries hw h2 T⟩ :=
      Subtype.ext (signGL_insert hiT)
    have hQi : oQ (diagGL hw) (Pi.single i 1) ≠ 0 := by rw [oQ_diagGL_single hw]; exact hw i
    let _ : Invertible (oQ (diagGL hw) (Pi.single i 1)) := invertibleOfNonzero hQi
    have hrefl : isoHom (oQ (diagGL hw)) ⟨signGL K {i}, signGL_mem_matrixIsometries hw h2 {i}⟩ =
        TauCeti.QuadraticMap.reflectionOrthogonal (oQ (diagGL hw)) (Pi.single i 1) := by
      apply Subtype.ext
      rw [isoHom_signGL_single hw h2 i, ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect]
    rw [e, map_mul, map_mul, ih, hrefl, ClassicalInvolution.detSpinorNorm_reflectionOrthogonal,
      Prod.mk_mul_mk, Finset.card_insert_of_notMem hiT, Finset.prod_insert hiT, map_mul, pow_succ,
      mul_comm ((-1 : Kˣ) ^ T.card)]
    congr 2
    congr 1
    apply Units.ext
    rw [val_unitOfInvertible, Units.val_mk0, oQ_diagGL_single hw]

theorem isSquare_prod_of_signGL_mem (hK : ringChar K ≠ 2) {T : Finset (Fin d)}
    (hT : signGL K T ∈ matrixDerived (oQ (diagGL hw))) : IsSquare (∏ i ∈ T, w i) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  have hnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK
    (diagGL hw) (diagGL_transpose hw)
  have hQ : (oQ (diagGL hw)).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hnd
  set Φ := (ClassicalInvolution.detSpinorNorm hQ).comp (isoHom (oQ (diagGL hw))) with hΦ
  have hker : commutator (matrixIsometries (oQ (diagGL hw))) ≤ Φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (Φ g₁) (Φ g₂))
  rw [matrixDerived_eq_map_commutator] at hT
  obtain ⟨s, hs, hsT⟩ := hT
  have hs' : s = ⟨signGL K T, signGL_mem_matrixIsometries hw h2 T⟩ := Subtype.ext hsT
  have h1 := hker hs
  rw [MonoidHom.mem_ker, hs', hΦ, MonoidHom.comp_apply,
    detSpinorNorm_isoHom_signGL hw hK hQ T] at h1
  have h1' := congrArg Prod.snd h1
  change squareClassHom _ = 1 at h1'
  rw [← MonoidHom.mem_ker, ker_squareClassHom, Subgroup.mem_square,
    ← isSquare_units_val_iff] at h1'
  simpa [Units.coe_prod] using h1'

end CFSG.ComponentClassification.GSThmB.Orth516
