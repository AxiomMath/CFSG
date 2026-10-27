module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K]

@[expose] def determinantForm (K : Type*) [Field K] :
    QuadraticForm K (Matrix (Fin 2) (Fin 2) K) :=
  linMulLin (Matrix.entryLinearMap K K 0 0) (Matrix.entryLinearMap K K 1 1) -
    linMulLin (Matrix.entryLinearMap K K 0 1) (Matrix.entryLinearMap K K 1 0)

theorem determinantForm_apply (X : Matrix (Fin 2) (Fin 2) K) :
    determinantForm K X = X.det := by
  change X 0 0 * X 1 1 - X 0 1 * X 1 0 = X.det
  rw [Matrix.det_fin_two]

theorem determinantForm_polar (X Y : Matrix (Fin 2) (Fin 2) K) :
    polar (determinantForm K) X Y =
      X 0 0 * Y 1 1 + X 1 1 * Y 0 0 - X 0 1 * Y 1 0 - X 1 0 * Y 0 1 := by
  simp only [polar, determinantForm_apply, Matrix.det_fin_two, Matrix.add_apply]
  ring

section OriginalSpace

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_two_hypPairs_of_family [FiniteDimensional K V]
    (hQ : Q.polarBilin.Nondegenerate) {t : Fin 2 → V} (ht : LinearIndependent K t)
    (htQ : ∀ i, Q (t i) = 0) (htB : ∀ i j, polar Q (t i) (t j) = 0) :
    ∃ P R : HypPair Q, P.e = t 0 ∧ R.e = t 1 ∧ P.Orth R := by
  obtain ⟨g, hg⟩ := exists_dual_family hQ ht
  have h00 : polar Q (t 0) (g 0) = 1 := by simpa using hg 0 0
  let P := HypPair.ofPolarEqOne (htQ 0) h00
  have hB1 : ∀ i, polar Q (t i) P.f = polar Q (t i) (g 0) := fun i =>
    HypPair.polar_ofPolarEqOne_f (htQ 0) h00 (htB i 0)
  let h := g 1 - polar Q (g 1) P.f • t 0
  have hth : ∀ i, polar Q (t i) h = polar Q (t i) (g 1) := fun i => by
    dsimp [h]
    rw [polar_sub_right, polar_smul_right_eq, htB, mul_zero, sub_zero]
  have h11 : polar Q (t 1) h = 1 := by rw [hth]; simpa using hg 1 1
  let R := HypPair.ofPolarEqOne (htQ 1) h11
  have hB2 : ∀ i, polar Q (t i) R.f = polar Q (t i) (g 1) := fun i => by
    rw [HypPair.polar_ofPolarEqOne_f (htQ 1) h11 (htB i 1), hth]
  have h10 : polar Q P.f (t 1) = 0 := by
    rw [polar_comm, hB1]
    simpa using hg 1 0
  have hff : polar Q P.f R.f = 0 := by
    change polar Q P.f (h - Q h • t 1) = 0
    rw [polar_sub_right, polar_smul_right_eq, h10, mul_zero, sub_zero]
    dsimp [h]
    rw [polar_sub_right, polar_smul_right_eq, show polar Q P.f (t 0) = 1 from P.polar_fe,
      polar_comm Q (g 1)]
    ring
  refine ⟨P, R, rfl, rfl, ⟨htB 0 1, ?_, h10, hff⟩⟩
  change polar Q (t 0) R.f = 0
  rw [hB2]
  simpa using hg 0 1

theorem exists_two_hypPairs [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    (S : Submodule K V) (hdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0) :
    ∃ P R : HypPair Q, P.Orth R ∧ P.e ∈ S ∧ R.e ∈ S := by
  let b := Module.finBasisOfFinrankEq K S hdim
  let t : Fin 2 → V := fun i => (b i : V)
  have ht : LinearIndependent K t := b.linearIndependent.map' S.subtype S.ker_subtype
  have hm : ∀ i, t i ∈ S := fun i => (b i).2
  obtain ⟨P, R, hP, hR, hPR⟩ := exists_two_hypPairs_of_family hQ ht
    (fun i => hS _ (hm i)) (fun i j => by
      rw [polar, hS _ (S.add_mem (hm i) (hm j)), hS _ (hm i), hS _ (hm j),
        sub_zero, sub_zero])
  exact ⟨P, R, hPR, hP ▸ hm 0, hR ▸ hm 1⟩

@[expose] def matrixToOriginal (P R : HypPair Q) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] V where
  toFun X := X 0 0 • P.e + X 0 1 • R.e + X 1 1 • P.f - X 1 0 • R.f
  map_add' X Y := by simp only [Matrix.add_apply, add_smul]; abel
  map_smul' a X := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, smul_add, smul_sub,
      RingHom.id_apply]

theorem matrixToOriginal_apply (P R : HypPair Q) (X : Matrix (Fin 2) (Fin 2) K) :
    matrixToOriginal P R X = X 0 0 • P.e + X 0 1 • R.e + X 1 1 • P.f - X 1 0 • R.f := rfl

theorem matrixToOriginal_polar (P R : HypPair Q) (h : P.Orth R)
    (X : Matrix (Fin 2) (Fin 2) K) :
    polar Q (matrixToOriginal P R X) P.f = X 0 0 ∧
      polar Q (matrixToOriginal P R X) R.f = X 0 1 ∧
      polar Q (matrixToOriginal P R X) P.e = X 1 1 ∧
      polar Q (matrixToOriginal P R X) R.e = -X 1 0 := by
  simp only [matrixToOriginal_apply, polar_sub_left, polar_add_left, polar_smul_left_eq,
    P.polar_ef, P.polar_fe, P.polar_ee, P.polar_ff, R.polar_ef, R.polar_fe,
    R.polar_ee, R.polar_ff, h.ee, h.ef, h.fe, h.ff,
    h.symm.ee, h.symm.ef, h.symm.fe, h.symm.ff,
    mul_zero, mul_one, add_zero, zero_add, sub_zero, zero_sub, and_self]

theorem matrixToOriginal_injective (P R : HypPair Q) (h : P.Orth R) :
    Function.Injective (matrixToOriginal P R) := by
  intro X Y hXY
  have hx := matrixToOriginal_polar P R h X
  have hy := matrixToOriginal_polar P R h Y
  have h00 := congrArg (fun z => polar Q z P.f) hXY
  have h01 := congrArg (fun z => polar Q z R.f) hXY
  have h11 := congrArg (fun z => polar Q z P.e) hXY
  have h10 := congrArg (fun z => polar Q z R.e) hXY
  rw [hx.1, hy.1] at h00
  rw [hx.2.1, hy.2.1] at h01
  rw [hx.2.2.1, hy.2.2.1] at h11
  rw [hx.2.2.2, hy.2.2.2, neg_inj] at h10
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem matrixToOriginal_form (P R : HypPair Q) (h : P.Orth R)
    (X : Matrix (Fin 2) (Fin 2) K) :
    Q (matrixToOriginal P R X) = X.det := by
  rw [matrixToOriginal_apply, sub_eq_add_neg]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_add Q]
  simp only [QuadraticMap.map_neg, map_smul_eq_sq, P.Q_e, P.Q_f,
    R.Q_e, R.Q_f, polar_add_left, polar_neg_right,
    polar_smul_left_eq, polar_smul_right_eq, P.polar_ef, R.polar_ef,
    h.ee, h.ef, h.ff, h.symm.ef,
    Matrix.det_fin_two]
  ring

@[expose] def determinantCoordinates [FiniteDimensional K V]
    (hdim : Module.finrank K V = 4) (P R : HypPair Q) (h : P.Orth R) :
    Q.IsometryEquiv (determinantForm K) := by
  let e := LinearEquiv.ofBijective (matrixToOriginal P R) ⟨
    matrixToOriginal_injective P R h,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_matrix]
      simpa using hdim.symm)).mp (matrixToOriginal_injective P R h)⟩
  refine { toLinearEquiv := e.symm, map_app' := ?_ }
  intro v
  rw [determinantForm_apply]
  calc
    (e.symm v).det = Q (matrixToOriginal P R (e.symm v)) :=
      (matrixToOriginal_form P R h _).symm
    _ = Q v := congrArg Q (e.apply_symm_apply v)

theorem determinantCoordinates_symm_apply [FiniteDimensional K V]
    (hdim : Module.finrank K V = 4) (P R : HypPair Q) (h : P.Orth R)
    (X : Matrix (Fin 2) (Fin 2) K) :
    (determinantCoordinates hdim P R h).symm X =
      X 0 0 • P.e + X 0 1 • R.e + X 1 1 • P.f - X 1 0 • R.f := rfl

theorem determinantCoordinates_apply [FiniteDimensional K V]
    (hdim : Module.finrank K V = 4) (P R : HypPair Q) (h : P.Orth R) (v : V) :
    determinantCoordinates hdim P R h v =
      !![polar Q v P.f, polar Q v R.f; -polar Q v R.e, polar Q v P.e] := by
  have hv : matrixToOriginal P R (determinantCoordinates hdim P R h v) = v :=
    (determinantCoordinates hdim P R h).symm_apply_apply v
  have hx := matrixToOriginal_polar P R h (determinantCoordinates hdim P R h v)
  rw [hv] at hx
  ext i j
  fin_cases i <;> fin_cases j
  · exact hx.1.symm
  · exact hx.2.1.symm
  · simpa using (congrArg Neg.neg hx.2.2.2).symm
  · exact hx.2.2.1.symm

theorem exists_determinant_isometry [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 4)
    (S : Submodule K V) (hSdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0) :
    Nonempty (Q.IsometryEquiv (determinantForm K)) := by
  obtain ⟨P, R, h, _, _⟩ := exists_two_hypPairs hQ S hSdim hS
  exact ⟨determinantCoordinates hdim P R h⟩

theorem split_four_determinant_form_isometry [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 4)
    (S : Submodule K V) (hSdim : Module.finrank K S = 2) (hS : ∀ x ∈ S, Q x = 0) :
    ∃ psi : V ≃ₗ[K] Matrix (Fin 2) (Fin 2) K,
      ∃ e : TauCeti.QuadraticMap.orthogonalGroup Q ≃*
        TauCeti.QuadraticMap.orthogonalGroup (determinantForm K),
        (∀ v, Q v = (psi v).det) ∧
        (∀ g X, (e g).val X = psi (g.val (psi.symm X))) ∧
        (∀ g v, (e.symm g).val v = psi.symm (g.val (psi v))) := by
  obtain ⟨psi⟩ := exists_determinant_isometry Q hQ hdim S hSdim hS
  refine ⟨psi.toLinearEquiv, TauCeti.QuadraticMap.orthogonalGroupCongr psi, ?_, ?_, ?_⟩
  · intro v
    rw [← psi.map_app, determinantForm_apply]
    rfl
  · exact TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply psi
  · exact TauCeti.QuadraticMap.coe_orthogonalGroupCongr_symm_apply psi

end OriginalSpace

end CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
