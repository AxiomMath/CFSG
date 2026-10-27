module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionSplitMatrix
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix CatalogueBProjectiveInvolution CatalogueBProjectiveCoordinates

variable {K : Type} [Field K] {n : ℕ}

@[expose] def fstSL (r s : ℕ) : Subgroup (GL (Fin r) K × GL (Fin s) K) :=
  ((MonoidHom.inl _ _).comp Matrix.SpecialLinearGroup.toGL).range

@[expose] def sndSL (r s : ℕ) : Subgroup (GL (Fin r) K × GL (Fin s) K) :=
  ((MonoidHom.inr _ _).comp Matrix.SpecialLinearGroup.toGL).range

theorem toGL_conj_mem {s : ℕ} (g : GL (Fin s) K) (w : SpecialLinearGroup (Fin s) K) :
    ∃ w' : SpecialLinearGroup (Fin s) K,
      Matrix.SpecialLinearGroup.toGL w' = g * Matrix.SpecialLinearGroup.toGL w * g⁻¹ := by
  have hN : (Matrix.SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin s) K →* GL (Fin s) K).range.Normal := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    infer_instance
  exact hN.conj_mem _ ⟨w, rfl⟩ g

instance fstSL_normal (r s : ℕ) : (fstSL (K := K) r s).Normal := ⟨fun x hx g => by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', hw'⟩ := toGL_conj_mem g.1 w
  exact ⟨w', Prod.ext (by simp [hw']) (by simp)⟩⟩

instance sndSL_normal (r s : ℕ) : (sndSL (K := K) r s).Normal := ⟨fun x hx g => by
  obtain ⟨w, rfl⟩ := hx
  obtain ⟨w', hw'⟩ := toGL_conj_mem g.2 w
  exact ⟨w', Prod.ext (by simp) (by simp [hw'])⟩⟩

theorem isQuasisimple_fstSL [Finite K] (h4 : 4 ≤ Nat.card K) {r : ℕ} (hr : 2 ≤ r) (s : ℕ) :
    IsQuasisimple (fstSL (K := K) r s) := by
  have hinj : Function.Injective ((MonoidHom.inl (GL (Fin r) K) (GL (Fin s) K)).comp
      (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin r) K →* GL (Fin r) K)) :=
    fun _ _ h => Matrix.SpecialLinearGroup.toGL_injective (congrArg Prod.fst h)
  exact LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj)
    (RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hr h4)

theorem isQuasisimple_sndSL [Finite K] (h4 : 4 ≤ Nat.card K) (r : ℕ) {s : ℕ} (hs : 2 ≤ s) :
    IsQuasisimple (sndSL (K := K) r s) := by
  have hinj : Function.Injective ((MonoidHom.inr (GL (Fin r) K) (GL (Fin s) K)).comp
      (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin s) K →* GL (Fin s) K)) :=
    fun _ _ h => Matrix.SpecialLinearGroup.toGL_injective (congrArg Prod.snd h)
  exact LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj)
    (RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hs h4)

theorem eq_one_of_scalar_eq_one {r : ℕ} (hr : 1 ≤ r) {u : Kˣ}
    (h : GeneralLinearGroup.scalar (Fin r) u = 1) : u = 1 := by
  have h1 := congrArg (fun g : GL (Fin r) K => (g : Matrix (Fin r) (Fin r) K) ⟨0, hr⟩ ⟨0, hr⟩) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, Units.val_one,
    one_apply_eq] at h1
  exact Units.ext h1

section split

variable (A : GL (Fin n) K) (b : Kˣ) (htwo : (2 : K) ≠ 0)
  (hsq : A ^ 2 = GeneralLinearGroup.scalar (Fin n) (b ^ 2))

@[expose] def splitCoord : (Fin n → K) ≃ₗ[K]
    (Fin (positiveMatrixDimension A b.val) → K) × (Fin (negativeMatrixDimension A b.val) → K) :=
  (squareScalar_eigenspaceEquiv (splitMatrixOperator A) b.val b.ne_zero htwo
    (splitMatrixOperator_square A b hsq)).symm.trans
    ((positiveMatrixBasis A b.val).equivFun.prodCongr (negativeMatrixBasis A b.val).equivFun)

theorem splitCoord_mulVec (B : centralizer ({A} : Set (GL (Fin n) K))) (v : Fin n → K) :
    splitCoord A b htwo hsq ((B : GL (Fin n) K).val *ᵥ v) =
      ((matrixCentralizerSplitEquiv A b htwo hsq B).1.val *ᵥ (splitCoord A b htwo hsq v).1,
        (matrixCentralizerSplitEquiv A b htwo hsq B).2.val *ᵥ
          (splitCoord A b htwo hsq v).2) := by
  set E := squareScalar_eigenspaceEquiv (splitMatrixOperator A) b.val b.ne_zero htwo
    (splitMatrixOperator_square A b hsq) with hE
  obtain ⟨y, rfl⟩ := E.surjective v
  set B' := matrixCentralizerEquiv A B
  have hB : (B : GL (Fin n) K).val *ᵥ E y =
      E (operatorCentralizerRestriction (splitMatrixOperator A) b.val B' y.1,
        operatorCentralizerRestriction (splitMatrixOperator A) (-b.val) B' y.2) := by
    change (B : GL (Fin n) K).val *ᵥ ((y.1 : Fin n → K) + y.2) =
      (B : GL (Fin n) K).val *ᵥ (y.1 : Fin n → K) + (B : GL (Fin n) K).val *ᵥ (y.2 : Fin n → K)
    rw [Matrix.mulVec_add]
  rw [hB]
  simp only [splitCoord, LinearEquiv.trans_apply, ← hE, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, matrixCentralizerSplitEquiv_apply,
    basisAutomorphismMatrixEquiv_mulVec]
  rfl

theorem splitCoord_A (v : Fin n → K) :
    splitCoord A b htwo hsq (A.val *ᵥ v) =
      (b.val • (splitCoord A b htwo hsq v).1, (-b.val) • (splitCoord A b htwo hsq v).2) := by
  set E := squareScalar_eigenspaceEquiv (splitMatrixOperator A) b.val b.ne_zero htwo
    (splitMatrixOperator_square A b hsq) with hE
  obtain ⟨y, rfl⟩ := E.surjective v
  have h1 : A.val *ᵥ (y.1 : Fin n → K) = b.val • (y.1 : Fin n → K) :=
    Module.End.mem_eigenspace_iff.mp y.1.2
  have h2 : A.val *ᵥ (y.2 : Fin n → K) = (-b.val) • (y.2 : Fin n → K) :=
    Module.End.mem_eigenspace_iff.mp y.2.2
  have hA : A.val *ᵥ E y = E (b.val • y.1, (-b.val) • y.2) := by
    change A.val *ᵥ ((y.1 : Fin n → K) + y.2) =
      b.val • (y.1 : Fin n → K) + (-b.val) • (y.2 : Fin n → K)
    rw [Matrix.mulVec_add, h1, h2]
  rw [hA]
  simp only [splitCoord, LinearEquiv.trans_apply, ← hE, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, map_smul]

theorem splitCoord_pull {m : SpecialLinearGroup (Fin n) K}
    (hm : Matrix.SpecialLinearGroup.toGL m ∈ centralizer ({A} : Set (GL (Fin n) K)))
    {x₁ : GL (Fin (positiveMatrixDimension A b.val)) K}
    {x₂ : GL (Fin (negativeMatrixDimension A b.val)) K}
    (hx : matrixCentralizerSplitEquiv A b htwo hsq ⟨_, hm⟩ = (x₁, x₂)) (v : Fin n → K) :
    splitCoord A b htwo hsq ((m : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (x₁.val *ᵥ (splitCoord A b htwo hsq v).1, x₂.val *ᵥ (splitCoord A b htwo hsq v).2) := by
  have := splitCoord_mulVec A b htwo hsq ⟨_, hm⟩ v
  rw [hx] at this
  exact this

end split

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
