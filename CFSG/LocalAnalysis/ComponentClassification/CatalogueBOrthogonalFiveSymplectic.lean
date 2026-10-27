module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveSimilitudes

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem symplecticGram_eq_neg_JFin : symplecticGram K = -TauCeti.JFin 2 K := by
  rw [TauCeti.JFin_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symplecticGram]

theorem symplectic_matrix_iff_native (A : GL (Fin 4) K) :
    A.valᵀ * symplecticGram K * A.val = symplecticGram K ↔
      A ∈ TauCeti.GLSymplecticFin 2 K := by
  rw [TauCeti.GLSymplecticFin.mem_iff', symplecticGram_eq_neg_JFin,
    Matrix.mul_neg, Matrix.neg_mul, neg_inj]

@[expose] def symplecticKernelEquivFin :
    (symplecticMultiplier (K := K)).ker ≃* TauCeti.GLSymplecticFin 2 K where
  toFun A := ⟨A.val.val, symplectic_matrix_iff_native A.val.val |>.mp
    (symplecticMultiplier_kernel_iff A.val |>.mp A.property)⟩
  invFun A :=
    let hA := (symplectic_matrix_iff_native A.val).mpr A.property
    let g : symplecticSimilitudes K := ⟨A.val, 1, by simpa only [Units.val_one, one_smul] using hA⟩
    ⟨g, (symplecticMultiplier_kernel_iff g).mpr hA⟩
  left_inv A := Subtype.ext (Subtype.ext rfl)
  right_inv A := Subtype.ext rfl
  map_mul' A B := Subtype.ext rfl

theorem symplecticKernelEquivFin_val (A : (symplecticMultiplier (K := K)).ker) :
    (symplecticKernelEquivFin A).val = A.val.val := rfl

@[expose] def symplecticKernelEquiv :
    (symplecticMultiplier (K := K)).ker ≃* TauCeti.GLSymplectic (Fin 2) K :=
  symplecticKernelEquivFin.trans (TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 K)

variable [Finite K]

instance symplecticKernelFinite : Finite (symplecticMultiplier (K := K)).ker :=
  Finite.of_injective (fun A : (symplecticMultiplier (K := K)).ker => A.val.val.val)
    (Units.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective))

theorem symplecticKernel_quasisimple (hodd : Odd (Nat.card K)) :
    CFSG.IsQuasisimple (symplecticMultiplier (K := K)).ker :=
  CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv symplecticKernelEquiv
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (CatalogueBAlternatingIsometry.symplectic_quasisimple K 2 (by decide) hodd
          (Or.inl (by decide)))))

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
