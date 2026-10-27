module
public import CFSG.LieType.AlgebraicGroups.DiagonalCocharacter
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.AlgebraicGroups.RootWordRegular

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Matrix Module TauCeti WithConv
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped TensorProduct CFSG.ConvolutionPoints
variable {k : Type} [Field k] [IsAlgClosed k] {τ : Tag}

theorem diagonalCocharacterBialgHom_rootDiagPoint
    (lam : Fin τ.rank → ℤ)
    (p : WithConv (MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k)) :
    TauCeti.AlgHom.mapDomain (A := k)
      (diagonalCocharacterBialgHom (fun b : Label τ => ∑ i, lam i * labelWt τ b i)) p =
      modGLPoint τ k (rootDiagUnit τ (fun i =>
        DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^ lam i)) := by
  apply glPointEquiv.symm.injective
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [glPointEquiv_symm_apply]
  rw [TauCeti.AlgHom.mapDomain_apply]
  have h := diagonalCocharacterAlgHom_point (fun b : Label τ => ∑ i, lam i * labelWt τ b i) p
  have hij := congrArg (fun m : Matrix (Label τ) (Label τ) k => m i j) h
  simp only [pointMatrix, Matrix.of_apply, AlgHom.comp_apply] at hij
  have hp : (diagonalCocharacterBialgHom (k := k) (fun b : Label τ => ∑ i, lam i * labelWt τ b i)).toAlgHom =
      diagonalCocharacterAlgHom (fun b : Label τ => ∑ i, lam i * labelWt τ b i) := by
    exact diagonalCocharacterBialgHom_toAlgHom _
  have hp' := AlgHom.congr_fun hp (glEntry k (Label τ) i j)
  simp only [AlgHom.comp_apply]
  rw [hp', hij]
  rw [glPointEquiv_symm_apply, modGLPoint_apply_glEntry]
  change _ = rootDiag _ (Finsupp.single j 1) i
  rw [rootDiag_single, Finsupp.smul_apply, smul_eq_mul]
  have hchar : rootChar (fun l => DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^ lam l)
      (labelWt τ j) = DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^
        ∑ l, lam l * labelWt τ j l := by
    simp only [rootChar, ← _root_.zpow_mul]
    exact Finset.prod_zpow_eq_zpow_sum _ _ _
  rw [hchar, Units.val_zpow_eq_zpow_val, Matrix.diagonal_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

end CFSG.LieType.AlgebraicGroups
