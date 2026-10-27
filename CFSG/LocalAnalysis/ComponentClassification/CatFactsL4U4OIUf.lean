module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUe
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EULift

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank LinearFlag
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {k : Type} [Field k] (δ : kˣ) (h2 : (2 : k) ≠ 0)

abbrev Umat : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k)) →* GL (Fin 4) k :=
  rowOHom δ (hermitianCoordinates (δ : k) h2)

theorem Umat_mulVec (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k)))
    (x : Fin 4 → k) :
    (Umat δ h2 g : Matrix (Fin 4) (Fin 4) k) *ᵥ x =
      (hermitianCoordinates (δ : k) h2).symm
        (rowOAction δ g (hermitianCoordinates (δ : k) h2 x)) :=
  linearConjGL_mulVec _ _ x

theorem qf_Umat (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) (x : Fin 4 → k) :
    OIL.qf (δ : k) ((Umat δ h2 g : Matrix (Fin 4) (Fin 4) k) *ᵥ x) = OIL.qf (δ : k) x := by
  have hX : ∀ X : hermitianSubmodule (δ : k),
      hermitianForm (δ : k) X = OIL.qf (δ : k) ((hermitianCoordinates (δ : k) h2).symm X) :=
    fun X => by
      rw [← OIL.hermitianForm_coord (δ : k) h2, LinearEquiv.apply_symm_apply]
  have hiso := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (specialRho (δ : k) h2 g).2
  rw [Umat_mulVec, ← hX, ← OIL.hermitianForm_coord (δ : k) h2 x]
  exact hiso _

theorem dotProduct_gramQ (x y : Fin 4 → k) :
    x ⬝ᵥ (gramQ (δ : k) *ᵥ y) = OIL.qf (δ : k) (x + y) - OIL.qf (δ : k) x - OIL.qf (δ : k) y := by
  simp only [gramQ, OIL.qf, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.add_apply]
  simp
  ring

theorem Umat_gram (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) :
    (Umat δ h2 g : Matrix (Fin 4) (Fin 4) k)ᵀ * gramQ (δ : k) * (Umat δ h2 g) =
      gramQ (δ : k) := by
  apply OIL.eq_of_dotProduct_mulVec
  intro x y
  rw [Matrix.mul_assoc, OIL.dotProduct_transpose_mul, ← Matrix.mulVec_mulVec, dotProduct_gramQ,
    dotProduct_gramQ, ← Matrix.mulVec_add, qf_Umat, qf_Umat, qf_Umat]

theorem det_Umat [Finite k] (hδ : ¬ IsSquare (δ : k)) (hE : 2 < Nat.card k)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) :
    (Umat δ h2 g : Matrix (Fin 4) (Fin 4) k).det = 1 := by
  have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
  have : Finite (extension (δ : k)) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (δ : k) 0).symm
  have hcE : 3 < Nat.card (extension (δ : k)) := by
    rw [extension_card]
    nlinarith
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 (extension (δ : k)) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  let χ := (GeneralLinearGroup.det).comp (Umat δ h2)
  have hY : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k)))),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))))⁆ = ⊤ := by
    rw [← commutator_def, hperf.commutator_eq_top]
  have h1 := GSThmB.Catalog7L4EU.le_ker_of_perfect χ hY (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at h1
  have h3 := congrArg Units.val h1
  simpa [χ] using h3

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
