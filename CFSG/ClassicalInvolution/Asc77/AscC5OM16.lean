module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM15

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F] (μ : F)

@[expose] def kap (u : Fin 2 → QuadraticAlgebra F μ 0) : Fin 2 ⊕ Fin 2 → F :=
  Sum.elim ![(u 0).re, (u 0).im] ![(u 1).im, (u 1).re]

@[expose] def kapInv (x : Fin 2 ⊕ Fin 2 → F) : Fin 2 → QuadraticAlgebra F μ 0 :=
  ![⟨x (Sum.inl 0), x (Sum.inl 1)⟩, ⟨x (Sum.inr 1), x (Sum.inr 0)⟩]

theorem kap_kapInv (x : Fin 2 ⊕ Fin 2 → F) : kap μ (kapInv μ x) = x := by
  funext r
  rcases r with r | r <;> fin_cases r <;> rfl

theorem kapInv_kap (u : Fin 2 → QuadraticAlgebra F μ 0) : kapInv μ (kap μ u) = u := by
  funext i
  fin_cases i <;> rfl

@[expose] def phiM (A : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks
    !![(A 0 0).re, μ * (A 0 0).im; (A 0 0).im, (A 0 0).re]
    !![μ * (A 0 1).im, (A 0 1).re; (A 0 1).re, (A 0 1).im]
    !![(A 1 0).im, (A 1 0).re; (A 1 0).re, μ * (A 1 0).im]
    !![(A 1 1).re, (A 1 1).im; μ * (A 1 1).im, (A 1 1).re]

theorem phiM_mulVec_kap (A : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0))
    (u : Fin 2 → QuadraticAlgebra F μ 0) : phiM μ A *ᵥ kap μ u = kap μ (A *ᵥ u) := by
  funext r
  rcases r with r | r <;> fin_cases r <;>
    simp [phiM, kap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem phiM_ext {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ u : Fin 2 → QuadraticAlgebra F μ 0, X *ᵥ kap μ u = Y *ᵥ kap μ u) : X = Y :=
  matrix_ext_single fun j => by
    rw [← kap_kapInv μ (Pi.single j 1), h]

theorem phiM_mul (A B : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) :
    phiM μ (A * B) = phiM μ A * phiM μ B :=
  phiM_ext μ fun u => by
    rw [← Matrix.mulVec_mulVec, phiM_mulVec_kap, phiM_mulVec_kap, phiM_mulVec_kap,
      Matrix.mulVec_mulVec]

theorem phiM_one : phiM μ (1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) = 1 :=
  phiM_ext μ fun u => by rw [phiM_mulVec_kap, Matrix.one_mulVec, Matrix.one_mulVec]

theorem phiM_neg_one :
    phiM μ (-1 : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) = -1 :=
  phiM_ext μ fun u => by
    rw [phiM_mulVec_kap, Matrix.neg_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec]
    funext r
    rcases r with r | r <;> fin_cases r <;> simp [kap]

theorem kap_injective : Function.Injective (kap μ) := fun u v h => by
  rw [← kapInv_kap μ u, ← kapInv_kap μ v, h]

theorem phiM_injective : Function.Injective (phiM μ) := fun A B h => by
  refine Matrix.ext fun i j => ?_
  have h1 : kap μ (A *ᵥ Pi.single j 1) = kap μ (B *ᵥ Pi.single j 1) := by
    rw [← phiM_mulVec_kap, ← phiM_mulVec_kap, h]
  rw [← mulVec_single_one_apply A j i, ← mulVec_single_one_apply B j i, kap_injective μ h1]

theorem form_kap (u v : Fin 2 → QuadraticAlgebra F μ 0) :
    form (kap μ u) (kap μ v) = (u 0 * v 1 - u 1 * v 0).im := by
  rw [form_apply]
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, kap, sgn, par]
  ring

theorem transpose_gram_apply (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (a b : Fin 2 ⊕ Fin 2) :
    (Xᵀ * gram F 2 * X) a b = form (X *ᵥ Pi.single a 1) (X *ᵥ Pi.single b 1) := by
  rw [transpose_mul_gram_mul_apply, form_apply]
  simp only [mulVec_single_one_apply]

theorem form_single_single (a b : Fin 2 ⊕ Fin 2) :
    form (Pi.single a (1 : F)) (Pi.single b 1) = gram F 2 a b := by
  rw [form_single_right, gram_apply]
  by_cases h : b = par a
  · subst h
    simp
  · have h' : par b ≠ a := fun e => h (by rw [← e, par_par])
    simp [h, h']

theorem phiM_symplectic (g : SL(2, QuadraticAlgebra F μ 0)) :
    (phiM μ (g : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)))ᵀ * gram F 2 *
      phiM μ (g : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) = gram F 2 := by
  ext a b
  rw [transpose_gram_apply, ← kap_kapInv μ (Pi.single a 1), ← kap_kapInv μ (Pi.single b 1),
    phiM_mulVec_kap, phiM_mulVec_kap, form_kap, ← form_single_single, ← kap_kapInv μ
    (Pi.single a 1), ← kap_kapInv μ (Pi.single b 1), form_kap, kap_kapInv, kap_kapInv]
  have hdet : (g : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  congr 1
  set u := kapInv μ (Pi.single a 1)
  set v := kapInv μ (Pi.single b 1)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (u 0 * v 1 - u 1 * v 0) * hdet

theorem nPlus_mulVec_kap (u : Fin 2 → QuadraticAlgebra F μ 0) :
    nPlus μ *ᵥ kap μ u = kap μ ((QuadraticAlgebra.omega : QuadraticAlgebra F μ 0) • u) := by
  funext r
  rcases r with r | r <;> fin_cases r <;>
    simp [nPlus, kap, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem phiM_mul_nPlus (A : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) :
    phiM μ A * nPlus μ = nPlus μ * phiM μ A :=
  phiM_ext μ fun u => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nPlus_mulVec_kap, phiM_mulVec_kap,
      phiM_mulVec_kap, nPlus_mulVec_kap, Matrix.mulVec_smul]

@[expose] noncomputable def phiSL : SL(2, QuadraticAlgebra F μ 0) →* StatedSp 2 F where
  toFun g := ofSymplecticMat (phiM μ g) (phiM_symplectic μ g)
  map_one' := mat_injective (by rw [mat_ofSymplecticMat, map_one,
    Matrix.SpecialLinearGroup.coe_one, phiM_one])
  map_mul' g h := mat_injective (by rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat,
    mat_ofSymplecticMat, Matrix.SpecialLinearGroup.coe_mul, phiM_mul])

theorem mat_phiSL (g : SL(2, QuadraticAlgebra F μ 0)) :
    mat 2 F (phiSL μ g) = phiM μ (g : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F μ 0)) := rfl

end CFSG.ClassicalInvolution.Asc77.C5O.M
