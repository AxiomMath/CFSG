module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import CFSG.LieType.AlgebraicGroups.GLCoordPoints
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Cocharacter
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.Algebra.Bialgebra.Quotient

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open Matrix Module TauCeti WithConv
open scoped TensorProduct CFSG.ConvolutionPoints

variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentMonomialUnit : Multiplicative ℤ →* (MonoidAlgebra k (Multiplicative ℤ))ˣ :=
  (MonoidAlgebra.of k (Multiplicative ℤ)).toHomUnits

theorem laurentMonomialUnit_val (n : ℤ) :
    (laurentMonomialUnit (k := k) (Multiplicative.ofAdd n) : MonoidAlgebra k (Multiplicative ℤ)) =
      MonoidAlgebra.single (Multiplicative.ofAdd n) 1 := by
  rw [laurentMonomialUnit, MonoidHom.coe_toHomUnits, MonoidAlgebra.of_apply]

def diagonalCocharacterAlgHom (wt : ι → ℤ) :
    GLCoord k ι →ₐ[k] MonoidAlgebra k (Multiplicative ℤ) := by
  let d : ι → (MonoidAlgebra k (Multiplicative ℤ))ˣ :=
    fun i => laurentMonomialUnit (Multiplicative.ofAdd (wt i))
  let t := (∏ i, d i)⁻¹
  exact GLCoord.lift k ι (Matrix.diagonal fun i => (d i : MonoidAlgebra k (Multiplicative ℤ))) t
    (by
      rw [Matrix.det_diagonal]
      have hd : (∏ i, (d i : MonoidAlgebra k (Multiplicative ℤ))) =
          (∏ i, d i : (MonoidAlgebra k (Multiplicative ℤ))ˣ) := by simp
      rw [hd]
      exact congrArg Units.val (mul_inv_cancel (∏ i, d i)))

theorem diagonalCocharacterAlgHom_entry (wt : ι → ℤ) (i j : ι) :
    diagonalCocharacterAlgHom (k := k) wt (glEntry k ι i j) =
      if i = j then MonoidAlgebra.single (Multiplicative.ofAdd (wt i)) 1 else 0 := by
  rw [diagonalCocharacterAlgHom, GLCoord.lift_glEntry, Matrix.diagonal_apply]
  split_ifs
  · exact laurentMonomialUnit_val _
  · rfl

theorem diagonalCocharacterAlgHom_detInv (wt : ι → ℤ) :
    diagonalCocharacterAlgHom (k := k) wt (glDetInv k ι) =
      (laurentMonomialUnit (k := k) (Multiplicative.ofAdd (-∑ i, wt i)) :
        MonoidAlgebra k (Multiplicative ℤ)) := by
  rw [diagonalCocharacterAlgHom, GLCoord.lift_glDetInv]
  have h : (∏ i, laurentMonomialUnit (k := k) (Multiplicative.ofAdd (wt i))) =
      laurentMonomialUnit (Multiplicative.ofAdd (∑ i, wt i)) := by
    rw [← map_prod, ← ofAdd_sum]
  rw [h, ← map_inv]
  rfl

theorem diagonalCocharacterAlgHom_point (wt : ι → ℤ)
    (p : WithConv (MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k)) :
    (pointMatrix (p.ofConv.comp (diagonalCocharacterAlgHom (k := k) wt))) =
      Matrix.diagonal (fun i => (DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) : k) ^ wt i) := by
  ext i j
  rw [pointMatrix, Matrix.of_apply, AlgHom.comp_apply, diagonalCocharacterAlgHom_entry,
    Matrix.diagonal_apply]
  split_ifs
  · have h : (laurentMonomialUnit (k := k) (Multiplicative.ofAdd (wt i)) :
        MonoidAlgebra k (Multiplicative ℤ)) =
        ((laurentMonomialUnit (k := k) (Multiplicative.ofAdd 1)) ^ wt i :
          (MonoidAlgebra k (Multiplicative ℤ))ˣ) := by
      rw [← map_zpow, ← ofAdd_zsmul]
      simp
    rw [← laurentMonomialUnit_val, h]
    have hmap := Units.map (p.ofConv : _ →* k) |>.map_zpow
      (laurentMonomialUnit (k := k) (Multiplicative.ofAdd 1)) (wt i)
    have h' := congrArg Units.val hmap
    simpa only [Units.coe_map, Units.val_zpow_eq_zpow_val, laurentMonomialUnit_val,
      TauCeti.DiagonalizableGroup.pointsMulEquiv_apply, DiagonalizableGroup.charOfPoint_apply_coe, MonoidHom.coe_coe] using h'
  · simp

@[irreducible] def diagonalCocharacterBialgHom [IsAlgClosed k] (wt : ι → ℤ) :
    GLCoord k ι →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) :=
  bialgHomOfPointMulTo (diagonalCocharacterAlgHom wt) (by
    intro p q
    have hmon (n : ℤ) : (p * q).ofConv (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) =
        p.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) *
          q.ofConv (MonoidAlgebra.single (Multiplicative.ofAdd n) 1) := by
      rw [AlgHom.convMul_apply]
      have hm : Coalgebra.comul (R := k) (MonoidAlgebra.single (Multiplicative.ofAdd n) (1 : k)) =
          MonoidAlgebra.single (Multiplicative.ofAdd n) 1 ⊗ₜ[k]
            MonoidAlgebra.single (Multiplicative.ofAdd n) 1 := by simp
      rw [hm, Algebra.TensorProduct.lift_tmul]
    apply WithConv.ext
    apply GLCoord.algHom_ext
    · intro i j
      rw [AlgHom.comp_apply, diagonalCocharacterAlgHom_entry, convMul_glEntry]
      simp only [AlgHom.comp_apply, diagonalCocharacterAlgHom_entry]
      rw [Finset.sum_eq_single i]
      · by_cases hij : i = j
        · subst j
          simp only [ite_true]
          exact hmon (wt i)
        · simp [hij]
      · intro l _ hli
        simp [Ne.symm hli]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · rw [AlgHom.comp_apply, diagonalCocharacterAlgHom_detInv, convMul_glDetInv]
      simp only [AlgHom.comp_apply, diagonalCocharacterAlgHom_detInv,
        laurentMonomialUnit_val]
      exact hmon (-∑ i, wt i))

theorem diagonalCocharacterBialgHom_toAlgHom [IsAlgClosed k] (wt : ι → ℤ) :
    (diagonalCocharacterBialgHom (k := k) wt).toAlgHom = diagonalCocharacterAlgHom wt := by
  unfold diagonalCocharacterBialgHom
  exact coe_bialgHomOfPointMulTo _ _

end CFSG.LieType.AlgebraicGroups
