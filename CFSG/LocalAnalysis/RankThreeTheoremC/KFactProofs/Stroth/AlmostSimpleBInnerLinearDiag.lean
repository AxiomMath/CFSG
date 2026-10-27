module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerDiagAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerDiagLeaf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.CALinearPrimary
open Polynomial

section Matrix

variable {k : Type} [Field k] [CharP k 2]

theorem three_cast_ne_zero_of_charP_two : ((3 : ℕ) : k) ≠ 0 := by
  intro h0
  rw [CharP.cast_eq_zero_iff k 2] at h0
  omega

theorem toLin'_scalar_fin {n : ℕ} (c : k) :
    Matrix.toLin' (Matrix.scalar (Fin n) c) = c • (1 : Module.End k (Fin n → k)) := by
  ext v i
  simp [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem squarefree_minpoly_slGL_of_pow_scalar {n : ℕ} {a : Matrix.SpecialLinearGroup (Fin n) k}
    {c : kˣ} (hac : ((a : Matrix (Fin n) (Fin n) k)) ^ 3 = Matrix.scalar (Fin n) (c : k)) :
    Squarefree (minpoly k ((slGL n k a : LinearMap.GeneralLinearGroup k (Fin n → k)) :
      Module.End k (Fin n → k))) := by
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ 3 - C (c : k))
    (Polynomial.separable_X_pow_sub_C (c : k) three_cast_ne_zero_of_charP_two
      c.ne_zero).squarefree ?_
  rw [map_sub, map_pow, aeval_X, aeval_C, coe_slGL, ← Matrix.toLin'_pow, hac, toLin'_scalar_fin]
  simp [Algebra.algebraMap_eq_smul_one]

end Matrix

section Main

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem pClosureOdd_projectiveSL_three : PClosureOdd 3 (projectiveSL 3 k) := by
  intro d hd1 hdp
  obtain ⟨a, rfl⟩ := proj_surjective 3 k d
  have hZ3 : ∀ z ∈ scalars 3 k, z ^ 3 = 1 := by
    rintro z ⟨c, hc, hz⟩
    have hc3 : ((c : k)) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    have hz' : (z : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) (c : k) := hz
    have h1 : (z : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
      rw [hz', ← map_pow, hc3, map_one]
    exact Subtype.ext (by simpa using h1)
  have ha3 : a ^ 3 ∈ scalars 3 k := by
    rw [← proj_eq_one_iff, map_pow]
    exact hdp
  obtain ⟨c, -, hac⟩ := ha3
  have hac' : (a : Matrix (Fin 3) (Fin 3) k) ^ 3 = Matrix.scalar (Fin 3) (c : k) := by
    have h1 : ((a ^ 3 : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        Matrix.scalar (Fin 3) (c : k) := hac
    simpa using h1
  have hsq := squarefree_minpoly_slGL_of_pow_scalar hac'
  have hC := oddPCoreInClosure_centralizer_slGL_of_squarefree Nat.prime_three (by norm_num) hsq
  refine oddPCoreInClosure_centralizer_mk_of_dichotomy Nat.prime_three (by norm_num) (scalars 3 k)
    (scalars_le_center 3 k) hZ3 a hC ?_
  rintro ⟨g, hg, hga⟩ t ht2 hta
  have h1 : proj 3 k g * proj 3 k a = proj 3 k a * proj 3 k g :=
    Subgroup.mem_centralizer_singleton_iff.1 hg
  have h2 : proj 3 k (g * a) = proj 3 k (a * g) := by rw [map_mul, map_mul]; exact h1
  obtain ⟨c', hc', hw⟩ := proj_eq_proj_iff.1 h2
  have hag : a * g = g * a * ((g * a)⁻¹ * (a * g)) := (mul_inv_cancel_left (g * a) (a * g)).symm
  have hag' : ((slGL 3 k (a * g) : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
      Module.End k (Fin 3 → k)) =
      (c' : k) • ((slGL 3 k (g * a) : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
        Module.End k (Fin 3 → k)) := by
    rw [hag, map_mul, Units.val_mul, coe_slGL ((g * a)⁻¹ * (a * g)), hw, toLin'_scalar_fin]
    simp
  have hc'1 : (c' : k) ≠ 1 := by
    intro h
    apply hga
    rw [h, one_smul] at hag'
    exact slGL_injective (Units.ext hag'.symm)
  have hζ3 : ((c' : k)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, ← Units.val_pow_eq_pow_val, hc', Units.val_one, inv_one]
  have hζ1 : (c' : k)⁻¹ ≠ 1 := fun h => hc'1 (inv_eq_one.1 h)
  have hc'0 : (c' : k) ≠ 0 := c'.ne_zero
  have hg3 : ((slGL 3 k g : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
        Module.End k (Fin 3 → k)) *
      ((slGL 3 k a : LinearMap.GeneralLinearGroup k (Fin 3 → k)) : Module.End k (Fin 3 → k)) =
      (c' : k)⁻¹ • (((slGL 3 k a : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
        Module.End k (Fin 3 → k)) *
        ((slGL 3 k g : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
          Module.End k (Fin 3 → k))) := by
    simp only [map_mul, Units.val_mul] at hag'
    rw [hag', smul_smul, inv_mul_cancel₀ hc'0, one_smul]
  have ht3 : ((slGL 3 k t : LinearMap.GeneralLinearGroup k (Fin 3 → k)) :
        Module.End k (Fin 3 → k)) *
      ((slGL 3 k a : LinearMap.GeneralLinearGroup k (Fin 3 → k)) : Module.End k (Fin 3 → k)) =
      ((slGL 3 k a : LinearMap.GeneralLinearGroup k (Fin 3 → k)) : Module.End k (Fin 3 → k)) *
        ((slGL 3 k t : LinearMap.GeneralLinearGroup k (Fin 3 → k)) : Module.End k (Fin 3 → k)) := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, hta]
  have ht23 : (slGL 3 k t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hW : Module.finrank k (Fin 3 → k) = 3 := by simp
  exact slGL_injective
    ((eq_one_of_sq_eq_one_of_commute_of_conj_smul hW hζ3 hζ1 hg3 ht3 ht23).trans (map_one _).symm)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
