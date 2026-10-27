module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerUnitaryFamily
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerDiagAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerDiagLeaf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary
open Polynomial

section Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem squarefree_minpoly_toLin_of_pow_three_scalar {n : ℕ} {a : GL (Fin n) K} {c : Kˣ}
    (hap : a ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    Squarefree (minpoly K ((Matrix.GeneralLinearGroup.toLin a :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))) := by
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    omega
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ 3 - C (c : K))
    (Polynomial.separable_X_pow_sub_C (c : K) hpK c.ne_zero).squarefree ?_
  have h1 : ((Matrix.GeneralLinearGroup.toLin a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) := rfl
  rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val,
    hap]
  ext v i
  by_cases hi : i = v <;> simp [hi]

end Matrix

section Main

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem pClosureOdd_unitaryPSU_three (hℓ : ℓ = 2) (h : UnitaryFieldData ℓ f K) :
    PClosureOdd 3 (unitaryPSU h 3) := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := hℓ ▸ h.charP
  intro d hd1 hdp
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective d
  have hZ3 : ∀ z ∈ unitaryScalars h 3, z ^ 3 = 1 := by
    intro z hz
    obtain ⟨c, -, hc, hzc⟩ := mem_unitaryScalars.1 hz
    apply Subtype.ext
    change ((z : GL (Fin 3) K)) ^ 3 = 1
    rw [hzc, ← map_pow, hc, map_one]
  have hx3 : x ^ 3 ∈ unitaryScalars h 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hdp
  obtain ⟨c, -, -, hxc⟩ := mem_unitaryScalars.1 hx3
  have hsq := squarefree_minpoly_toLin_of_pow_three_scalar (a := (x : GL (Fin 3) K)) (c := c)
    (by simpa using hxc)
  have hC := oddPCoreInClosure_centralizer_unitarySU_of_squarefree Nat.prime_three (by norm_num) hℓ
    h 3 x hsq
  refine oddPCoreInClosure_centralizer_mk_of_dichotomy Nat.prime_three (by norm_num)
    (unitaryScalars h 3) (unitaryScalars_le_center h 3) hZ3 x hC ?_
  rintro ⟨g, hg, hga⟩ t ht2 hta
  have h1 :
      (g : unitaryPSU h 3) * (x : unitaryPSU h 3) = (x : unitaryPSU h 3) * (g : unitaryPSU h 3) :=
    Subgroup.mem_centralizer_singleton_iff.1 hg
  have h2 : ((g * x : ↥(unitarySU ℓ f K 3)) : unitaryPSU h 3) =
      ((x * g : ↥(unitarySU ℓ f K 3)) : unitaryPSU h 3) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact h1
  have hw := QuotientGroup.eq.1 h2
  obtain ⟨c', -, hc', hwc⟩ := mem_unitaryScalars.1 hw
  have hxg : x * g = g * x * ((g * x)⁻¹ * (x * g)) := (mul_inv_cancel_left (g * x) (x * g)).symm
  let T : GL (Fin 3) K ≃* LinearMap.GeneralLinearGroup K (Fin 3 → K) :=
    Matrix.GeneralLinearGroup.toLin
  have hTc : ((T (Matrix.GeneralLinearGroup.scalar (Fin 3) c') :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K)) =
      (c' : K) • (1 : Module.End K (Fin 3 → K)) := by
    ext v i
    simp [T, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply, Matrix.scalar_apply,
      Matrix.mulVec_diagonal]
  have hxg' : ((T ((x * g : ↥(unitarySU ℓ f K 3)) : GL (Fin 3) K) :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K)) =
      (c' : K) • ((T ((g * x : ↥(unitarySU ℓ f K 3)) : GL (Fin 3) K) :
        LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K)) := by
    have e : ((x * g : ↥(unitarySU ℓ f K 3)) : GL (Fin 3) K) =
        ((g * x : ↥(unitarySU ℓ f K 3)) : GL (Fin 3) K) *
          Matrix.GeneralLinearGroup.scalar (Fin 3) c' := by
      rw [← hwc, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [e, map_mul, Units.val_mul, hTc]
    simp
  have hc'1 : (c' : K) ≠ 1 := by
    intro h1
    apply hga
    rw [h1, one_smul] at hxg'
    exact (Subtype.ext (T.injective (Units.ext hxg'))).symm
  have hc'0 : (c' : K) ≠ 0 := c'.ne_zero
  have hζ3 : ((c' : K)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, ← Units.val_pow_eq_pow_val, hc', Units.val_one, inv_one]
  have hζ1 : (c' : K)⁻¹ ≠ 1 := fun h1 => hc'1 (inv_eq_one.1 h1)
  have hxg'' : ((T (x : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) *
      ((T (g : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) =
      (c' : K) • (((T (g : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) *
        ((T (x : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
          Module.End K (Fin 3 → K))) := by
    simpa only [Subgroup.coe_mul, map_mul, Units.val_mul] using hxg'
  have hg3 : ((T (g : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) *
      ((T (x : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) =
      (c' : K)⁻¹ • (((T (x : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) *
        ((T (g : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
          Module.End K (Fin 3 → K))) := by
    rw [hxg'', smul_smul, inv_mul_cancel₀ hc'0, one_smul]
  have ht3 : ((T (t : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) *
      ((T (x : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) =
      ((T (x : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) *
        ((T (t : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
          Module.End K (Fin 3 → K)) := by
    have := congrArg (fun y : ↥(unitarySU ℓ f K 3) =>
      ((T (y : GL (Fin 3) K) : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K))) hta
    simpa only [Subgroup.coe_mul, map_mul, Units.val_mul] using this
  have ht23 : (T (t : GL (Fin 3) K)) ^ 2 = 1 := by
    rw [← map_pow]
    have : (t : GL (Fin 3) K) ^ 2 = 1 := by
      have := congrArg (fun y : ↥(unitarySU ℓ f K 3) => (y : GL (Fin 3) K)) ht2
      simpa using this
    rw [this, map_one]
  have hW : Module.finrank K (Fin 3 → K) = 3 := by simp
  have key := eq_one_of_sq_eq_one_of_commute_of_conj_smul hW hζ3 hζ1 hg3 ht3 ht23
  exact Subtype.ext (T.injective (key.trans (map_one T).symm))

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
