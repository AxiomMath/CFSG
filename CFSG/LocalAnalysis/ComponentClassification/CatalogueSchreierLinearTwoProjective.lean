module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinates
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.CatalogueSchreierLinearTwoNormalized

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter Matrix Projectivization
open scoped Pointwise

universe u

@[expose] def scalarCenter (K : Type u) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {A | ∃ s : Kˣ, s ^ 2 = 1 ∧
    (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (s : K)}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro A B ⟨s, hs, hA⟩ ⟨t, ht, hB⟩
    refine ⟨s * t, by simp [mul_pow, hs, ht], ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mul, hA, hB, Units.val_mul,
      ← map_mul (Matrix.scalar (Fin 2))]
  inv_mem' := by
    rintro A ⟨s, hs, hA⟩
    refine ⟨s⁻¹, by simp [inv_pow, hs], ?_⟩
    have hsInv : (s : K) = (s : K)⁻¹ := by
      have hs2 : (s : K) * (s : K) = 1 := by simpa [pow_two] using congrArg Units.val hs
      exact eq_inv_of_mul_eq_one_left hs2
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA, Matrix.scalar_apply]
    all_goals exact hsInv

theorem scalarCenter_eq_center (K : Type u) [Field K] :
    scalarCenter K = Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext A
  constructor
  · rintro ⟨s, hs, hA⟩
    apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
    refine ⟨(s : K), ?_, hA.symm⟩
    simpa using congrArg Units.val hs
  · intro hA
    obtain ⟨s, hs, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have hs' : s ^ 2 = 1 := by simpa using hs
    have hs0 : s ≠ 0 := by
      intro h
      simp [h] at hs'
    refine ⟨Units.mk0 s hs0, ?_, hscalar.symm⟩
    apply Units.ext
    exact hs'

noncomputable instance scalarCenterNormal (K : Type u) [Field K] :
    (scalarCenter K).Normal := by rw [scalarCenter_eq_center]; infer_instance

abbrev ProjectiveQuotient (K : Type u) [Field K] :=
  Matrix.SpecialLinearGroup (Fin 2) K ⧸ scalarCenter K

@[expose] def projectiveQuotientEquivPSL (K : Type u) [Field K] :
    ProjectiveQuotient K ≃* PSL2 K :=
  QuotientGroup.quotientMulEquivOfEq (scalarCenter_eq_center K)

theorem weyl_smul_zero (K : Type u) [Field K] :
    psl2SymplecticElement K • psl2ProjectiveZero K = psl2ProjectiveInfinity K := by
  rw [psl2SymplecticElement_eq_mk]
  change sl2SymplecticMatrix K • psl2ProjectiveZero K = psl2ProjectiveInfinity K
  rw [psl2ProjectiveZero, psl2ProjectiveInfinity, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨-1, ?_⟩
  change (-1 : K) • (![1, 0] : Fin 2 → K) =
    (sl2SymplecticMatrix K).val *ᵥ ![0, 1]
  ext i
  fin_cases i <;> simp [sl2SymplecticMatrix, Matrix.mulVec]

theorem weyl_smul_affine (K : Type u) [Field K] (x : K) (hx : x ≠ 0) :
    psl2SymplecticElement K • psl2AffinePoint K x = psl2AffinePoint K (-x⁻¹) := by
  rw [psl2SymplecticElement_eq_mk]
  change sl2SymplecticMatrix K • psl2AffinePoint K x = psl2AffinePoint K (-x⁻¹)
  rw [psl2AffinePoint, psl2AffinePoint, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff']
  refine ⟨x, ?_⟩
  change x • (![-x⁻¹, 1] : Fin 2 → K) = (sl2SymplecticMatrix K).val *ᵥ ![x, 1]
  ext i
  fin_cases i <;> simp [sl2SymplecticMatrix, Matrix.mulVec, hx]

theorem coordinatePSLAction_upper (K : Type u) [Field K] (b : K) :
    coordinatePSLAction K (psl2QuotientMap K (sl2UpperUnipotent b)) = translation K b := by
  apply Equiv.ext
  intro x
  apply (coordinateEquiv K).injective
  rw [coordinatePSLAction_point]
  cases x with
  | none =>
    simp only [coordinateEquiv_none, translation_none]
    apply MulAction.mem_stabilizer_iff.mp
    exact psl2UpperUnipotent_le_borel
      ((mem_psl2UpperUnipotentSubgroup_iff _).mpr ⟨b, rfl⟩)
  | some x => simp

theorem coordinatePSLAction_weyl (K : Type u) [Field K] :
    coordinatePSLAction K (psl2SymplecticElement K) = inversion K := by
  apply Equiv.ext
  intro x
  apply (coordinateEquiv K).injective
  rw [coordinatePSLAction_point]
  cases x with
  | none => simpa using weyl_smul_infinity K
  | some x =>
    by_cases hx : x = 0
    · subst x
      simpa using weyl_smul_zero K
    · rw [coordinateEquiv_some, inversion_nonzero K x hx, coordinateEquiv_some]
      exact weyl_smul_affine K x hx

theorem coordinateG_le_range (K : Type u) [Field K] :
    coordinateG K ≤ (coordinatePSLAction K).range := by
  apply (Subgroup.closure_le (coordinatePSLAction K).range).mpr
  intro x hx
  rcases hx with ⟨b, rfl⟩ | hx
  · exact ⟨psl2QuotientMap K (sl2UpperUnipotent b), coordinatePSLAction_upper K b⟩
  · have h : x = inversion K := Set.mem_singleton_iff.mp hx
    rw [h]
    exact ⟨psl2SymplecticElement K, coordinatePSLAction_weyl K⟩

private theorem upper_eq_transvection (K : Type u) [Field K] (b : K) :
    sl2UpperUnipotent b = Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2UpperUnipotent, Matrix.SpecialLinearGroup.transvection_coe]

private theorem lower_eq_weyl_upper (K : Type u) [Field K] (b : K) :
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) b =
      sl2SymplecticMatrix K * sl2UpperUnipotent (-b) * (sl2SymplecticMatrix K)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  apply Subtype.ext
  change (1 : Matrix (Fin 2) (Fin 2) K) + Matrix.single 1 0 b =
    ((sl2SymplecticMatrix K).val * (sl2UpperUnipotent (-b)).val) *
      !![(sl2SymplecticMatrix K).val 1 1, -(sl2SymplecticMatrix K).val 0 1;
        -(sl2SymplecticMatrix K).val 1 0, (sl2SymplecticMatrix K).val 0 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2UpperUnipotent, sl2SymplecticMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem coordinatePSLAction_range_eq_G (K : Type u) [Field K] :
    (coordinatePSLAction K).range = coordinateG K := by
  apply le_antisymm _ (coordinateG_le_range K)
  rintro x ⟨g, rfl⟩
  obtain ⟨A, rfl⟩ := psl2QuotientMap_surjective g
  apply Matrix.SL2.transvection_induction
    (fun A => coordinatePSLAction K (psl2QuotientMap K A) ∈ coordinateG K)
  · intro i j hij b
    have hupper (c : K) : coordinatePSLAction K (psl2QuotientMap K (sl2UpperUnipotent c)) ∈
        coordinateG K := by
      rw [coordinatePSLAction_upper]
      exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
    have hweyl : coordinatePSLAction K (psl2QuotientMap K (sl2SymplecticMatrix K)) ∈
        coordinateG K := by
      change coordinatePSLAction K (psl2SymplecticElement K) ∈ _
      rw [coordinatePSLAction_weyl]
      exact Subgroup.subset_closure (Or.inr rfl)
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · rw [← upper_eq_transvection]
      exact hupper b
    · rw [lower_eq_weyl_upper, map_mul, map_mul, map_inv,
        map_mul, map_mul, map_inv]
      exact (coordinateG K).mul_mem ((coordinateG K).mul_mem hweyl (hupper (-b)))
        ((coordinateG K).inv_mem hweyl)
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul, map_mul]
    exact (coordinateG K).mul_mem hA hB

@[expose] def pslEquivCoordinateG (K : Type u) [Field K] : PSL2 K ≃* coordinateG K :=
  (MulEquiv.ofBijective (coordinatePSLAction K).rangeRestrict
    ⟨fun _ _ h => coordinatePSLAction_injective K (congrArg Subtype.val h),
      (coordinatePSLAction K).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (coordinatePSLAction_range_eq_G K))

@[expose] def projectiveQuotientEquivCoordinateG (K : Type u) [Field K] :
    ProjectiveQuotient K ≃* coordinateG K :=
  (projectiveQuotientEquivPSL K).trans (pslEquivCoordinateG K)

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
