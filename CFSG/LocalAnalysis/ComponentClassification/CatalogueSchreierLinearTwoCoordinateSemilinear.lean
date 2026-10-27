module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter
open scoped Pointwise

universe u

@[expose] def finiteFieldPrime (K : Type u) [Field K] [Finite K] : ℕ :=
  ringChar K

theorem finiteField_primePower (K : Type u) [Field K] [Finite K] :
    ∃ f : ℕ, Nat.Prime (ringChar K) ∧ Nat.card K = ringChar K ^ f := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, hp, by simpa [Nat.card_eq_fintype_card] using hcard⟩

theorem finiteField_characteristic_prime (K : Type u) [Field K] [Finite K] :
    Nat.Prime (ringChar K) := (finiteField_primePower K).choose_spec.1

@[expose] def finiteFieldExponent (K : Type u) [Field K] [Finite K] : ℕ :=
  (finiteField_primePower K).choose

theorem finiteField_card_eq (K : Type u) [Field K] [Finite K] :
    Nat.card K = ringChar K ^ finiteFieldExponent K :=
  (finiteField_primePower K).choose_spec.2

@[expose] def coordinateAutAction (K : Type u) [Field K] [Finite K] :
    MulAut (PSL2 K) →* Equiv.Perm (Omega K) := by
  let : Fact (Nat.Prime (ringChar K)) := ⟨finiteField_characteristic_prime K⟩
  exact (coordinateEquiv K).symm.permCongrHom.toMonoidHom.comp
    (psl2MulAutProjectiveLine K (finiteField_card_eq K))

theorem coordinateAutAction_point (K : Type u) [Field K] [Finite K]
    (alpha : MulAut (PSL2 K)) (x : Omega K) :
    letI : Fact (Nat.Prime (ringChar K)) := ⟨finiteField_characteristic_prime K⟩
    coordinateEquiv K (coordinateAutAction K alpha x) =
      psl2MulAutProjectiveLine K (finiteField_card_eq K) alpha (coordinateEquiv K x) := by
  exact (coordinateEquiv K).apply_symm_apply _

@[expose] def coordinateSemilinearAction (K : Type u) [Field K] [Finite K] :
    PGammaL2 K →* Equiv.Perm (Omega K) :=
  (coordinateAutAction K).comp (semilinearAction K)

theorem coordinateSemilinearAction_inl (K : Type u) [Field K] [Finite K] (g : PGL2 K) :
    coordinateSemilinearAction K (SemidirectProduct.inl g) = coordinatePGLAction K g := by
  let : Fact (Nat.Prime (ringChar K)) := ⟨finiteField_characteristic_prime K⟩
  apply Equiv.ext
  intro x
  apply (coordinateEquiv K).injective
  change coordinateEquiv K (coordinateAutAction K (semilinearAction K (SemidirectProduct.inl g)) x) = _
  rw [semilinearAction_inl, coordinateAutAction_point, coordinatePGLAction_point,
    pglAction_projectiveLine]

theorem coordinateSemilinearAction_inr (K : Type u) [Field K] [Finite K]
    (sigma : K ≃+* K) :
    coordinateSemilinearAction K (SemidirectProduct.inr sigma) = fieldExtension K sigma := by
  let : Fact (Nat.Prime (ringChar K)) := ⟨finiteField_characteristic_prime K⟩
  apply Equiv.ext
  intro x
  apply (coordinateEquiv K).injective
  change coordinateEquiv K (coordinateAutAction K (semilinearAction K (SemidirectProduct.inr sigma)) x) = _
  rw [semilinearAction_inr, coordinateAutAction_point]
  cases x with
  | none =>
    simp only [coordinateEquiv_none, fieldExtension_none]
    exact fieldAut_projectiveLine_infinity K (finiteField_card_eq K) sigma
  | some x =>
    simp only [coordinateEquiv_some, fieldExtension_some]
    exact fieldAut_projectiveLine_affine K (finiteField_card_eq K) sigma x

theorem coordinateAutAction_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (coordinateAutAction K) := by
  let : Fact (Nat.Prime (ringChar K)) := ⟨finiteField_characteristic_prime K⟩
  exact (coordinateEquiv K).symm.permCongrHom.injective.comp
    (psl2MulAutProjectiveLine_injective K (finiteField_card_eq K))

theorem coordinateSemilinearAction_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (coordinateSemilinearAction K) :=
  (coordinateAutAction_injective K).comp (semilinearAction_injective K)

theorem coordinateD_le_E (K : Type u) [Field K] : coordinateD K ≤ coordinateE K := by
  intro g hg
  exact Subgroup.subset_closure (Or.inl hg)

theorem coordinateE_le_range (K : Type u) [Field K] [Finite K] :
    coordinateE K ≤ (coordinateSemilinearAction K).range := by
  apply (Subgroup.closure_le (coordinateSemilinearAction K).range).mpr
  intro g hg
  rcases hg with hg | ⟨sigma, rfl⟩
  · rw [← coordinatePGLAction_range_eq_D] at hg
    obtain ⟨h, rfl⟩ := hg
    exact ⟨SemidirectProduct.inl h, coordinateSemilinearAction_inl K h⟩
  · exact ⟨SemidirectProduct.inr sigma, coordinateSemilinearAction_inr K sigma⟩

theorem coordinateSemilinearAction_range_eq_E (K : Type u) [Field K] [Finite K] :
    (coordinateSemilinearAction K).range = coordinateE K := by
  apply le_antisymm _ (coordinateE_le_range K)
  rintro g ⟨h, rfl⟩
  rw [← SemidirectProduct.inl_left_mul_inr_right h, map_mul,
    coordinateSemilinearAction_inl, coordinateSemilinearAction_inr]
  apply (coordinateE K).mul_mem
  · apply coordinateD_le_E K
    rw [← coordinatePGLAction_range_eq_D]
    exact ⟨h.left, rfl⟩
  · exact Subgroup.subset_closure (Or.inr ⟨h.right, rfl⟩)

@[expose] def semilinearEquivCoordinateE (K : Type u) [Field K] [Finite K] :
    PGammaL2 K ≃* coordinateE K :=
  (MulEquiv.ofBijective (coordinateSemilinearAction K).rangeRestrict
    ⟨fun _ _ h => coordinateSemilinearAction_injective K (congrArg Subtype.val h),
      (coordinateSemilinearAction K).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr (coordinateSemilinearAction_range_eq_E K))

theorem semilinearEquivCoordinateE_coe (K : Type u) [Field K] [Finite K] (g : PGammaL2 K) :
    ((semilinearEquivCoordinateE K g : coordinateE K) : Equiv.Perm (Omega K)) =
      coordinateSemilinearAction K g := rfl

theorem semilinearPGLRange_map (K : Type u) [Field K] [Finite K] :
    (pGammaL2PGLRange K).map (semilinearEquivCoordinateE K).toMonoidHom =
      (coordinateD K).subgroupOf (coordinateE K) := by
  apply Subgroup.map_injective (coordinateE K).subtype_injective
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
  rw [show ((coordinateE K).subtype.comp (semilinearEquivCoordinateE K).toMonoidHom) =
    coordinateSemilinearAction K by rfl]
  rw [pGammaL2PGLRange, ← MonoidHom.range_comp]
  have hcomp : (coordinateSemilinearAction K).comp SemidirectProduct.inl =
      coordinatePGLAction K := by
    apply MonoidHom.ext
    intro g
    exact coordinateSemilinearAction_inl K g
  rw [hcomp, coordinatePGLAction_range_eq_D, inf_eq_left.mpr (coordinateD_le_E K)]

theorem semilinearPSLRange_map (K : Type u) [Field K] [Finite K] :
    (pGammaL2PSLRange K).map (semilinearEquivCoordinateE K).toMonoidHom =
      (coordinateG K).subgroupOf (coordinateE K) := by
  apply Subgroup.map_injective (coordinateE K).subtype_injective
  rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
  rw [show ((coordinateE K).subtype.comp (semilinearEquivCoordinateE K).toMonoidHom) =
    coordinateSemilinearAction K by rfl]
  rw [pGammaL2PSLRange, ← MonoidHom.range_comp]
  have hcomp : (coordinateSemilinearAction K).comp
      ((SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
        Matrix.ProjectiveSpecialLinearGroup.toPGL) = coordinatePSLAction K := by
    ext g
    simp only [MonoidHom.comp_apply, coordinateSemilinearAction_inl, coordinatePGLAction_toPGL]
  rw [hcomp, coordinatePSLAction_range_eq_G,
    inf_eq_left.mpr ((coordinateG_le_D K).trans (coordinateD_le_E K))]

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
