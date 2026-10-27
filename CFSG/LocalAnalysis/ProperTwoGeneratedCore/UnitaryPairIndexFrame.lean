module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryNumeratorIndex
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsModelAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.HighRankPair CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open scoped LinearAlgebra.Projectivization

instance scalarCenter_normal {K : Type} [Field K] (J : HermitianForm 3 K) :
    (scalarCenter J).Normal :=
  ⟨fun n hn g => by
    have h := Subgroup.mem_center_iff.mp (scalarCenter_le_center J hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩

@[expose] def coverPSUEquiv {K : Type} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.specialSubgroup ⧸ scalarCenter J ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (QuotientGroup.quotientMulEquivOfEq (scalarCenter_eq_ker J hJ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (psuMk J) psuMk_surjective)

theorem coverPSUEquiv_apply {K : Type} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (x : J.specialSubgroup ⧸ scalarCenter J) :
    coverPSUEquiv J hJ x = coverToPSU J (scalarCenter J) hJ le_rfl x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

universe u

theorem exists_cover_point_of_model {G : Type u} [Group G] {H : Subgroup G} {z u : G}
    (huα : rightCosetMk H 1 ∈ elementFixedSet H u)
    (hodd : CFSG.oddCore (localInvolutionPointHull z u) = ⊥)
    {K : Type} [Field K] (A : HermitianForm 3 K)
    (hA : A.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (ρ : ProjectiveSpecialUnitaryMatrixGroup A →* Equiv.Perm (unitaryIsotropicPoints A))
    (hρ : ∀ g p, ((ρ g p : unitaryIsotropicPoints A) : ℙ K (Fin 3 → K)) =
      (g : Matrix.ProjGenLinGroup (Fin 3) K) • (p : ℙ K (Fin 3 → K)))
    (E : localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u) ≃*
      ProjectiveSpecialUnitaryMatrixGroup A)
    (ψ : elementFixedSet H u ≃ unitaryIsotropicPoints A)
    (hψα : ∀ δ : elementFixedSet H u, (δ : pointRightCosetSpace H) = rightCosetMk H 1 →
      ψ δ = unitaryOuterIsotropicPoint A hA 0 (by decide))
    (hψ : letI := hullFixedSetAction H z u
      ∀ (l : localInvolutionPointHull z u) (δ : elementFixedSet H u),
        ψ (l • δ) = ρ (E (QuotientGroup.mk' _ l)) (ψ δ)) :
    ∃ θ : A.specialSubgroup ⧸ scalarCenter A ≃* localInvolutionPointHull z u,
      ∀ x, ((θ x : localInvolutionPointHull z u) : G) ∈ H ↔
        coverToPGL A (scalarCenter A) hA le_rfl x • unitaryCoordinatePoint (K := K) 0 =
          unitaryCoordinatePoint 0 := by
  let := hullFixedSetAction H z u
  let eL : localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u) ≃*
      localInvolutionPointHull z u :=
    (QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot
  have heL : ∀ y, QuotientGroup.mk' (CFSG.oddCore (localInvolutionPointHull z u)) (eL y) = y := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rfl
  refine ⟨((coverPSUEquiv A hA).trans E.symm).trans eL, fun x => ?_⟩
  obtain ⟨l, hl⟩ : ∃ l, l = eL (E.symm (coverPSUEquiv A hA x)) := ⟨_, rfl⟩
  change ((eL (E.symm (coverPSUEquiv A hA x)) : localInvolutionPointHull z u) : G) ∈ H ↔ _
  rw [← hl]
  have hEl : E (QuotientGroup.mk' _ l) = coverPSUEquiv A hA x := by
    rw [hl, heL, MulEquiv.apply_symm_apply]
  have hδα : ψ ⟨rightCosetMk H 1, huα⟩ = unitaryOuterIsotropicPoint A hA 0 (by decide) :=
    hψα _ rfl
  have hmemH : (l : G) ∈ H ↔ l • (⟨rightCosetMk H 1, huα⟩ : elementFixedSet H u) =
      ⟨rightCosetMk H 1, huα⟩ := by
    have h1 : (l : G) ∈ H ↔
        pointRightCosetMul H (rightCosetMk H 1) (l : G) = rightCosetMk H 1 := by
      have := mem_rightCosetStabilizer_iff_pointRightCosetMul H (rightCosetMk H 1) (l : G)
      rwa [rightCosetStabilizer_base] at this
    rw [h1, ← pointRightCosetMul_inv_eq_self_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [hmemH, ← ψ.injective.eq_iff, hψ, hEl, hδα]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [hρ, coverPSUEquiv_apply] at h'
    exact h'
  · intro h
    apply Subtype.ext
    rw [hρ, coverPSUEquiv_apply]
    exact h

theorem exists_flip_cover_of_cover {G : Type} [Group G] {H L : Subgroup G} {t : G}
    (htL : t ∈ L) (htH : t ∉ H)
    {k : Type} [Field k] [Finite k] [CharP k 2] (J : HermitianForm 3 k)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {f : ℕ} (hf : 2 ≤ f)
    (hk : Nat.card k = (2 ^ f) ^ 2) (hfix : Nat.card {x : k // J.conj x = x} = 2 ^ f)
    (θ₀ : J.specialSubgroup ⧸ scalarCenter J ≃* L)
    (hθ₀ : ∀ x, ((θ₀ x : L) : G) ∈ H ↔
      coverToPGL J (scalarCenter J) hJ le_rfl x • unitaryCoordinatePoint (K := k) 0 =
        unitaryCoordinatePoint 0) :
    ∃ θ : J.specialSubgroup ⧸ scalarCenter J ≃* L,
      (∀ x, ((θ x : L) : G) ∈ H ↔
        coverToPGL J (scalarCenter J) hJ le_rfl x • unitaryCoordinatePoint (K := k) 0 =
          unitaryCoordinatePoint 0) ∧
      (∀ x, ((θ x : L) : G) = t →
        coverToPGL J (scalarCenter J) hJ le_rfl x • unitaryCoordinatePoint (K := k) 0 =
          unitaryCoordinatePoint 2) := by
  set C := scalarCenter J
  have hC : C ≤ scalarCenter J := le_rfl
  set τ₀ := θ₀.symm ⟨t, htL⟩
  have hP : coverToPGL J C hJ hC τ₀ • unitaryCoordinatePoint (K := k) 0 ≠
      unitaryCoordinatePoint 0 := by
    intro hfix0
    have hmemH := (hθ₀ τ₀).mpr hfix0
    rw [MulEquiv.apply_symm_apply] at hmemH
    exact htH hmemH
  set w : J.specialSubgroup ⧸ C := QuotientGroup.mk' C (hermitianWeylSU J hJ)
  have hw : coverToPGL J C hJ hC w • unitaryCoordinatePoint (K := k) 0 =
      unitaryCoordinatePoint 2 :=
    UnitaryModel.hermitianWeylPSU_smul_zero J hJ
  have hw0 : coverToPGL J C hJ hC w • unitaryCoordinatePoint (K := k) 0 ≠
      unitaryCoordinatePoint 0 := by
    rw [hw]
    exact UnitaryModel.unitaryCoordinatePoint_two_ne_zero
  obtain ⟨z₀, hz₀, -⟩ := heisL_regular hf hk hfix hJ hC hP hw0
  set c := heisL J C hJ z₀
  have hc0 : coverToPGL J C hJ hC c • unitaryCoordinatePoint (K := k) 0 =
      unitaryCoordinatePoint 0 := heisL_smul_zero hJ hC z₀
  let θ : J.specialSubgroup ⧸ C ≃* L := (MulAut.conj c⁻¹).trans θ₀
  have hmem : ∀ x, ((θ x : L) : G) ∈ H ↔
      coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 = unitaryCoordinatePoint 0 := by
    intro x
    change ((θ₀ (c⁻¹ * x * c⁻¹⁻¹) : L) : G) ∈ H ↔ _
    rw [hθ₀, inv_inv, map_mul, map_mul, mul_smul, mul_smul, hc0, map_inv, inv_smul_eq_iff, hc0]
  have hflip : ∀ x, ((θ x : L) : G) = t →
      coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := k) 0 = unitaryCoordinatePoint 2 := by
    intro x hx
    have hx' : θ₀ (c⁻¹ * x * c⁻¹⁻¹) = θ₀ τ₀ := by
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hx
    have hxτ : c⁻¹ * x * c⁻¹⁻¹ = τ₀ := θ₀.injective hx'
    have hxeq : x = c * τ₀ * c⁻¹ := by
      rw [← hxτ]
      group
    rw [hxeq, map_mul, map_mul, mul_smul, mul_smul, map_inv, inv_smul_eq_iff.mpr hc0.symm, hz₀,
      hw]
  exact ⟨θ, hmem, hflip⟩

end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame
