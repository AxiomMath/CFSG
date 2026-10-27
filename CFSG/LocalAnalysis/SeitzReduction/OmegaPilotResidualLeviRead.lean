module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviTrace

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Group

variable {X : Type*} [Group X]

theorem isSimpleGroup_quotient_of_eq_or_top {N : Subgroup X} [N.Normal]
    (hq : ∀ M : Subgroup X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    (hnc : ∃ a b : X ⧸ N, a * b ≠ b * a) : IsSimpleGroup (X ⧸ N) := by
  have hnt : Nontrivial (X ⧸ N) := by
    obtain ⟨a, b, hab⟩ := hnc
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hab (Subsingleton.elim _ _)
  refine ⟨fun H hH => ?_⟩
  have hc : (H.comap (QuotientGroup.mk' N)).Normal := hH.comap _
  have hle : N ≤ H.comap (QuotientGroup.mk' N) := fun x hx => by
    rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem H
  rcases hq _ hc hle with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ H.comap (QuotientGroup.mk' N) := hy
    rw [h] at hx
    rw [mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr hx
  · right
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ H.comap (QuotientGroup.mk' N) := by rw [h]; exact mem_top x
    exact hx

theorem le_of_isPGroup_of_eq_or_top [Finite X] {N : Subgroup X} [N.Normal]
    (hq : ∀ M : Subgroup X, M.Normal → N ≤ M → M = N ∨ M = ⊤)
    (hab : N = ⊤ ∨ ∃ a b : X ⧸ N, a * b ≠ b * a) (M : Subgroup X) (hM : M.Normal)
    (hMp : IsPGroup 2 M) : M ≤ N := by
  rcases hab with rfl | hnc
  · exact le_top
  · have : IsSimpleGroup (X ⧸ N) := isSimpleGroup_quotient_of_eq_or_top hq hnc
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact le_of_isPGroup_of_simple hnc hMp

end Group

section Subspace

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem mapsTo_inv_of_mapsTo {C : Type*} [Group C] [Finite C] (β : MulAut C) {X : Subgroup C}
    (h : ∀ x ∈ X, β x ∈ X) : ∀ x ∈ X, β⁻¹ x ∈ X := by
  intro x hx
  have heq := subgroup_map_eq_of_mapsTo β h
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change β⁻¹ (β y) ∈ X
  rwa [MulAut.inv_apply_self]

theorem spLeviSection_of_trace_restrict (hQ : ∃ v, Q v ≠ 0)
    (fp : MulAut (matrixProjectiveDerived Q) →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q, fp (matrixProjectiveConjugationHom Q g) = g.val.right)
    (hsurj : ∀ β : MulAut (matrixProjectiveDerived Q),
      ∃ g, matrixProjectiveConjugationHom Q g = β)
    {X : Subgroup (matrixProjectiveDerived Q)} (U : Submodule K (Fin d → K))
    (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U)
    (hTU : ∀ g : similarityPairs Q, (∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) →
      ∀ u ∈ U, coordinateSemilinearMap g.val u ∈ U)
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K U
      (((projLift hQ (x : matrixProjectiveDerived Q) : (Fin d → K) →ₗ[K] (Fin d → K))).restrict
        (hXU x x.2))) :
    SpLeviSection fp X ρ.ker := by
  refine spLeviSection_of_hom fp hr ρ hρ fun β hβ _ x => ?_
  obtain ⟨g, rfl⟩ := hsurj β
  have hβ' := mapsTo_inv_of_mapsTo _ hβ
  have hTU' : ∀ u ∈ U, (coordinateSemilinearMap g.val).symm u ∈ U := by
    intro u hu
    have h := hTU g⁻¹ (by rw [map_inv]; exact hβ') u hu
    rwa [Subgroup.coe_inv, coordinateSemilinearMap_inv] at h
  rw [htr, htr, hfp]
  exact trace_restrict_projLift_kappa hQ g U (hTU g hβ) hTU' x (hXU x x.2) _

theorem mapsTo_of_fixedSpace_eq (hQ : ∃ v, Q v ≠ 0) {X : Subgroup (matrixProjectiveDerived Q)}
    (N₁ N₂ N₃ : Subgroup ↥X)
    (hN : ∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → IsPGroup 2 M → M ≤ N)
    (hR : IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃)) (hRn : (N₁ ⊓ N₂ ⊓ N₃).Normal)
    (U : Submodule K (Fin d → K))
    (hU : ∀ v, v ∈ U ↔
      ∀ r ∈ N₁ ⊓ N₂ ⊓ N₃, projLift hQ (r : matrixProjectiveDerived Q) v = v)
    (g : similarityPairs Q) (hgX : ∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) :
    ∀ u ∈ U, coordinateSemilinearMap g.val u ∈ U := by
  intro u hu
  rw [hU] at hu ⊢
  exact mapsTo_fixedSpace_of_core hQ g hgX N₁ N₂ N₃ hN hR hRn hu

end Subspace

section Assembly

open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {C : Type*} [Group C] [Finite C]

@[expose] def SpLeviSections (fp : MulAut C →* (K ≃+* K)) (X : Subgroup C) : Prop :=
  ∃ (N₁ N₂ N₃ : Subgroup ↥X) (_ : N₁.Normal) (_ : N₂.Normal) (_ : N₃.Normal),
    IsPGroup 2 ↥(N₁ ⊓ N₂ ⊓ N₃) ∧
    (∀ N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → N ≤ M → M = N ∨ M = ⊤) ∧
    (∀ (N : Subgroup ↥X) [N.Normal], N ∈ ({N₁, N₂, N₃} : Set (Subgroup ↥X)) →
      SpLeviSection fp X N) ∧
    ∃ r : ℕ, 1 ≤ r ∧ Nonempty (↥X ⧸ N₁ ≃* StatedProj (StatedSp r K)) ∧
      IsEmpty (↥X ⧸ N₂ ≃* StatedProj (StatedSp r K)) ∧
      IsEmpty (↥X ⧸ N₃ ≃* StatedProj (StatedSp r K))

theorem spLeviData_of_spLeviSections (fp : MulAut C →* (K ≃+* K)) (hq4 : 4 ≤ Nat.card K)
    {X : Subgroup C} (h : SpLeviSections fp X) : SpLeviData fp X := by
  obtain ⟨N₁, N₂, N₃, h₁, h₂, h₃, h123, hq, hs, r, hr, ⟨e⟩, he₂, he₃⟩ := h
  exact spLeviData_of_isEmpty_mulEquiv fp hq4 N₁ N₂ N₃ h123 hq hs hr e he₂ he₃

end Assembly

end CFSG.SeitzReduction.OmegaPilot
