module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidSp
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviSection
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviRead

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

section Kappa

omit [CharP K 2] in
theorem exists_kappa_fp_eq (fp : matrixProjectiveImage Q →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q,
      fp ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right)
    {β : MulAut (matrixProjectiveDerived Q)} (hβE : β ∈ matrixProjectiveImage Q) :
    ∃ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = β ∧
      fp ⟨β, hβE⟩ = g.val.right := by
  obtain ⟨g, rfl⟩ := hβE
  exact ⟨g, rfl, hfp g⟩

theorem trace_projLift_kappa (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    (x : matrixProjectiveDerived Q) :
    LinearMap.trace K _ (projLift hQ (matrixProjectiveConjugationHom Q g x) :
        (Fin d → K) →ₗ[K] (Fin d → K)) =
      g.val.right (LinearMap.trace K _ (projLift hQ x : (Fin d → K) →ₗ[K] (Fin d → K))) :=
  trace_eq_of_semilinear_comm g.val.right (coordinateSemilinearMap g.val)
    (coordinateSemilinearMap_smul g.val) _ _ (projLift_kappa_apply hQ g x)

omit [CharP K 2] in
theorem symm_mem_of_mapsTo_kappa [Finite K] {X : Subgroup (matrixProjectiveDerived Q)}
    (U : Submodule K (Fin d → K))
    (hTU : ∀ g : similarityPairs Q, (∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) →
      ∀ u ∈ U, coordinateSemilinearMap g.val u ∈ U)
    (g : similarityPairs Q) (hgX : ∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) :
    ∀ u ∈ U, (coordinateSemilinearMap g.val).symm u ∈ U := by
  have hβ' := mapsTo_inv_of_mapsTo _ hgX
  intro u hu
  have h := hTU g⁻¹ (by rw [map_inv]; exact hβ') u hu
  rwa [Subgroup.coe_inv, coordinateSemilinearMap_inv] at h

theorem mem_of_mapsTo_fixed_kappa (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    (U : Submodule K (Fin d → K)) (hTU' : ∀ u ∈ U, (coordinateSemilinearMap g.val).symm u ∈ U)
    {x : matrixProjectiveDerived Q} (hx : ∀ u ∈ U, projLift hQ x u = u) :
    ∀ u ∈ U, projLift hQ (matrixProjectiveConjugationHom Q g x) u = u := by
  intro u hu
  have e := projLift_kappa_apply hQ g x ((coordinateSemilinearMap g.val).symm u)
  rw [AddEquiv.apply_symm_apply] at e
  rw [e, hx _ (hTU' u hu), AddEquiv.apply_symm_apply]

end Kappa

section Readings

variable [Finite K]

theorem spLeviSectionE_of_trace_restrict (hQ : ∃ v, Q v ≠ 0)
    (fp : matrixProjectiveImage Q →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q,
      fp ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right)
    {X : Subgroup (matrixProjectiveDerived Q)} (U : Submodule K (Fin d → K))
    (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U)
    (hTU : ∀ g : similarityPairs Q, (∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) →
      ∀ u ∈ U, coordinateSemilinearMap g.val u ∈ U)
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K U
      (((projLift hQ (x : matrixProjectiveDerived Q) : (Fin d → K) →ₗ[K] (Fin d → K))).restrict
        (hXU x x.2))) :
    SpLeviSectionE (matrixProjectiveImage Q) fp X ρ.ker := by
  refine spLeviSectionE_of_hom _ fp hr ρ hρ fun β hβE hβ _ x => ?_
  obtain ⟨g, rfl, hg⟩ := exists_kappa_fp_eq fp hfp hβE
  rw [htr, htr, hg]
  exact trace_restrict_projLift_kappa hQ g U (hTU g hβ) (symm_mem_of_mapsTo_kappa U hTU g hβ) x
    (hXU x x.2) _

theorem spLeviSectionE_of_trace_restrict_add (hQ : ∃ v, Q v ≠ 0)
    (fp : matrixProjectiveImage Q →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q,
      fp ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right)
    {X : Subgroup (matrixProjectiveDerived Q)} (U : Submodule K (Fin d → K))
    (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U)
    (hTU : ∀ g : similarityPairs Q, (∀ x ∈ X, matrixProjectiveConjugationHom Q g x ∈ X) →
      ∀ u ∈ U, coordinateSemilinearMap g.val u ∈ U)
    (c : K) (hc : ∀ σ : K ≃+* K, σ c = c)
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) + c = LinearMap.trace K U
      (((projLift hQ (x : matrixProjectiveDerived Q) : (Fin d → K) →ₗ[K] (Fin d → K))).restrict
        (hXU x x.2))) :
    SpLeviSectionE (matrixProjectiveImage Q) fp X ρ.ker := by
  refine spLeviSectionE_of_hom _ fp hr ρ hρ fun β hβE hβ _ x => ?_
  obtain ⟨g, rfl, hg⟩ := exists_kappa_fp_eq fp hfp hβE
  have h1 := htr (restrictAutOfMapsTo (matrixProjectiveConjugationHom Q g) X hβ x)
  have h2 := htr x
  have h3 := trace_restrict_projLift_kappa hQ g U (hTU g hβ)
    (symm_mem_of_mapsTo_kappa U hTU g hβ) x (hXU x x.2)
    (hXU _ (restrictAutOfMapsTo (matrixProjectiveConjugationHom Q g) X hβ x).2)
  rw [hg]
  have h4 : spMatTrace (ρ (restrictAutOfMapsTo (matrixProjectiveConjugationHom Q g) X hβ x)) + c =
      g.val.right (spMatTrace (ρ x) + c) := by
    rw [h1, h2]
    exact h3
  rw [map_add, hc] at h4
  exact add_right_cancel h4

theorem spLeviSectionE_of_trace_eq (hQ : ∃ v, Q v ≠ 0)
    (fp : matrixProjectiveImage Q →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q,
      fp ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right)
    {X : Subgroup (matrixProjectiveDerived Q)} {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K)
    (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (projLift hQ (x : matrixProjectiveDerived Q) : (Fin d → K) →ₗ[K] (Fin d → K))) :
    SpLeviSectionE (matrixProjectiveImage Q) fp X ρ.ker :=
  spLeviSectionE_of_hom _ fp hr ρ hρ fun β hβE hβ _ x => by
    obtain ⟨g, rfl, hg⟩ := exists_kappa_fp_eq fp hfp hβE
    rw [htr, htr, coe_restrictAutOfMapsTo, hg]
    exact trace_projLift_kappa hQ g x

theorem spLeviSectionE_of_kerQuot (hQ : ∃ v, Q v ≠ 0)
    (fp : matrixProjectiveImage Q →* (K ≃+* K))
    (hfp : ∀ g : similarityPairs Q,
      fp ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right)
    {X : Subgroup (matrixProjectiveDerived Q)} {r : ℕ} (hr : 1 ≤ r)
    (N : (Fin d → K) →ₗ[K] (Fin d → K)) (hNN : ∀ v, N (N v) = 0)
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v))
    (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (kerQuotMap N (projLift hQ (x : matrixProjectiveDerived Q) :
        (Fin d → K) →ₗ[K] (Fin d → K)) (hXN x x.2))) :
    SpLeviSectionE (matrixProjectiveImage Q) fp X ρ.ker :=
  spLeviSectionE_of_trace_eq hQ fp hfp hr ρ hρ fun x => by
    rw [htr, ← trace_eq_trace_kerQuotMap N _ hNN]

end Readings

end CFSG.SeitzReduction.OmegaPilot
