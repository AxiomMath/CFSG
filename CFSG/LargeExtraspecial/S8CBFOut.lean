module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk onCenterQuotient_eq_one_imp)

variable {X : Type*} [Group X]

noncomputable def conjOuterCenterQuot (U : Subgroup X) [U.Normal] :
    X →* Outer (↥U ⧸ center ↥U) :=
  (QuotientGroup.mk' (inner (↥U ⧸ center ↥U))).comp
    ((centerQuotientHom ↥U).comp (MulAut.conjNormal (H := U)))

theorem centerQuotientHom_conjNormal_coe (U : Subgroup X) [U.Normal] (u : U) :
    centerQuotientHom ↥U (MulAut.conjNormal (u : X)) =
      MulAut.conj (QuotientGroup.mk' (center ↥U) u) := by
  ext q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center ↥U) q
  change onCenterQuotient _ _ = _
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem mem_sup_centralizer_of_conjOuterCenterQuot_eq_one (U : Subgroup X) [U.Normal]
    (hU : ⁅U, U⁆ = U) {x : X} (hx : conjOuterCenterQuot U x = 1) :
    x ∈ U ⊔ centralizer (U : Set X) := by
  have : Group.IsPerfect U := Subgroup.isPerfect_iff.mpr hU
  have hmem : centerQuotientHom ↥U (MulAut.conjNormal (H := U) x) ∈
      inner (↥U ⧸ center ↥U) :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨s, hs⟩ := hmem
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center ↥U) s
  have h1 : onCenterQuotient (MulAut.conjNormal (H := U) ((u : X)⁻¹ * x)) = 1 := by
    change centerQuotientHom ↥U (MulAut.conjNormal (H := U) ((u : X)⁻¹ * x)) = 1
    rw [map_mul, map_mul, map_inv, map_inv, centerQuotientHom_conjNormal_coe, ← hs,
      inv_mul_cancel]
  have h2 := onCenterQuotient_eq_one_imp _ h1
  have hc : (u : X)⁻¹ * x ∈ centralizer (U : Set X) := by
    rw [mem_centralizer_iff]
    intro v hv
    have h3 := congrArg (fun φ : MulAut U => ((φ ⟨v, hv⟩ : U) : X)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    calc v * ((u : X)⁻¹ * x)
        = ((u : X)⁻¹ * x) * v * ((u : X)⁻¹ * x)⁻¹ * ((u : X)⁻¹ * x) := by rw [h3]
      _ = ((u : X)⁻¹ * x) * v := by group
  have hx' : x = (u : X) * ((u : X)⁻¹ * x) := by group
  rw [hx']
  exact mul_mem (mem_sup_left u.2) (mem_sup_right hc)

theorem exists_derivedSeries_le_sup_centralizer (U : Subgroup X) [U.Normal] (hU : ⁅U, U⁆ = U)
    (hS : Group.IsSolvable (Outer (↥U ⧸ center ↥U))) :
    ∃ k, derivedSeries X k ≤ U ⊔ centralizer (U : Set X) := by
  obtain ⟨k, hk⟩ := hS.solvable
  refine ⟨k, fun x hx => mem_sup_centralizer_of_conjOuterCenterQuot_eq_one U hU ?_⟩
  have h := map_derivedSeries_le_derivedSeries (conjOuterCenterQuot U) k ⟨x, hx, rfl⟩
  rw [hk] at h
  exact h

end CFSG.LargeExtraspecial.S8
