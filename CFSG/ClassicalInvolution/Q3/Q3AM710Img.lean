module

public import CFSG.ClassicalInvolution.Asc77.AscE184Sub
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM710

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem member_eq_of_map_eq (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {X : Subgroup G}
    {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hLX : L ≤ X) (hL'X : L' ≤ X) {u u' : G}
    (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u') {W₀ : Subgroup G}
    (hW₀ : IsPGroup 2 W₀) (huW : u ∈ W₀) (hu'W : u' ∈ W₀)
    (h : (L.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) =
      (L'.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))) : L = L' := by
  set N : Subgroup ↥X := classicalInvolutionOddCore ↥X with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card _
  have hz := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN (L.subgroupOf X))
    (isUniqueInvolution_subgroupOf hu hLX)
  have hz' := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN (L'.subgroupOf X))
    (isUniqueInvolution_subgroupOf hu' hL'X)
  rw [h] at hz
  have hmk : QuotientGroup.mk' N (⟨u, hLX hu.mem⟩ : ↥X) = QuotientGroup.mk' N ⟨u', hL'X hu'.mem⟩ :=
    hz.eq hz'
  have hw : (⟨u, hLX hu.mem⟩ : ↥X)⁻¹ * ⟨u', hL'X hu'.mem⟩ ∈ N := by
    have : QuotientGroup.mk' N ((⟨u, hLX hu.mem⟩ : ↥X)⁻¹ * ⟨u', hL'X hu'.mem⟩) = 1 := by
      rw [map_mul, map_inv, hmk, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have h2 : IsPGroup 2 (Subgroup.zpowers ((⟨u, hLX hu.mem⟩ : ↥X)⁻¹ * ⟨u', hL'X hu'.mem⟩)) := by
    rw [← isPGroup_zpowers_coe_iff]
    refine hW₀.to_le (Subgroup.zpowers_le.mpr ?_)
    exact W₀.mul_mem (W₀.inv_mem huW) hu'W
  have h1 := eq_one_of_isPGroup_of_mem_odd hN hw h2
  have huu : u = u' := by
    have h3 : u⁻¹ * u' = 1 := congrArg Subtype.val h1
    exact inv_mul_eq_one.mp h3
  have hL'twin : L' ∈ twinSet Ω L := ⟨hL', u, hu, huu ▸ hu'⟩
  exact (hnt L hL L' hL'twin).symm

end CFSG.ClassicalInvolution.Q3.Q3AM710
