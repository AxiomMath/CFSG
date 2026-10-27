module

public import CFSG.ClassicalInvolution.Q3.Q3T6DHexA

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Comp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isSolvable_member3 (hΩ : HypOmegaModU (.sl2 3 1) Ω) {M : Subgroup G} (hM : M ∈ Ω) :
    Group.IsSolvable ↥M := by
  obtain ⟨w, hw⟩ := hΩ.classical M hM
  have hq := Q3T6.isSolvable_oddCoreQuotient_of_isClassicalMember3
    (hw.toQ3 (by norm_num : (3 : ℕ) ^ 1 = 3))
  have ho : Group.IsSolvable ↥(classicalInvolutionOddCore ↥M) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card ↥M)
  exact Group.isSolvable_of_ker_le_range (classicalInvolutionOddCore ↥M).subtype
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥M))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_modOdd3 {M : Subgroup G} {z : G} (hMC : M ≤ Subgroup.centralizer ({z} : Set G))
    (hM : Group.IsSolvable ↥M) : Group.IsSolvable ↥(modOdd z M) := by
  let ψ : ↥M →* OddQuot z :=
    (oddQuotMk z).comp (Subgroup.inclusion hMC)
  have hrange : ψ.range = modOdd z M := by
    ext x
    rw [MonoidHom.mem_range, mem_modOdd_iff]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨⟨m, hMC m.2⟩, m.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have : Group.IsSolvable ↥ψ.range := Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  rwa [hrange] at this

theorem isSubnormal_modOdd3 {M : Subgroup G} {z : G}
    (hsub : IsSubnormal M (Subgroup.centralizer ({z} : Set G))) : (modOdd z M).IsSubnormal := by
  have h := isSubnormal_subgroupOf hsub (Subgroup.centralizer ({z} : Set G))
  rw [Subgroup.subgroupOf_self] at h
  have hsurj : Function.Surjective (oddQuotMk z) := QuotientGroup.mk'_surjective _
  have h2 := CFSG.ComponentClassification.Components.chain_map (oddQuotMk z) h
  rw [Subgroup.map_top_of_surjective _ hsurj] at h2
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib _).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).mpr h2)



namespace Std20Three

variable {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem commutator_component_modOdd3 (d : Std20Three K K' J S R R' W V z t)
    {M : Subgroup G} (hM : M ∈ CoreAssembly.conjClass K) (hzM : IsUniqueInvolution M z)
    {L : Subgroup (OddQuot z)} (hL : CFSG.IsComponent L) : ⁅L, modOdd z M⁆ = ⊥ := by
  have hsubC : IsSubnormal M (Subgroup.centralizer ({z} : Set G)) :=
    Q3CL.ClassicalClause.isSubnormal_of_uniqueInvolution d.late_cls hM hzM
  have hMC : M ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hsubC
  have hsolv : Group.IsSolvable ↥(modOdd z M) :=
    isSolvable_modOdd3 hMC (isSolvable_member3 d.hyp hM)
  rcases CFSG.LocalCores.component_subnormal_subgroup hL (isSubnormal_modOdd3 hsubC) with h | h
  · exfalso
    have : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect ↥L := hL.1.1
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  · exact h

end Std20Three

end Comp

end CFSG.ClassicalInvolution.Q3.Q3T6D
