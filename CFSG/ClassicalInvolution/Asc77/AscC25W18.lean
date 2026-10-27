module

public import CFSG.ClassicalInvolution.Asc77.AscC25W1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace C25W

section Closure

variable {G : Type} [Group G] [Finite G]

theorem stronglyClosed_inter_of_good {z : G} {S A E : Subgroup G} (hz2 : z * z = 1)
    (hA : ∀ x ∈ A, ∀ c : G, c * z * c⁻¹ = z → c * x * c⁻¹ ∈ S → c * x * c⁻¹ ∈ A)
    (𝒟 : Set (Subgroup G)) (hcompl : ∀ D ∈ 𝒟, ∀ x ∈ A, x ∈ D ∨ x * z ∈ D)
    (hzD : ∀ D ∈ 𝒟, z ∉ D)
    (hbad : ∀ D ∈ 𝒟, ∀ x ∈ D, x ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)))
    (hEA : E ≤ A) (hED : ∀ D ∈ 𝒟, E ≤ D)
    (hmax : ∀ x ∈ A, (∀ D ∈ 𝒟, x ∈ D) → x ∈ E)
    (hEg : ∀ e ∈ E, e ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({e * z} : Set G))) :
    ∀ e ∈ E, ∀ c : G, c * z * c⁻¹ = z → c * e * c⁻¹ ∈ S → c * e * c⁻¹ ∈ E := by
  intro e he c hcz hcS
  by_cases he1 : e = 1
  · subst he1
    simp
  have heA : c * e * c⁻¹ ∈ A := hA e (hEA he) c hcz hcS
  have hgood : z ∈ zStarOf (Subgroup.centralizer ({(c * e * c⁻¹) * z} : Set G)) := by
    have h1 : (c * e * c⁻¹) * z = c * (e * z) * c⁻¹ := by
      calc (c * e * c⁻¹) * z = c * e * c⁻¹ * (c * z * c⁻¹) := by rw [hcz]
        _ = c * (e * z) * c⁻¹ := by group
    rw [h1]
    exact (mem_zStarOf_centralizer_conj_iff hcz).mpr (hEg e he he1)
  refine hmax _ heA fun D hD => ?_
  rcases hcompl D hD _ heA with h | h
  · exact h
  · exfalso
    by_cases h1 : (c * e * c⁻¹) * z = 1
    ·
      have hez : c * e * c⁻¹ = z := by
        calc c * e * c⁻¹ = (c * e * c⁻¹) * z * z := by rw [mul_assoc _ z z, hz2, mul_one]
          _ = z := by rw [h1, one_mul]
      have : e = z := by
        calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
          _ = c⁻¹ * z * c := by rw [hez]
          _ = z := by
            calc c⁻¹ * z * c = c⁻¹ * (c * z * c⁻¹) * c := by rw [hcz]
              _ = z := by group
      exact hzD D hD (this ▸ hED D hD he)
    · exact hbad D hD _ h h1 hgood

end Closure

end C25W

end CFSG.ClassicalInvolution.Asc77
