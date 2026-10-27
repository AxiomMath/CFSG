module

public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

@[expose] def Bal368 (F : Type) [Group F] [Finite F] : Prop :=
  ∀ {K J : Subgroup F} {z t : F}, Mem3 K z → Mem3 J t → z ≠ t →
    t ∈ Subgroup.normalizer (K : Set F) → (∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K) →
      z ∈ Subgroup.normalizer (J : Set F) → ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J

theorem not_mem_oddCoreOf_of_orderOf_two {X : Subgroup F} {x : F} (hx : orderOf x = 2) :
    x ∉ oddCoreOf X := by
  intro hmem
  have hodd : Odd (Nat.card (oddCoreOf X)) := oddCoreOf_odd_natCard X
  have h1 : orderOf (⟨x, hmem⟩ : oddCoreOf X) ∣ Nat.card (oddCoreOf X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hx] at h1
  exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat h1)) even_two

end CFSG.ClassicalInvolution.Q3.Q3T6B
