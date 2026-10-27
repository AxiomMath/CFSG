module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Odd

variable {A : Type} [Group A] [Finite A]

theorem mem_oddCore_of_mem_oddCoreOf {X H : Subgroup A} (hHX : H ≤ X) {y : ↥H}
    (hy : (y : A) ∈ oddCoreOf X) : y ∈ classicalInvolutionOddCore ↥H := by
  set S : Subgroup ↥H := (oddCoreOf X).subgroupOf H with hS
  have hnorm : S.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := conj_mem_oddCoreOf (hHX g.2) hx
    simpa using this
  have hodd : Odd (Nat.card S) := by
    have h1 : S.map H.subtype ≤ oddCoreOf X := by
      rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hs
    have h2 : Nat.card ↥(S.map H.subtype) = Nat.card S :=
      Subgroup.card_map_of_injective H.subtype_injective
    have h3 : Nat.card ↥(S.map H.subtype) ∣ Nat.card ↥(oddCoreOf X) := Subgroup.card_dvd_of_le h1
    have h4 : Odd (Nat.card ↥(oddCoreOf X)) := oddCoreOf_odd_natCard X
    rw [← h2]
    exact h4.of_dvd_nat h3
  have hle : S ≤ classicalInvolutionOddCore ↥H := le_sSup ⟨hnorm, hodd⟩
  exact hle (Subgroup.mem_subgroupOf.mpr hy)

theorem mem_oddCoreOf_of_mem_oddCore {X H : Subgroup A} (hHX : H ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (H : Set A))
    {y : ↥H} (hy : y ∈ classicalInvolutionOddCore ↥H) : (y : A) ∈ oddCoreOf X := by
  have hsub : IsSubnormal H X := isSubnormal_of_normal_subgroupOf hHX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hHX).mpr hnorm)
  have h1 := Balance.oddCoreIn_le_of_isSubnormal hsub
  exact h1 ⟨y, hy, rfl⟩

end Odd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
