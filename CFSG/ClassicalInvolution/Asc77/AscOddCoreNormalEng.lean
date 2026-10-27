module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section
namespace CFSG.ClassicalInvolution.Asc77.AscFusion
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups Pointwise
variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_oddCoreOf_of_normal_odd_gen {M N : Subgroup G} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M := by
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hn
  have hodd' : Odd (Nat.card ↥(N.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
  have hle : N.subgroupOf M ≤ classicalInvolutionOddCore ↥M := by
    unfold classicalInvolutionOddCore
    exact le_sSup ⟨hnorm, hodd'⟩
  intro x hx
  exact ⟨⟨x, hNM hx⟩, hle hx, rfl⟩

end CFSG.ClassicalInvolution.Asc77.AscFusion
