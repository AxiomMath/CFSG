module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.PlaneLevi
public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizers

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

public noncomputable section

open CFSG.HardMathSupport.Malle.SeitzCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.E6 (e6Index)
open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

theorem isPGroup_radicalIn_E6 (K : Type) [Field K] [Fintype K] {r : ℕ} [Fact r.Prime]
    [CharP K r] :
    IsPGroup r (parabolicRadicalIn Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) := by
  obtain ⟨n, -, hn⟩ := FiniteField.card K r
  have hn' : Nat.card K = r ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hQA := parabolicRadical_le_adjointGroup (τ := Tag.E6) (K := K)
    (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)
  have hrad : IsPGroup r (parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)) :=
    IsPGroup.of_card (n := (n : ℕ) * (parabolicRadicalRoots Tag.E6
      (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1)).ncard) (by
        rw [card_parabolicRadical, hn', ← pow_mul])
  exact hrad.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm


theorem plane_le_normalizer_radicalIn_E6 (K : Type) [Field K]
    (ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K)
    (hψ : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      ((ψ i (CFSG.LieType.Steinberg.SL.x 2 K γ c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        pinnedX Tag.E6 K (e6A2Frame i γ) (ε * c))
    (g : SL(3, K)) :
    plane ψ g ≤ Subgroup.normalizer
      ((parabolicRadicalIn Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :
        Subgroup ↥(adjointGroup Tag.E6 K)) : Set ↥(adjointGroup Tag.E6 K)) := by
  intro x hx
  have hN := plane_le_normalizer_parabolicRadical_E6 K ψ hψ g x hx
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro y
  have hy := hN (y : ModGL Tag.E6 K)
  simp only [parabolicRadicalIn, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hy

theorem e6PlaneLeviSet_ne_univ :
    e6FrameLeviSet 0 ∪ e6FrameLeviSet 1 ≠ (Set.univ : Set (Fin Tag.E6.rank)) := by
  intro h
  have hmem : e6Index 1 ∈ e6FrameLeviSet 0 ∪ e6FrameLeviSet 1 := by
    rw [h]
    exact Set.mem_univ _
  rw [Set.mem_union] at hmem
  simp only [e6FrameLeviSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  revert hmem
  decide

end

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
