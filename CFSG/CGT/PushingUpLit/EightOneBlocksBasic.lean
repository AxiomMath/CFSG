module

public import CFSG.CGT.PushingUpLit.BlocksCommute
public import CFSG.CGT.PushingUpLit.EightOneRel

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem InClassX.not_isPGroup {X : Subgroup G} (hX : InClassX ↥X) : ¬ IsPGroup 2 ↥X := by
  intro hp
  have hle : X ≤ (⊥ : Subgroup G) := by
    refine noTwoQuot_of_short hX.1 ⊥ (fun g _ n hn => ?_) fun g hg => ?_
    · rw [Subgroup.mem_bot] at hn ⊢
      simp [hn]
    · obtain ⟨k, hk⟩ := hp ⟨g, hg⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact blockU_ne_bot_of_short hX.1 (le_bot_iff.1 ((blockU_le X).trans hle))

theorem InClassX.commutator_ne_bot {X : Subgroup G} (hX : InClassX ↥X) : ⁅X, X⁆ ≠ ⊥ := by
  intro h
  refine blockU_ne_bot_of_short hX.1 (le_bot_iff.1 ?_)
  calc blockU X ≤ ⁅X, X⁆ := Subgroup.commutator_mono (oTwoIn_le X) le_rfl
    _ = ⊥ := h

theorem isBlockOfInX_conjugate {N L : Subgroup G} (hL : IsBlockOfInX N L) {g : G} (hg : g ∈ N) :
    IsBlockOfInX N (conjugate L g) :=
  ⟨CFSG.GroupTheory.conjugate_le_of_mem hL.1 hg, isSubnormal_conjugate hL.2.1 hg,
    inClassX_conjugate hL.2.2 g⟩

theorem unique_block_above {N X L₁ L₂ : Subgroup G} (hN : IsCharacteristicP 2 ↥N)
    (hX : InClassX ↥X) (h₁ : IsBlockOfInX N L₁) (h₂ : IsBlockOfInX N L₂) (hX₁ : X ≤ L₁)
    (hX₂ : X ≤ L₂) : L₁ = L₂ := by
  by_contra hne
  have h := distinct_blocks_commute_of_isBlockOfInX hN h₁ h₂ hne
  refine InClassX.commutator_ne_bot hX (le_bot_iff.1 ?_)
  calc ⁅X, X⁆ ≤ ⁅L₁, L₂⁆ := Subgroup.commutator_mono hX₁ hX₂
    _ = ⊥ := h

theorem conjugate_block_eq {N X L : Subgroup G} (hN : IsCharacteristicP 2 ↥N) (hX : InClassX ↥X)
    (hL : IsBlockOfInX N L) (hXL : X ≤ L) {g : G} (hgN : g ∈ N)
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) : conjugate L g = L := by
  refine unique_block_above hN hX (isBlockOfInX_conjugate hL hgN) hL ?_ hXL
  have h := CFSG.GroupTheory.conjugate_mono g hXL
  rwa [ThreeFromEight.conjugate_eq_self_of_mem_normalizer hgX] at h

end CFSG.CGT.PushingUpLit
