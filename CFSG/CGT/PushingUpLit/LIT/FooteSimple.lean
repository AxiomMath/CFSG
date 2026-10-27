module

public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.Assembly

@[expose] def FooteNonsolvableSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → KProper InCatalog G → IsCharTwoType G →
    ∀ M X : Subgroup G, IsMaximalTwoLocal M → X ≤ M → (X.subgroupOf M).IsSubnormal →
      IsShortGroup ↥X → CFSG.IsQuasisimple (↥X ⧸ pCore 2 ↥X) →
        maximalTwoLocalsContaining (X : Set G) = {M} → (X.subgroupOf M).Normal

theorem not_isPGroup_of_isShortGroup {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsShortGroup ↥X) : ¬ IsPGroup 2 X := by
  intro hp
  have hle : X ≤ ⊥ := noTwoQuot_of_short hX ⊥
    (fun g _ n hn => by
      rw [Subgroup.mem_bot] at hn
      simp [hn])
    (fun g hg => by
      obtain ⟨k, hk⟩ := hp ⟨g, hg⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
  exact blockU_ne_bot_of_short hX (le_bot_iff.1 ((blockU_le X).trans hle))

theorem ne_top_of_isMaximalTwoLocal_of_isShortGroup {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {M X : Subgroup G} (hM : IsMaximalTwoLocal M) (hX : IsShortGroup ↥X) :
    M ≠ ⊤ := by
  intro hMtop
  obtain ⟨P, hP, hP2, hMP⟩ := hM.1
  have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.1 (hMP ▸ hMtop)
  have hPtop : P = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h0 | h0
    · exact absurd h0 hP
    · exact h0
  rw [hPtop] at hP2
  exact not_isPGroup_of_isShortGroup hX (hP2.to_le le_top)

end CFSG.CGT.PushingUpLit
