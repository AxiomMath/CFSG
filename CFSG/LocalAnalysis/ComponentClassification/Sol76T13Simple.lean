module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Setting
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

@[expose] def SimpleAmbient (G : Type) [Group G] : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ Assembly.KProper Blueprint.Catalog G

@[expose] def SolomonThm13Simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ∀ N : Subgroup G, ¬ IsKBalanced N

theorem not_isSolomonChoice_of_simple (h : SolomonThm13Simple) {G : Type} [Group G] [Finite G]
    (hG : SimpleAmbient G) {N : Subgroup G} (hN : IsSolomonChoice N) : False :=
  h G hG.1 hG.2.1 hG.2.2 N hN.1

theorem not_le_solomonKStarOf_top_of_simple {G : Type} [Group G] [Finite G]
    (hG : SimpleAmbient G) {N : Subgroup G} (hN : IsKBalanced N) :
    ¬ solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G) := by
  have := hG.1
  obtain ⟨r, K, -, hiff, h2r, -⟩ := hN
  have hK0 : K ⟨0, by omega⟩ ∈ kStarComponents N := (hiff _).mpr ⟨_, rfl⟩
  have hKD : K ⟨0, by omega⟩ ≤ solomonKStarOf N := le_iSup₂_of_le _ hK0 le_rfl
  obtain ⟨b, hbK, hb2⟩ := exists_orderOf_eq_two_of_pRank
    ((by norm_num : 1 ≤ 2).trans (two_le_pRank_of_mem_solomonKStar hK0.2))
  intro hle
  have hbot := solomonKStarOf_top_eq_bot hG.2.1 hb2
  have hb : b ∈ solomonKStarOf (⊤ : Subgroup G) := hle (hKD hbK)
  rw [hbot, mem_bot] at hb
  rw [hb, orderOf_one] at hb2
  norm_num at hb2

theorem solomonThm13Simple_of_thm13 (h : SolomonThm13Input) : SolomonThm13Simple :=
  fun G _ _ hs hna hK N hN => not_le_solomonKStarOf_top_of_simple ⟨hs, hna, hK⟩ hN (h G N hN)

theorem solomonThm13Simple_of_noChoice
    (h : ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G,
      ¬ IsSolomonChoice N) : SolomonThm13Simple := by
  intro G _ _ hs hna hK N hN
  obtain ⟨N', hN'⟩ := exists_isSolomonChoice (G := G) fun hG =>
    not_le_solomonKStarOf_top_of_simple ⟨hs, hna, hK⟩ hN (hG N hN)
  exact h G ⟨hs, hna, hK⟩ N' hN'

end CFSG.ComponentClassification.Sol76T13
