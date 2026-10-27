module

public import CFSG.CGT.PushingUpLit.Glue.NinePair

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.Nine
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowOf_of_le {Q N N' : Subgroup G} (hQ : IsSylowOf 2 Q N) (hQN' : Q ≤ N')
    (hN' : N' ≤ N) : IsSylowOf 2 Q N' := by
  refine ⟨hQN', hQ.2.1, fun hd => hQ.2.2 ?_⟩
  have h := Subgroup.relIndex_mul_relIndex Q N' N hQN' hN'
  rw [← h]
  exact dvd_mul_of_dvd_left hd _

theorem oTwoIn_le_normalizer_of_subnormal {L Y : Subgroup G} (hYL : Y ≤ L)
    (hs : (Y.subgroupOf L).IsSubnormal) (hsh : IsShortGroup ↥Y) :
    oTwoIn L ≤ Subgroup.normalizer (Y : Set G) := by
  have hblock : IsBlockOf (Y.subgroupOf L) :=
    ⟨hs, isShortGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYL).symm hsh⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := le_normalizer_of_isPGroup_normal hblock (pCore_normal (p := 2)) pCore_isPGroup
  intro c hc
  obtain ⟨c', hc', rfl⟩ := hc
  have := coe_mem_normalizer_map (h1 hc')
  rwa [Subgroup.map_subgroupOf_eq_of_le hYL] at this

theorem exists_extremal_pair (M I : Subgroup G) (h : ∃ Y L : Subgroup G, NinePair M I Y L) :
    ∃ Y L : Subgroup G, NinePair M I Y L ∧
      ∀ Y' L' : Subgroup G, NinePair M I Y' L' → Nat.card Y' ≤ Nat.card Y := by
  obtain ⟨Y₀, L₀, hp⟩ := h
  obtain ⟨Y, ⟨L, hL⟩, hmax⟩ := Set.exists_max_image {Y : Subgroup G | ∃ L, NinePair M I Y L}
    (fun Y => Nat.card Y) (Set.toFinite _) ⟨Y₀, L₀, hp⟩
  exact ⟨Y, L, hL, fun Y' L' hp' => hmax Y' ⟨L', hp'⟩⟩

end CFSG.CGT.PushingUpLit.Glue
