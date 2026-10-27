module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

structure Sol78Lemma612Out (G : Type) [Group G] (L : Subgroup G) (t : G) (W : Subgroup G) :
    Prop where
  t_order : orderOf t = 2
  t_mem : t ∈ centralizer (L : Set G)
  elemAbelian : IsElemAbelian 2 W
  card : Nat.card W = 2 ^ 12
  t_mem_W : t ∈ W
  weaklyClosed : Finkelstein77.WeaklyClosedInNormalizer W
  quotient : Nonempty (normalizer (W : Set G) ⧸
    (centralizer (W : Set G)).subgroupOf (normalizer (W : Set G)) ≃* Carrier .M24)
  index_two : ∃ N₀ : Subgroup (normalizer (W : Set G)), N₀.Normal ∧ N₀.index = 2 ∧
    (⟨t, Subgroup.le_normalizer t_mem_W⟩ : normalizer (W : Set G)) ∉ N₀

end CFSG.EvenSporadicStandard.Solomon78
