module

public import CFSG.ClassicalInvolution.Q3.Q3DBEdge
public import CFSG.ClassicalInvolution.Q3.Q3NLExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement


section Adjacency

variable {G : Type} [Group G]

@[expose] def TqAdj3 (M N : Subgroup G) : Prop :=
  ∃ a : G, IsClassicalMember3 M a ∧ ActsTrivOnQuot N a

@[expose] def TqAdjSymm3 (M N : Subgroup G) : Prop := TqAdj3 M N ∨ TqAdj3 N M

end Adjacency

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem actsTrivOnQuot_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a : G} (ha : IsClassicalMember3 M a) :
    ActsTrivOnQuot N a := by
  obtain ⟨h1, h2⟩ := fuzzy_of_mem_omegaNbr hK hint hN ha
  exact ⟨mem_normalizer_iff_conjSub_eq.mpr h1, h2⟩

theorem tqChain_of_dConnected3 (hK : IsClassicalMember3 K z) (hint : IsIntrinsicU (.sl2 3 1) K z)
    (hD : DConnected (CoreAssembly.conjClass K)) :
    ∀ L ∈ CoreAssembly.conjClass K, ∀ L' ∈ CoreAssembly.conjClass K,
      Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ TqAdjSymm3 M N) L L' := by
  intro L hL L' hL'
  have key : ∀ X, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ dAdj (CoreAssembly.conjClass K) M N)
      L X → X ∈ CoreAssembly.conjClass K ∧ Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ TqAdjSymm3 M N) L X := by
    intro X hX
    induction hX with
    | refl => exact ⟨hL, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ih.2.tail ⟨hbc.1, ?_⟩⟩
      rcases hbc.2 with h | h
      · obtain ⟨a, ha⟩ := exists_involution_of_mem_class hK ih.1
        exact Or.inl ⟨a, ha, actsTrivOnQuot_of_mem_omegaNbr hK hint h ha⟩
      · obtain ⟨a, ha⟩ := exists_involution_of_mem_class hK hbc.1
        exact Or.inr ⟨a, ha, actsTrivOnQuot_of_mem_omegaNbr hK hint h ha⟩
  exact (key L' (hD L hL L' hL')).2

theorem mem_tqMembers3_of_mem_omegaNbr (hK : IsClassicalMember3 K z)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M N : Subgroup G}
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass K) M) {a : G} (ha : IsClassicalMember3 M a) :
    N ∈ Q3NL.tqMembers3 (CoreAssembly.conjClass K) a :=
  ⟨hN.1, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (actsTrivOnQuot_of_mem_omegaNbr hK hint hN ha)⟩

end CFSG.ClassicalInvolution.Q3.Q3DB
