module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedEdgeless
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyBase
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureFrame
public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {G : Type} [Group G]

@[expose] def dAdj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  J ∈ Asc77.omegaNbr Ω K ∨ K ∈ Asc77.omegaNbr Ω J

@[expose] def DConnected (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) K J

@[expose] def DEdgeless (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, ¬ dAdj Ω K J

theorem dAdj_symm {Ω : Set (Subgroup G)} {K J : Subgroup G} (h : dAdj Ω K J) : dAdj Ω J K :=
  h.symm

theorem ne_of_dAdj {Ω : Set (Subgroup G)} {K J : Subgroup G} (h : dAdj Ω K J) : K ≠ J := by
  rcases h with h | h
  · exact h.2.1.symm
  · exact h.2.1

section Commuting

theorem dAdj_of_commutes {Ω : Set (Subgroup G)} {K J : Subgroup G} (hJ : J ∈ Ω) (hne : K ≠ J)
    (h : Commutes K J) : dAdj Ω K J := by
  refine Or.inl ⟨hJ, hne.symm, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  refine ⟨Subgroup.map J.subtype (P : Subgroup ↥J), ⟨J, hJ, P, rfl⟩, Subgroup.map_subtype_le _, ?_⟩
  rintro _ ⟨r, -, rfl⟩
  refine Subgroup.centralizer_le_normalizer (K : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact h k hk r r.2

theorem dConnected_of_omegaConnected {Ω : Set (Subgroup G)} (h : OmegaConnected Ω) :
    DConnected Ω := by
  intro K hK J hJ
  have key : ∀ L, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K L →
      L ∈ Ω ∧ Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) K L := by
    intro L hL
    induction hL with
    | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ?_⟩
      by_cases hbc' : b = c
      · rw [← hbc']
        exact ih.2
      · exact ih.2.tail ⟨hbc.1, dAdj_of_commutes hbc.1 hbc' hbc.2⟩
  exact (key J (h K hK J hJ)).2

theorem dConnected_of_deltaConnected {K : Subgroup G}
    (h : CFSG.ClassicalInvolution.DeltaConnected K) :
    DConnected (Generic.CoreAssembly.conjClass K) := by
  rw [← Generic.CoreAssembly.conjugateSet_eq_range]
  exact dConnected_of_omegaConnected (omegaConnected_of_deltaConnected h)

theorem deltaEdgeless_of_dEdgeless {K : Subgroup G}
    (h : DEdgeless (Generic.CoreAssembly.conjClass K)) : DeltaEdgeless K := by
  intro X Y ⟨hX, hY, hne, hcomm⟩
  rw [Generic.CoreAssembly.conjugateSet_eq_range] at hX hY
  exact h X hX Y hY (dAdj_of_commutes hY hne fun x hx y hy => hcomm x hx y hy)

end Commuting

end CFSG.ClassicalInvolution.Disconnected
