module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Graph

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models

variable {G : Type} [Group G]

@[expose] def DeltaConnected (Ω : Set (Subgroup G)) : Prop := (commGraph Ω).Connected

theorem subset_of_adj_closed {Ω : Set (Subgroup G)} (hconn : DeltaConnected Ω) {𝔖 : Set (Subgroup G)}
    (hsub : 𝔖 ⊆ Ω) (hne : 𝔖.Nonempty)
    (hcl : ∀ N ∈ 𝔖, ∀ L ∈ Ω, L ≠ N → Commutes N L → L ∈ 𝔖) : Ω ⊆ 𝔖 := by
  obtain ⟨N₀, hN₀⟩ := hne
  intro L hL
  have key : ∀ v : ↥Ω, Relation.ReflTransGen (commGraph Ω).Adj ⟨N₀, hsub hN₀⟩ v →
      (v : Subgroup G) ∈ 𝔖 := by
    intro v hv
    induction hv with
    | refl => exact hN₀
    | @tail b c _ hadj ih =>
      obtain ⟨hne', hcomm⟩ := commGraph_adj.mp hadj
      exact hcl _ ih _ c.2 (fun e => hne' (Subtype.ext e).symm) hcomm
  exact key ⟨L, hL⟩ (SimpleGraph.reachable_iff_reflTransGen _ _ |>.mp (hconn.preconnected _ _))

end CFSG.ClassicalInvolution.RouteD
