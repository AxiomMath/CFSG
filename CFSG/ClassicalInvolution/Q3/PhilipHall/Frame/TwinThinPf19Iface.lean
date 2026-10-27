module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMaxOrb
public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

@[expose] def PairInv (K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g u : G) : Prop :=
  u ∈ K ⊔ K' ∧ u ∈ pCoreOf 2 (conjSub g (piGen π)) ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z

@[expose] def NbrPiTwin (K₀ K K' : Subgroup G) (π : Set (Subgroup G)) (g : G) : Prop :=
  (∀ J ∈ omegaNbr (CoreAssembly.conjClass K₀) K, J ∈ π ∨ J = K') ∧ conjSub g K' ∈ π

@[expose] def SecYu (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G)) (g : G) : Prop :=
  ∀ u : G, PairInv K K' z π g u →
    (∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u, ∀ L' ∈ centMembers (CoreAssembly.conjClass K₀) u,
      ∃ x ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub x L = L') ∧
    (∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u, ∀ t : G, IsUniqueInvolution L t →
      t ∈ pCoreOf 2 (centLayer (CoreAssembly.conjClass K₀) u)) ∧
    ∃ k : ℕ, 5 ≤ k ∧ Nonempty (AEIdent (centMembers (CoreAssembly.conjClass K₀) u) k)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThin
