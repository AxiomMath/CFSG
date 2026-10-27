module

public import CFSG.GH74.Uniqueness.Statements
public import CFSG.GH74.Uniqueness.SU.SU1Graph
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G]

@[expose] def IsFour (X V : Subgroup G) : Prop :=
  V ≤ X ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 2 ^ 2

@[expose] def IsIsolatedVertex (X V : Subgroup G) : Prop :=
  ∃ h : IsFour X V, SU1.IsIsolated 2 (⟨V, h⟩ : SU1.Ep2Vertex 2 X)

@[expose] def compSet (X U : Subgroup G) : Set (Subgroup G) :=
  {E | ∃ (hU : IsFour X U) (hE : IsFour X E),
    (SU1.Ep2Graph 2 X).Reachable (⟨U, hU⟩ : SU1.Ep2Vertex 2 X) ⟨E, hE⟩}

@[expose] def conjSub (g : G) (E : Subgroup G) : Subgroup G :=
  E.map (MulAut.conj g).toMonoidHom

@[expose] def PermutesComp (U : Subgroup G) (g : G) : Prop :=
  ∀ E : Subgroup G, E ∈ compSet ⊤ U → conjSub g E ∈ compSet ⊤ U

@[expose] def IsSylowIn (X P : Subgroup G) : Prop :=
  P ≤ X ∧ IsPGroup 2 P ∧ Odd (P.relIndex X)

@[expose] def IsFusionIsolated (X P : Subgroup G) (z : G) : Prop :=
  z ∈ P ∧ ∀ u ∈ X, u⁻¹ * z * u ∈ P → u⁻¹ * z * u = z

section Finite

variable [Finite G]

@[expose] noncomputable def gammaTwo (S : Subgroup G) : Subgroup G :=
  Open.properTwoGenCoreGamma S 2

structure Setup18Core (S : Sylow 2 G) (U : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  rank : 3 ≤ Open.pRank 2 (S : Subgroup G)
  four : IsFour (S : Subgroup G) U
  normal : (S : Subgroup G) ≤ normalizer (U : Set G)

structure Setup18 (S : Sylow 2 G) (U : Subgroup G) : Prop extends Setup18Core S U where
  kgh : KGH G

structure Hyp184Core (S : Sylow 2 G) (U M : Subgroup G) : Prop extends Setup18Core S U where
  gamma_ne_top : gammaElem (S : Subgroup G) ≠ ⊤
  maximal : IsCoatom M
  gamma_le : gammaElem (S : Subgroup G) ≤ M
  disconn_le : (∃ E : Subgroup G, IsFour ⊤ E ∧ E ∉ compSet ⊤ U) →
    ∀ g : G, PermutesComp U g → g ∈ M

structure Hyp184 (S : Sylow 2 G) (U M : Subgroup G) : Prop extends Hyp184Core S U M where
  kgh : KGH G

@[expose] def Concl184a (S : Sylow 2 G) (M : Subgroup G) : Prop :=
  gammaTwo (S : Subgroup G) ≤ M

@[expose] def Concl184b (M : Subgroup G) : Prop :=
  ∀ V : Subgroup G, ¬ IsIsolatedVertex M V

end Finite

end CFSG.GH74.Uniqueness.SU.SU4
