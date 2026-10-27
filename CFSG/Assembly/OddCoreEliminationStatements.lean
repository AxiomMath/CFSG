module

public import CFSG.Assembly.CompletedOddCoreSpan

public section

namespace CFSG.Assembly.Dichotomy

@[expose] def subgroupCenter {G : Type*} [Group G] (S : Subgroup G) : Subgroup G :=
  S ⊓ Subgroup.centralizer (S : Set G)

@[expose] def PerfectInvolutionCoverageStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], commutator G = ⊤ → 3 ≤ twoRank G →
    ∀ t : G, orderOf t = 2 → ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E

@[expose] def NonisolatedConjugateStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], commutator G = ⊤ → 3 ≤ twoRank G →
    ∀ (S : Sylow 2 G) (V : Subgroup G), V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 →
    pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) = 2 →
    ∃ g : G, V.map (MulAut.conj g⁻¹).toMonoidHom ≤ S ∧
      3 ≤ pRank 2 ((S : Subgroup G) ⊓
        Subgroup.centralizer ((V.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G))

@[expose] def CompletedSpanPreparationStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 3 ≤ twoRank G →
    ∀ (S : Sylow 2 G) (U : Subgroup G), U ≤ S → (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) →
    IsElemAbelian 2 U → Nat.card U = 4 →
    (∀ D : Subgroup G, IsElemAbelian 2 D → Nat.card D = 8 → OddCoreSpanCompleted D) →
    Odd (Nat.card (oddCoreSpan U)) ∧
    (S : Subgroup G) ≤ Subgroup.normalizer (oddCoreSpan U : Set G) ∧
    (∀ u ∈ U, u ≠ 1 →
      oddCoreSpan U ⊓ Subgroup.centralizer ({u} : Set G) = involutionOddCore u) ∧
    (∀ E : Subgroup G, E ≤ S → IsElemAbelian 2 E → Nat.card E = 8 →
      oddCoreSpan E = oddCoreSpan U) ∧
    (∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 →
      3 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) →
      oddCoreSpan V = oddCoreSpan U ∧
        Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (oddCoreSpan U : Set G)) ∧
    (∀ D : Subgroup G, D ≤ S → 3 ≤ pRank 2 D →
      Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (oddCoreSpan U : Set G)) ∧
    ((∃ E : Subgroup G, E ≤ S ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ oddCoreSpan E ≠ ⊥) →
      oddCoreSpan U ≠ ⊥ ∧
        (oddCore G = ⊥ → Subgroup.normalizer (oddCoreSpan U : Set G) ≠ ⊤))

@[expose] def CentralInvolutionCentralizerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ¬ IsComponentType G →
    ∀ (S : Sylow 2 G) (U : Subgroup G), U ≤ S → (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) →
    IsElemAbelian 2 U → Nat.card U = 4 →
    ((∃ V : Subgroup G, V ≤ subgroupCenter S ∧ IsElemAbelian 2 V ∧ Nat.card V = 4) →
      U ≤ subgroupCenter S) →
    ∀ z ∈ U ⊓ subgroupCenter S, orderOf z = 2 →
    ∀ W : Subgroup G, Odd (Nat.card W) → (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) →
    (∀ u ∈ U, u ≠ 1 → involutionOddCore u ≤ W) →
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (W : Set G)

@[expose] def FusionControlStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G), 3 ≤ pRank 2 (S : Subgroup G) →
    ∀ U : Subgroup G, U ≤ S → (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) →
    IsElemAbelian 2 U → Nat.card U = 4 →
    ∀ z ∈ U ⊓ subgroupCenter S, orderOf z = 2 →
    ∀ M : Subgroup G, (S : Subgroup G) ≤ M → Subgroup.centralizer ({z} : Set G) ≤ M →
    (∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 →
      3 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) →
      Subgroup.normalizer (V : Set G) ≤ M) →
    (∀ D : Subgroup G, D ≤ S → 3 ≤ pRank 2 D → Subgroup.normalizer (D : Set G) ≤ M) →
    ∀ P : Subgroup G, P ≤ M → IsPGroup 2 P → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ M →
      ∃ m ∈ M, ∀ x ∈ P, g⁻¹ * x * g = m⁻¹ * x * m

@[expose] def FourSpanEqualizationStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], commutator G = ⊤ → 3 ≤ twoRank G →
    ∀ (S : Sylow 2 G) (W : Subgroup G), (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) →
    (∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 →
      3 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) → oddCoreSpan V = W) →
    (∀ P : Subgroup G, P ≤ S → IsPGroup 2 P → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      ∃ m ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ P, g⁻¹ * x * g = m⁻¹ * x * m) →
    ∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 → oddCoreSpan V = W

@[expose] def CommonSpanStrongEmbeddingStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], commutator G = ⊤ → 3 ≤ twoRank G → ¬ IsComponentType G →
    ∀ (S : Sylow 2 G) (W : Subgroup G), (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) →
    Subgroup.normalizer (W : Set G) ≠ ⊤ →
    (∀ V : Subgroup G, V ≤ S → IsElemAbelian 2 V → Nat.card V = 4 → oddCoreSpan V = W) →
    (∀ P : Subgroup G, P ≤ Subgroup.normalizer (W : Set G) → IsPGroup 2 P → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.normalizer (W : Set G) →
      ∃ m ∈ Subgroup.normalizer (W : Set G), ∀ x ∈ P, g⁻¹ * x * g = m⁻¹ * x * m) →
    (∀ t ∈ Subgroup.normalizer (W : Set G), orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (W : Set G)) ∧
      dichotomyStronglyEmbedded (Subgroup.normalizer (W : Set G))

end CFSG.Assembly.Dichotomy
