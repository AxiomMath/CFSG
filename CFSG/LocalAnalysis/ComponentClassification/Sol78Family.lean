module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def solomonPump (L T : Subgroup G) : Subgroup G :=
  ⨆ g ∈ pLayerOf 2 (centralizer (T : Set G)),
    (pLayerOf 2 (L ⊓ centralizer (T : Set G))).map (MulAut.conj g).toMonoidHom

variable (G) in
@[expose] def solomonFamily : Set (Subgroup G) :=
  {L | ⁅L, L⁆ = L ∧ ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
    T ≤ UnbalancedLayer.coreActionKernel L ∧
    IsPCompIn 2 (centralizer (T : Set G))
      (oPrimeResidualOf 2 (pPrimeCoreOf 2 (centralizer (T : Set G)) ⊔
        pLayerOf 2 (L ⊓ centralizer (T : Set G))))}

@[expose] def SolomonLt (L K : Subgroup G) : Prop :=
  L ∈ solomonFamily G ∧ K ∈ solomonFamily G ∧
    ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≤ UnbalancedLayer.coreActionKernel L ∧
      IsPCompIn 2 (solomonPump L T) K

@[expose] def SolomonStep (L K : Subgroup G) : Prop :=
  (SolomonLt L K ∨ SolomonLt K L) ∧
    Nonempty (L ⧸ Open.fusionZStar L ≃* K ⧸ Open.fusionZStar K)

@[expose] def SolomonEquiv (L K : Subgroup G) : Prop :=
  L ∈ solomonFamily G ∧ Relation.ReflTransGen SolomonStep L K

@[expose] def IsSolomonMaximal (L : Subgroup G) : Prop :=
  L ∈ solomonFamily G ∧
    ∀ K K₁ : Subgroup G, SolomonEquiv L K → SolomonLt K K₁ → SolomonEquiv L K₁

@[expose] def IsSolomonWide (L : Subgroup G) : Prop :=
  ∀ K : Subgroup G, SolomonEquiv L K → 2 ≤ CFSG.pRank 2 K

variable (G) in
@[expose] def solomonKStar : Set (Subgroup G) :=
  {L | IsSolomonMaximal L ∧ IsSolomonWide L}

@[expose] def kStarOf (H : Subgroup G) : Subgroup G :=
  sSup {K | IsPCompIn 2 H K ∧ K ∈ solomonKStar G}

@[expose] def MaximalComponentTheoremInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ L : Subgroup G, FooteLit.IsSolomonMaximal L → 3 ≤ CFSG.pRank 2 L →
      (∀ g : G, (L : Set G) * (CFSG.conjugate L g : Set G) =
          (CFSG.conjugate L g : Set G) * (L : Set G) →
        ⁅L, CFSG.conjugate L g⁆ ≠
          (pPrimeCore 2 ↥(L ⊔ CFSG.conjugate L g)).map (L ⊔ CFSG.conjugate L g).subtype) ∧
      ∀ H : Subgroup G, CFSG.IsPLocal 2 H → L ≤ H →
        Even (Nat.card ↥(H ⊓ UnbalancedLayer.coreActionKernel L)) →
        H ≤ normalizer ((pPrimeCoreOf 2 H ⊔ L : Subgroup G) : Set G)

@[expose] def MaximalityLemmaInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ n : ℕ, Odd n → 9 ≤ n → (∃ (t : X) (J : Subgroup X), SolAltLit.IsAltTwoComponent t J n) →
      (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' → Odd n' →
        n' ≤ n) →
      ∀ L : Subgroup X, FooteLit.IsSolomonMember L →
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n)) → FooteLit.IsSolomonMaximal L

end CFSG.ComponentClassification.Sol78
