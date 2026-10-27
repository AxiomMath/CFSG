module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerHeldPumpExclusionInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X), Sol78.IsSolomonPair t J 11 →
    ∀ (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)) (c e₀ : X) (he₀ : e₀ ∈ J),
      orderOf c = 2 → t * c = c * t → c ∈ normalizer (J : Set X) →
      c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J →
      ((θ ((⟨e₀, he₀⟩ : J) : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 4 →
    ∀ Jc M : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) →
      IsPComponent 2 (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))) →
      Nonempty (Jc ⧸ pPrimeCore 2 Jc ≃* alternatingGroup (Fin 7)) →
      M ≤ centralizer ({c} : Set X) → IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) →
      M.map (MulAut.conj t).toMonoidHom = M → Jc ≤ M →
      IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))) →
    ∀ a : X, orderOf a = 2 → a * c = c * a →
      ¬ ⁅M, (pPrimeCore 2 (centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
        (pPrimeCore 2 (centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype →
      (∀ m ∈ M, m⁻¹ * a ∉ UnbalancedLayer.coreActionKernel M) →
      IsEmpty (M ⧸ Open.fusionZStar M ≃* Blueprint.NativeSporadic.He)

end CFSG.ComponentClassification.SolMax
