module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

@[expose] def SignalizerSwapAltExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) → False

end CFSG.ComponentClassification.SolMax
