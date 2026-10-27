module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP2

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace SwapP2

@[expose] def SwapMemberResidueEleven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 11 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      FooteLit.IsSolomonMember M

@[expose] def SwapMemberResidueNine : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → n = 9 →
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      M.map (MulAut.conj t).toMonoidHom ≠ M → J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) →
      (∀ P : Subgroup X, P ≤ UnbalancedLayer.coreActionKernel J → IsPGroup 2 P →
        Nat.card P ≤ 2) →
      (∀ R : Subgroup X, R ≠ ⊥ → IsPGroup 2 R →
        R ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
        R ≤ UnbalancedLayer.coreActionKernel M →
        ¬ centralizer (R : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      FooteLit.IsSolomonMember M

theorem swapMemberResidue_of_eleven_nine (h11 : SwapMemberResidueEleven)
    (h9 : SwapMemberResidueNine) : SwapMemberResidue := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow
  rcases hn with h | h
  · exact h9 X t J n e E D S h hCH M hMH hMpc hne hJM hMalt hsmall hnarrow
  · exact h11 X t J n e E D S h hCH M hMH hMpc hne hJM hMalt hsmall hnarrow

end SwapP2

end CFSG.ComponentClassification.SolMax
