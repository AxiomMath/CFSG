module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapRes

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace SwapP2

theorem swapMemberResidueNine_of_leaves (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hX : SwapMemberResidueNineExact)
    (hC : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
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
        ClaimAHolds J n e E → FooteLit.IsSolomonMember M) :
    SwapMemberResidueNine := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow
  by_cases hex : ExactFivePump t J n e
  · exact hX X t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hex
  · exact hC X t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow
      (claimANine_of_inputs h33 h35 X t J n e E D M
        ⟨S, hCH, hMH, hMpc, hne, hJM, hMalt, hsmall, hnarrow⟩ hn hex)

end SwapP2

end CFSG.ComponentClassification.SolMax
