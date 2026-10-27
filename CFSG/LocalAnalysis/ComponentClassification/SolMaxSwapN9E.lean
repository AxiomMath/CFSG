module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBJ
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapBK

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapP2

theorem pumpSideNine_holds : PumpSideNine := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd he₀H N₁ hP hfix m hmo hθ
  obtain ⟨θN⟩ := hθ
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  obtain ⟨hm5, hmn⟩ := degree_le_of_pumpData hs hd hP hmo θN
  have hm6 : m ≠ 6 := by
    obtain ⟨a, ha⟩ := hmo
    omega
  have hlayer : IsPComponent 2 ((fixA M e₀ r).subgroupOf (N₁ ⊓ centralizer ({e₀} : Set X))) := by
    have h1 := hP.layer
    rwa [hfix, sup_idem] at h1
  have h := pumpSide_of_type' hs (by omega) hd he₀H χr hArle hArpc hP.le hP.pc hP.cover θN
    (by omega) hmn hm6 (Or.inr ⟨hfix, hlayer⟩)
  intro f hf
  obtain ⟨a, ha, h1, h2⟩ := h f hf
  refine ⟨a, ha, ?_, h2⟩
  rwa [hfix, sup_idem] at h1

theorem pumpDiagNine_holds : PumpDiagNine := by
  intro X _ _ _ t J n e E D M hs hn e₀ F DF r hd he₀H hOr hFH N₁ hP
  by_contra hdiag
  obtain ⟨⟨χr⟩, ⟨hArle, hArpc⟩, -⟩ := pump_holds X t J n e E D M hs e₀ F DF r hd he₀H
  obtain ⟨ψN⟩ := nonempty_fusionZStar_of_diagonal hs hd he₀H hP hdiag
  exact false_of_diagonalZ' hs (by omega) hd he₀H hOr hFH χr hArle hArpc hP.le hP.pc hP.cover
    hdiag ψN

theorem swapMemberResidueNineOfClaimA_of_exotic (hEx : SwapMemberResidueNineExotic) :
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
        ClaimAHolds J n e E → FooteLit.IsSolomonMember M := by
  intro X _ _ _ t J n e E D S hn hCH M hMH hMpc hne hJM hMalt hsmall hnarrow hCA
  exact swapMemberResidueNine_of_claimA pumpSideNine_holds pumpDiagNine_holds hEx S hn hCH hMH
    hMpc hne hJM hMalt hsmall hnarrow hCA

end SwapP2

end CFSG.ComponentClassification.SolMax
