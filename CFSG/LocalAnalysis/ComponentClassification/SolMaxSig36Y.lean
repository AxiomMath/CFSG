module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36X
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36R

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerCaseOneStrongClosureNarrowInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → 11 ≤ n → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)), IsPermAction θ ρ →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (13 ≤ n → ∀ (x : X) (hx : x ∈ M), x * x = 1 →
        (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
          centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (13 ≤ n → ∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
        normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ Q

theorem signalizerCaseOneStrongClosureInput_of_narrow (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hSC : SignalizerCaseOneStrongClosureNarrowInput) :
    SignalizerCaseOneStrongClosureInput := by
  intro X _ _ _ t J n e E D S hn hW M hMH hMpc hJM hHN hθ hsup Q S' hQK hQ2 hQcard htQ hQS hSH
    hS2 hScard
  obtain ⟨θ⟩ := hθ
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega)
    (by obtain ⟨b, hb⟩ := S.pair.2.1; omega) θ
  exact hSC X t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q S' hQK hQ2 hQcard htQ hQS hSH
    hS2 hScard (fun hn13 => S.claimA_M_of_sup h33 h35 hT13 hML hSch hPump hN1 hn13 hMH hMpc
      hJM hHN hsup hρ)
    (fun hn13 T hTQ hT1 => S.normalizer_le_of_le_Q h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup hρ
      (S.claimA_M_of_sup h33 h35 hT13 hML hSch hPump hN1 hn13 hMH hMpc hJM hHN hsup hρ)
      (hQK.trans inf_le_left) (hQK.trans inf_le_right) hQ2 htQ hTQ hT1)

theorem signalizerTrivialityInput_of_residues_narrow (hmax : SolAltLit.MaximalAltComponentInput)
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hSwap : SignalizerSwapAltExclusion) (hGT : Sol78.StronglyClosedResidualInput)
    (hA : SignalizerClaimASmallInput) (h2 : SignalizerCaseTwoFinishInput)
    (hSC : SignalizerCaseOneStrongClosureNarrowInput) (h9 : SignalizerNineInput) :
    SolAltLit.SignalizerTrivialityInput :=
  signalizerTrivialityInput_of_residues hmax hbal hPump hN1 hsmall hT13 hML hSch hSwap hGT hA h2
    (signalizerCaseOneStrongClosureInput_of_narrow
      (balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall)
      (signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall) hT13 hML hSch hPump hN1 hSC)
      h9

end CFSG.ComponentClassification.SolMax
