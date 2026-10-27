module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Twisted
public import CFSG.Adapters.TauCetiExceptional.EvenAll

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem diagOuterE6 : DiagOuterE6 := by
  intro q hv h3
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    (GaloisField q.p q.exponent) hK
  have e : AdjointQuotient Tag.E6 (GaloisField q.p q.exponent) ≃*
      adjointGroup Tag.E6 (GaloisField q.p q.exponent) :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  exact HasDiagOuterThree.of_mulEquiv (e.symm.trans b)
    (hasDiagOuterThree_adjointE6 (by rw [hK]; exact h3))

theorem diagOuterTwistedE6 : DiagOuterTwistedE6 := by
  intro q hv h3
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p (2 * q.exponent)
  have hK : Nat.card K = q.card ^ TwistTag.E6.order := by
    rw [PrimePower.card_def, GaloisField.card _ _ (by have := q.exponent_pos; omega),
      ← pow_mul, mul_comm]
    rfl
  let σ : K →+* K := iterateFrobenius K q.p q.exponent
  have hσ : ∀ x, σ x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact iterateFrobenius_def q.p q.exponent x
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K hK σ hσ
  have hmodel : ChevalleyExceptionalModel (ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩)
      .twistedE6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance, inferInstance, ?_, σ, ?_,
      ⟨b.symm⟩⟩
    · rw [hK, PrimePower.card_def]
    · intro x
      rw [hσ, PrimePower.card_def]
  obtain ⟨L, _, _, σ', hL, hσ', ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hmodel
  exact HasDiagOuterThree.of_mulEquiv e.symm
    (hasDiagOuterThree_graphFixedE6 σ' hL hσ' (by rw [PrimePower.card_def] at h3; exact h3))

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
