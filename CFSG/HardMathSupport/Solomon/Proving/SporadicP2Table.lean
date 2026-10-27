module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.AGLEmbedding

private instance (name : TauCeti.SporadicName) (p : ℕ) : Decidable (B3SporRestPair name p) := by
  unfold B3SporRestPair
  infer_instance

private theorem sporP2_table : ∀ s : TauCeti.SporadicName, ∀ p ∈ Finset.range 80, p.Prime →
    p ≠ 2 → p ^ 2 ∣ sporOrd s → SporadicOnePair s p ∨ B3SporRestPair s p := by
  decide +kernel

theorem sporadicP2Table_of_orders
    (hOrd : ∀ s : TauCeti.SporadicName,
      Nat.card (TauCeti.CFSGIndex.sporadic s).Group = CFSG.AGLEmbedding.sporOrd s) :
    CFSG.HardMathSupport.Solomon.Coordinator.SporadicP2Table := by
  intro name p hp hp2 hdvd
  rw [hOrd name] at hdvd
  have hN : sporOrd name ≠ 0 := by cases name <;> simp [sporOrd]
  have hmem : p ∈ (sporOrd name).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans hdvd, hN⟩
  exact sporP2_table name p (Finset.mem_range.2 (primeFactors_lt name p hmem)) hp hp2 hdvd

end CFSG.HardMathSupport.Solomon.Proving
