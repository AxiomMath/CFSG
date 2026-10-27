module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOdd
public import CFSG.RankThree.Chevalley.SteinbergCFOddE8InnerField

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

section E8


theorem isLocallyBalancedAbs_adjointE8_fieldOdd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hcnt : degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.E8 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_E8_of_degCount_eq_two K hp hcnt) fun x hxp hxo => ?_
  refine fieldCoreAt_of_oddInnerField hℓ hℓ2 hf K hK
    (odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ hℓ2 hf K hK).1 hp
    (fun σ hσp => not_coprime_card_adjointE8 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast hℓ hf hK hp hσp]
  exact hcnt

end E8

section FamilyE8


theorem crossCharFamAt_E8_fieldOdd :
    CrossCharFamAt .E8 (regimeExcFieldOdd TauCeti.LieTypeIndex.E8 (degCount Tag.E8)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE8_fieldOdd q.prime_p hq2
    q.exponent_pos K (hK.trans (TauCeti.PrimePower.card_def q)) hp hcnt)

end FamilyE8

end CFSG.HardMathSupport.Timmesfeld.CrossChar
