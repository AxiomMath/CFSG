module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOrders
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldOdd
public import CFSG.LieType.SeitzGeneration.ExcPlaneG2

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

section OddF4G2


theorem isLocallyBalancedAbs_adjointF4_fieldOdd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hcnt : degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)) = 2) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.F4 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hnd : ¬ p ∣ Nat.card K ^ 2 - 1 := by
    intro h
    have h2 := orderOf_dvd_two_of_dvd_sq_sub_one hpK h
    rcases degCount_F4_eq_two hcnt with h3 | h3 | h3 <;> rw [h3] at h2 <;> omega
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_adjointGroup_F4 K hp hp2 hpK hnd) fun x hxp hxo => ?_
  have hNF := conj_normalForm_of_pointwise
    (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .F4 (Or.inl rfl)).1
  refine fieldCoreAt_of_oddInnerField hℓ hℓ2 hf K hK hNF hp
    (fun σ hσp => not_coprime_card_adjointF4 (fixSubfield σ) hp ?_) hxp hxo
  rw [card_fixSubfield_cast hℓ hf hK hp hσp]
  exact hcnt

theorem isLocallyBalancedAbs_adjointG2_fieldOdd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hd : p ∣ Nat.card K ^ 2 - 1) :
    IsLocallyBalancedAbs p 3 (adjointGroup Tag.G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  refine isLocallyBalancedAbs_adjoint_of_fieldCore K hp
    (rankLE2_adjointGroup_G2 K hp hp5 hpK) fun x hxp hxo => ?_
  have hNF := conj_normalForm_of_pointwise
    (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)).1
  refine fieldCoreAt_of_oddInnerField hℓ hℓ2 hf K hK hNF hp
    (fun σ hσp => not_coprime_card_adjointG2 (fixSubfield σ) hp ?_) hxp hxo
  exact dvd_sq_sub_one_of_cast_eq hK1 Nat.card_pos (card_fixSubfield_cast hℓ hf hK hp hσp).symm hd

end OddF4G2

section FamilyF4G2


@[expose] def regimeG2FieldOdd (idx : TauCeti.ValidLieTypeIndex) (p : ℕ) : Prop :=
  ∃ q : TauCeti.PrimePower, idx.1 = .G2 q ∧ 5 ≤ p ∧ p ∣ q.card ^ 2 - 1 ∧ p ∣ q.exponent ∧
    q.p ≠ 2 ∧ q.p ≠ 3

theorem crossCharFamAt_F4_fieldOdd :
    CrossCharFamAt .F4 (regimeExcFieldOdd TauCeti.LieTypeIndex.F4 (degCount Tag.F4)) := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hcnt, hpf, hq2⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointF4_fieldOdd q.prime_p hq2
    q.exponent_pos K (hK.trans (TauCeti.PrimePower.card_def q)) hp hp2 hpK hcnt)

theorem crossCharFamAt_G2_fieldOdd : CrossCharFamAt .G2 regimeG2FieldOdd := by
  rintro ⟨d, hv⟩ _ p hp hp2 hc ⟨q, hd, hp5, hdq, hpf, hq2, hq3⟩
  change d = _ at hd
  subst hd
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, _, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hdq
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointG2_fieldOdd q.prime_p hq2
    hq3 q.exponent_pos K (hK.trans (TauCeti.PrimePower.card_def q)) hp hp5 hpK hdq)

end FamilyF4G2

end CFSG.HardMathSupport.Timmesfeld.CrossChar
