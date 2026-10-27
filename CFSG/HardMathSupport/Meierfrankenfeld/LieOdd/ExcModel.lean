module

public import CFSG.Adapters.TauCetiExceptional.BridgeAll
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeE7Multiplier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

theorem eq_three_or_five_le_of_odd_prime_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    p ^ e = 3 ∨ 5 ≤ p ^ e := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h3' : 3 ≤ p ^ e := hp3.trans (Nat.le_self_pow (by omega) p)
  have h4 : p ^ e ≠ 4 := by
    intro h4
    rw [h4] at hodd
    exact absurd hodd (by decide)
  omega

theorem not_dvd_of_dvd_pow_sub_one {p e z : ℕ} (hp : p.Prime) (he : 1 ≤ e) (h : z ∣ p ^ e - 1) :
    ¬ p ∣ z := by
  intro hpz
  have h1 : p ∣ p ^ e - 1 := hpz.trans h
  have h2 : p ∣ p ^ e := dvd_pow_self p (by omega)
  have h3 : p ∣ p ^ e - (p ^ e - 1) := Nat.dvd_sub h2 h1
  have : p ^ e - (p ^ e - 1) = 1 := by
    have : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
    omega
  rw [this] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

theorem card_eq_of_zmod_equiv {M : Type*} [Group M] {m : ℕ}
    (h : Nonempty (M ≃* Multiplicative (ZMod m))) : Nat.card M = m := by
  obtain ⟨φ⟩ := h
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exists_field_of_index (q : PrimePower) {c : PrimePower → LieTypeIndex}
    (hv : (c q).Valid) (hq : ValidLieTypeIndex.fieldOrder ⟨c q, hv⟩ = q.card) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField (⟨c q, hv⟩ : ValidLieTypeIndex)
  refine ⟨↥(ValidLieTypeIndex.fixedField ⟨c q, hv⟩), inferInstance, inferInstance, ?_⟩
  rw [ValidLieTypeIndex.card_fixedField, hq, PrimePower.card_def]

theorem exists_adjoint_model_of_lie_E6
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (_hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.E6 q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    ¬ q.p ∣ Nat.card (Subgroup.center L) ∧ Nat.card (Subgroup.center L) ≤ 3 ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ⧸ Subgroup.center L ≃* AdjointQuotient .E6 K) := by
  obtain ⟨K, hKf, hKfin, hK⟩ := exists_field_of_index q hv (LieTypeIndex.fieldOrder_E6 q)
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp2 K hKq
  let e' : L ⧸ Subgroup.center L ≃* AdjointQuotient .E6 K := e.trans φ.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have he1 : 1 ≤ q.exponent := q.exponent_pos
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E6 K)) =
      Nat.gcd 3 (Nat.card K - 1) := by
    rcases eq_three_or_five_le_of_odd_prime_pow q.prime_p hp2 he1 with h3 | h5
    · exact card_eq_of_zmod_equiv
        (CFSG.LieType.Steinberg.CentralExt.FieldThree.e6_three_hopfMultiplier
          (by rw [hK, h3])).2
    · exact card_eq_of_zmod_equiv
        (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier
          (by rw [hK]; exact h5)).2
  rw [hM] at hdvd
  refine ⟨?_, ?_, K, hKf, hKfin, hK, ⟨e'⟩⟩
  · have h1 : Nat.card (Subgroup.center L) ∣ Nat.card K - 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
    rw [hK] at h1
    exact not_dvd_of_dvd_pow_sub_one q.prime_p he1 h1
  · exact Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.gcd_dvd_left _ _))

theorem exists_adjoint_model_of_lie_E7
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.E7 q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.E7 q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ⧸ Subgroup.center L ≃* AdjointQuotient .E7 K) := by
  obtain ⟨K, hKf, hKfin, hK⟩ := exists_field_of_index q hv (LieTypeIndex.fieldOrder_E7 q)
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp2 K hKq
  let e' : L ⧸ Subgroup.center L ≃* AdjointQuotient .E7 K := e.trans φ.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have he1 : 1 ≤ q.exponent := q.exponent_pos
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E7 K)) =
      Nat.gcd 2 (Nat.card K - 1) := by
    rcases eq_three_or_five_le_of_odd_prime_pow q.prime_p hp2 he1 with h3 | h5
    · exact card_eq_of_zmod_equiv
        (CFSG.LieType.Steinberg.CentralExt.FieldThree.e7_three_hopfMultiplier
          (by rw [hK, h3])).2
    · exact card_eq_of_zmod_equiv
        (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e7_hopfMultiplier
          (by rw [hK]; exact h5)).2
  rw [hM] at hdvd
  have h2 : Nat.card (Subgroup.center L) ∣ 2 := hdvd.trans (Nat.gcd_dvd_left _ _)
  have h1 : Nat.card (Subgroup.center L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact ⟨Subgroup.eq_bot_of_card_eq _ h1, K, hKf, hKfin, hK, ⟨e'⟩⟩

theorem exists_adjoint_model_of_lie_E8
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (_hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.E8 q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.E8 q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ⧸ Subgroup.center L ≃* AdjointQuotient .E8 K) := by
  obtain ⟨K, hKf, hKfin, hK⟩ := exists_field_of_index q hv (LieTypeIndex.fieldOrder_E8 q)
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp2 K hKq
  let e' : L ⧸ Subgroup.center L ≃* AdjointQuotient .E8 K := e.trans φ.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have he1 : 1 ≤ q.exponent := q.exponent_pos
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) := by
    rcases eq_three_or_five_le_of_odd_prime_pow q.prime_p hp2 he1 with h3 | h5
    · exact (CFSG.LieType.Steinberg.CentralExt.FieldThree.e8_three_hopfMultiplier
        (by rw [hK, h3])).2
    · exact (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.e8_hopfMultiplier
        (by rw [hK]; exact h5)).2
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .E8 K)) = 1 :=
    Nat.card_of_subsingleton 1
  rw [hM] at hdvd
  exact ⟨Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hdvd), K, hKf, hKfin, hK, ⟨e'⟩⟩

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
