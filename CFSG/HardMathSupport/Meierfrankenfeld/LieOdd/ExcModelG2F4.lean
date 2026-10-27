module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier
public import CFSG.LieType.Steinberg.CentralExt.FieldThreeF4Multiplier

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

theorem exists_adjoint_model_of_lie_G2
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (_hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p ≠ 2) (h5 : 5 ≤ q.card)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ⧸ Subgroup.center L ≃* AdjointQuotient .G2 K) := by
  obtain ⟨K, hKf, hKfin, hK⟩ := exists_field_of_index q hv (LieTypeIndex.fieldOrder_G2 q)
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hp2 K hKq
  let e' : L ⧸ Subgroup.center L ≃* AdjointQuotient .G2 K := e.trans φ.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) :=
    (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.g2_hopfMultiplier (by rw [hKq]; exact h5)).2
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .G2 K)) = 1 :=
    Nat.card_of_subsingleton 1
  rw [hM] at hdvd
  exact ⟨Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hdvd), K, hKf, hKfin, hK, ⟨e'⟩⟩

theorem exists_adjoint_model_of_lie_F4
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (_hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.F4 q).Valid) (hp2 : q.p ≠ 2)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.F4 q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.p ^ q.exponent ∧
        Nonempty (L ⧸ Subgroup.center L ≃* AdjointQuotient .F4 K) := by
  obtain ⟨K, hKf, hKfin, hK⟩ := exists_field_of_index q hv (LieTypeIndex.fieldOrder_F4 q)
  have hKq : Nat.card K = q.card := by rw [hK, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hp2 K hKq
  let e' : L ⧸ Subgroup.center L ≃* AdjointQuotient .F4 K := e.trans φ.symm
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have he1 : 1 ≤ q.exponent := q.exponent_pos
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) := by
    rcases eq_three_or_five_le_of_odd_prime_pow q.prime_p hp2 he1 with h3 | h5
    · exact (CFSG.LieType.Steinberg.CentralExt.FieldThree.f4_three_hopfMultiplier
        (by rw [hK, h3])).2
    · exact (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_hopfMultiplier
        (by rw [hK]; exact h5)).2
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) = 1 :=
    Nat.card_of_subsingleton 1
  rw [hM] at hdvd
  exact ⟨Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.1 hdvd), K, hKf, hKfin, hK, ⟨e'⟩⟩

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
