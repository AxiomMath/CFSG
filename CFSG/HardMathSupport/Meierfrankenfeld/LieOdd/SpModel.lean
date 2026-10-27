module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SpThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank TauCeti

theorem center_eq_bot_of_psp {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {K : Type} [Field K] [Finite K] {r : ℕ}
    (hr : 2 ≤ r) (hK : 5 ≤ Nat.card K ∨ (Nat.card K = 3 ∧ 3 ≤ r))
    (hKodd : Odd (Nat.card K)) (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp r K)) :
    Subgroup.center L = ⊥ := by
  have hM : Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp r K)) ≃*
      Multiplicative (ZMod (Nat.gcd 2 (Nat.card K - 1)))) := by
    rcases hK with h5 | ⟨h3, hr3⟩
    · exact (CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_hopfMultiplier hr h5).2
    · exact (CFSG.LieType.Steinberg.CentralExt.SpThree.psp_three_hopfMultiplier hr3 h3).2
  obtain ⟨φ⟩ := hM
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e
  have h2 : Nat.gcd 2 (Nat.card K - 1) = 2 := by
    obtain ⟨k, hk⟩ := hKodd
    have : Nat.card K - 1 = 2 * k := by omega
    rw [this, Nat.gcd_mul_right_right]
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd, h2, Nat.card_zmod] at hdvd
  have h1 : Nat.card (Subgroup.center L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem exists_psp_model_of_lie_C {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.C r q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.C r q, hv⟩).Group) :
    Subgroup.center L = ⊥ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q.p ^ q.exponent ∧ Nonempty (L ≃* StatedProj (StatedSp r K)) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨hr3, hp2⟩ := hrange
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C r q, hv⟩ : ValidLieTypeIndex)
  set K := ↥(ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩)
  have hK : Nat.card K = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, PrimePower.card_def]
  let e' : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp r K) :=
    e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (q.prime_p.eq_two_or_odd'.resolve_left hp2).pow
  have hK3 : 3 ≤ Nat.card K := by
    rw [hK]
    have := q.prime_p.two_le
    have hp3 : 3 ≤ q.p := by omega
    exact hp3.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  have hK5 : 5 ≤ Nat.card K ∨ (Nat.card K = 3 ∧ 3 ≤ r) := by
    by_cases h3 : Nat.card K = 3
    · exact Or.inr ⟨h3, hr3⟩
    · left
      have h4 : Nat.card K ≠ 4 := by
        intro h4
        rw [h4] at hKodd
        exact absurd hKodd (by decide)
      omega
  have hbot := center_eq_bot_of_psp hperf hodd (by omega) hK5 hKodd e'
  refine ⟨hbot, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e'

theorem exists_psp_model_of_lie_B2 {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.B 2 q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) (hp2 : q.p ≠ 2)
    (hq5 : 5 ≤ q.card) :
    Subgroup.center L = ⊥ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = q.p ^ q.exponent ∧ Nonempty (L ≃* StatedProj (StatedSp 2 K)) := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B 2 q, hv⟩ : ValidLieTypeIndex)
  set K := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)
  have hK : Nat.card K = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, PrimePower.card_def]
  let e' : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp 2 K) :=
    e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (q.prime_p.eq_two_or_odd'.resolve_left hp2).pow
  have hK5 : 5 ≤ Nat.card K := by
    rw [hK]
    simpa [PrimePower.card_def] using hq5
  have hbot := center_eq_bot_of_psp hperf hodd le_rfl (Or.inl hK5) hKodd e'
  refine ⟨hbot, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e'

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
