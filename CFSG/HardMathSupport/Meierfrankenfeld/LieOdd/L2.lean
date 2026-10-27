module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Model
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Dim
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Order
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.L2Arith
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderOrder
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator

theorem pow_le_two_pow_mul {p d N : ℕ} (h : p + 1 ≤ 2 ^ d) : (p + 1) ^ N ≤ 2 ^ (d * N) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left h N

theorem noIrrFFOffender_lie_A1 {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hp : q.p ≠ 2)
    (he : 3 ≤ q.exponent) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨K, _, _, hchar, hK, ⟨θ⟩⟩ := exists_mulEquiv_psl2_of_lie_A1 hW hq hirr hv e hp he
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have h27 : 27 ≤ q.p ^ q.exponent :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_left hp3 q.exponent
  have hq3 : 3 < q.p ^ q.exponent := by omega
  have hord := card_sup_le_of_psl2 hW hp hK hq3 hirr θ hEN hel
  by_contra hcon
  push Not at hcon
  have hU1 := FFToolkit.card_le_card_sup_of_offender hW hq hirr hEN hE hel hcon
  have h2 := succ_le_two_pow_orderOf (p := q.p) hp
  rcases Nat.even_or_odd q.exponent with heven | hodd
  · have he4 : 4 ≤ q.exponent := by
      obtain ⟨k, hk⟩ := heven
      omega
    have hdim := two_pow_le_card_of_psl2 hW hp hK (by omega) θ
    have harith := card_pGammaL2_lt_of_even hp3 he4
    have h4 := pow_le_two_pow_mul (N := (q.p ^ q.exponent - 1) / (2 * (q.p - 1))) h2
    exact absurd ((hU1.trans hord).trans_lt (harith.trans_le (h4.trans hdim))) (lt_irrefl _)
  · have hdim := two_pow_le_card_of_psl2_of_odd hW hp hK (by omega) θ hodd
    have harith := card_pGammaL2_lt_of_odd hp3 he hodd
    have h4 := pow_le_two_pow_mul (N := (q.p ^ q.exponent - 1) / (q.p - 1)) h2
    exact absurd ((hU1.trans hord).trans_lt (harith.trans_le (h4.trans hdim))) (lt_irrefl _)

theorem noFFModule_lie_A1 (d : ValidLieTypeIndex) {q : PrimePower} (hd : d.1 = .A 1 q)
    (hp : q.p ≠ 2) (he : 3 ≤ q.exponent) : NoFFModule (CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_lie_A1 hv hp he)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
