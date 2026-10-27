module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorsAll
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.AGLEmbeddingD2

private theorem factorization_psuThreeOrder {p : ℕ} (hp : p.Prime) :
    (p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) / Nat.gcd 3 (p + 1)).factorization p = 3 := by
  have hp1 := hp.one_lt
  have hpg : ¬ p ∣ Nat.gcd 3 (p + 1) := fun h =>
    hp1.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_refl p)).1
      (h.trans (Nat.gcd_dvd_right 3 (p + 1)))))
  have hpA : ¬ p ∣ p ^ 2 - 1 := fun h =>
    hp1.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos) ▸ dvd_pow_self p two_ne_zero)))
  have hpB : ¬ p ∣ p ^ 3 + 1 := fun h =>
    hp1.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_pow_self p (by norm_num))).1 h))
  have hg : Nat.gcd 3 (p + 1) ∣ p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    have h1 : p + 1 ∣ p ^ 3 + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow p 1 (n := 3) (by decide)
    exact ((Nat.gcd_dvd_right 3 (p + 1)).trans h1).trans
      ((dvd_mul_left _ _).trans (dvd_mul_left _ _))
  have hA0 : p ^ 2 - 1 ≠ 0 := by
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
    omega
  rw [Nat.factorization_div hg, Finsupp.tsub_apply, Nat.factorization_eq_zero_of_not_dvd hpg,
    Nat.factorization_mul (by positivity) (mul_ne_zero hA0 (by positivity)),
    Nat.factorization_mul hA0 (by positivity), Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hpA, Nat.factorization_eq_zero_of_not_dvd hpB]
  rfl

theorem kFactUnitaryThreeSylow : KFactUnitaryThreeSylow := by
  intro K _ _ d ⟨e⟩ p hp _ ⟨q, hqp, hq1, hd⟩ _ T
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hcard := Nat.card_congr eF.toEquiv
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU q.prime_p q.exponent_pos hF
    (by norm_num)] at hcard
  rw [hqp, hq1, pow_one] at hcard
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv] at hcard
  have hprod : ∏ i ∈ Finset.Icc 2 3, ((p : ℤ) ^ i - (-1) ^ i).toNat =
      (p ^ 2 - 1) * (p ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    have h : ((p : ℤ) ^ 2 - (-1) ^ 2).toNat = p ^ 2 - 1 := by
      simp only [even_two, Even.neg_pow, one_pow, ← Nat.cast_pow]
      omega
    have h' : ((p : ℤ) ^ 3 - (-1) ^ 3).toNat = p ^ 3 + 1 := by
      simp only [Odd.neg_pow (by decide : Odd 3), one_pow, ← Nat.cast_pow]
      omega
    rw [h, h']
  rw [Sylow.card_eq_multiplicity T, hcard, hprod, factorization_psuThreeOrder hp]

end CFSG.AGLEmbeddingD2
