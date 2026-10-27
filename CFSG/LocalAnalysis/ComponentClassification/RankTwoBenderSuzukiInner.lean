module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderHypIICover
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting

public section

namespace CFSG.ComponentClassification.RankTwoBender

open CFSG.ComponentClassification.OuterAutomorphisms

theorem eq_one_of_sq_eq_one_of_odd_card {H : Type*} [Group H] (hodd : Odd (Nat.card H))
    {q : H} (hq : q ^ 2 = 1) : q = 1 := by
  have : Finite H := Nat.finite_of_card_ne_zero hodd.pos.ne'
  rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hq) with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ orderOf_dvd_natCard q) (Nat.not_even_iff_odd.mpr hodd ∘ even_iff_two_dvd.2)

theorem suzukiInvolutoryInner : SuzukiInvolutoryInner := by
  intro a ha Y _ eY α hα
  obtain ⟨eS⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card (p := 2) (n := 2 * a + 1) (by omega)
  have hodd := (CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha
    (GaloisField 2 (2 * a + 1)) hK).2.2.2.2.2.2
  rw [← Nat.card_congr (equivalence (eY.trans eS)).toEquiv] at hodd
  have hq : (QuotientGroup.mk α : Outer Y) = 1 :=
    eq_one_of_sq_eq_one_of_odd_card hodd (by rw [pow_two, ← QuotientGroup.mk_mul, hα]; rfl)
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff α).1 hq
  exact ⟨y, hy.symm⟩

end CFSG.ComponentClassification.RankTwoBender
