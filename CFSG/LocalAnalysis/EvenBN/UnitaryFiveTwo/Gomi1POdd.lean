module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddClassical
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddExc
public import CFSG.ClassicalInvolution.Orders.Ree

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Blueprint CFSG.Open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab


theorem gomi1P_not_odd_lie
    {T : Type} [Group T] [Finite T] {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hT : LieModel T t n p f)
    (hord : ∃ m : ℕ, Odd m ∧ Nat.card T = 2 ^ 8 * m)
    (hE : ∃ E : Subgroup T, Nat.card E = 2 ^ 6 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      ∀ x ∈ E, x * x = 1)
    (hdvd : 3 ^ 2 * 5 ^ 2 * 17 ∣ Nat.card T) : False := by
  have _ := hdvd
  obtain ⟨m, hmodd, hcard⟩ := hord
  obtain ⟨E, hEcard, hEcomm, hEsq⟩ := hE
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h8 : 2 ^ 8 ∣ Nat.card T := ⟨m, hcard⟩
  have hT0 := hT
  rcases hT with ⟨ht, hc⟩ | ⟨hn, ht, he⟩ | ⟨hn, ht, hr⟩ | ⟨hn, rfl, hs⟩
  · exact gomi1P_not_odd_lie_classical hp hp2 hc ⟨m, hmodd, hcard⟩
      ⟨E, hEcard, hEcomm, hEsq⟩
  · subst hn
    have hcardX := CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 he
    cases t
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact gomiOdd_false_of_g2 hp hp2 hT0 E hEcard hEsq
    · have h : Nat.card T = ordF4 (p ^ f) := hcardX
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (h ▸ gomiOdd_two_pow_nine_dvd_ordF4 hq)
    · have h : Nat.card T = ordE6 (p ^ f) := hcardX
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (h ▸ gomiOdd_two_pow_nine_dvd_ordE6 hq)
    · have h : Nat.card T = ordE7 (p ^ f) := hcardX
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (h ▸ gomiOdd_two_pow_nine_dvd_ordE7 hq)
    · have h : Nat.card T = ordE8 (p ^ f) := hcardX
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (h ▸ gomiOdd_two_pow_nine_dvd_ordE8 hq)
    · have h : Nat.card T = ordTwistedE6 (p ^ f) := hcardX
      exact gomiOdd_false_of_two_pow_nine_dvd hmodd hcard
        (h ▸ gomiOdd_two_pow_nine_dvd_ordTwistedE6 hq)
    · exact gomiOdd_false_of_d4 hp hp2 hT0 E hEcard hEsq
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  · subst hn
    have hadm := hT0.admissible
    cases t
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · obtain ⟨-, a, -, hfa, hN⟩ := CFSG.ClassicalInvolution.card_of_reeTitsModel_twistedG2 hr
      rw [hN] at h8
      exact gomiOdd_not_two_pow_eight_dvd_ordRee ⟨a, hfa⟩ h8
    · exact hp2 hadm.2.2.2.1
    · exact hp2 hadm.2.2.2.1
  · exact hp2 hs.1

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
