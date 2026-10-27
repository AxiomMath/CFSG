module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Cover5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem card_center_eq_three_of_hasLabel_twA5 {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : HasLabel K (fun l : GLALabel => l = lab)) (ht : lab.tag = .twA)
    (hr : lab.rank = 5) (hn : 2 ≤ lab.n) (hz : Subgroup.center K ≠ ⊥) :
    Nat.card (Subgroup.center K) = 3 := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht hr hn
  subst ht
  subst hr
  have hK' : Rk2IsLabel K ⟨.twA, 5, n⟩ := hK
  have hdvd : Nat.card (Subgroup.center K) ∣ Nat.gcd 6 (2 ^ n + 1) :=
    rk2_card_center_dvd_twA (X := K) (ℓ := 5) (n := n) hK'
      (i61_exc_PSU (f := n) (by omega))
  have h3 : Nat.card (Subgroup.center K) ∣ 3 :=
    i61_dvd_three_of_dvd_six (n := n) (by omega)
      (hdvd.trans (Nat.gcd_dvd_left 6 (2 ^ n + 1)))
      (hdvd.trans (Nat.gcd_dvd_right 6 (2 ^ n + 1)))
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h3'
  · exact absurd (Subgroup.card_eq_one.1 h1) hz
  · exact h3'

theorem i166On_famTwA5_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamTwA5 := by
  intro K _ _ lab p hK hfam hp hp2 _ he hr
  have hfam' := hfam
  obtain ⟨ht, hrk, hn2, -⟩ := hfam'
  by_cases hz : Subgroup.center K = ⊥
  · rcases Nat.lt_or_ge lab.n 4 with hlt | hge
    · have hn23 : lab.n = 2 ∨ lab.n = 3 := by omega
      rcases hn23 with hn | hn
      · exact concl166S_twA5Four_of_transport htr hK hfam hp hp2 he hr hn
      · exact concl166S_twA5Eight_of_transport htr hK hfam hp hz hn
    · exact concl166S_twA5Big_of_transport htr hK hfam hp hp2 hz hge
  · exact concl166S_twA5Cover_of_transport htr hK hfam hp hp2 he hr
      (card_center_eq_three_of_hasLabel_twA5 hK ht hrk hn2 hz)

theorem i166On_famTwA5_holds : I166On i166FamTwA5 :=
  i166On_famTwA5_of_transport
    (fun {K R} _ _ _ _ e {p} h => exists_concl166S_of_mulEquiv e h)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
