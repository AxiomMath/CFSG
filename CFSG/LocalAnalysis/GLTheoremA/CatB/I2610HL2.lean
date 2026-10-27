module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9

theorem card_of_catalogIs_isL2prime {X : Type} [Group X] (h : catalogIs X isL2prime) :
    Nat.card X = 60 ∨ ∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ Nat.card X = r * (r ^ 2 - 1) / 2 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [isL2prime] at hi
  | sporadic s => simp [isL2prime] at hi
  | alternating n hn =>
    simp only [isL2prime] at hi
    obtain rfl := hi
    refine Or.inl ?_
    rw [Nat.card_congr e.toEquiv]
    rw [show Nat.card (TauCeti.CFSGIndex.alternating 5 hn).Group =
      Nat.card (alternatingGroup (Fin 5)) from rfl]
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · simp [isL2prime] at hi
      · simp only [isL2prime] at hi
        obtain ⟨hqprime, hq7⟩ := hi
        refine Or.inr ⟨q.card, hqprime, hq7, ?_⟩
        have hq2 : q.card ≠ 2 := by omega
        have hodd : Odd q.card := hqprime.odd_of_ne_two hq2
        have hL := CFSG.Models.lieModel_A 1 q hv e
        have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
        have hc := CFSG.Blueprint.LieModel.card_eq_lieOrd (show (2 : ℕ) ≠ 0 by norm_num) hB
        have hqcard : q.p ^ q.exponent = q.card := (TauCeti.PrimePower.card_def q).symm
        rw [hqcard] at hc
        have htwo := CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.ordA_one_mul_two hodd
        have hb : q.card * (q.card ^ 2 - 1) = CFSG.Open.ordA 1 q.card * 2 := htwo.symm
        rw [hc, hb, Nat.mul_div_left _ (by norm_num : 0 < 2)]
        rfl
      · simp [isL2prime] at hi
    | _ => simp [isL2prime] at hi

theorem not_catalogIs_isL2prime_of_card_eq {X : Type} [Group X]
    (h : Nat.card X = 25920) : ¬ catalogIs X isL2prime := by
  intro hc
  rcases card_of_catalogIs_isL2prime hc with h60 | ⟨r, hrprime, hr7, hr⟩
  · omega
  · have hr2 : r ≠ 2 := by omega
    have hodd : Odd r := hrprime.odd_of_ne_two hr2
    obtain ⟨k, hk⟩ := hodd
    have h2 : 2 ∣ r ^ 2 - 1 := by
      refine ⟨2 * k * (k + 1), ?_⟩
      have h1 : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
        have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
        omega
      rw [hk]
      exact h1
    have h2' : 2 ∣ r * (r ^ 2 - 1) := dvd_mul_of_dvd_right h2 r
    have hdiv : r * (r ^ 2 - 1) / 2 = 25920 := by omega
    have heq : r * (r ^ 2 - 1) = 51840 := by
      have hm := Nat.div_mul_cancel h2'
      omega
    have hdvd : r ∣ 51840 := ⟨r ^ 2 - 1, by rw [← heq]⟩
    have h' : r ∣ 2 ^ 7 * 3 ^ 4 * 5 := by norm_num; exact hdvd
    rcases hrprime.dvd_mul.mp h' with h1 | h5
    · rcases hrprime.dvd_mul.mp h1 with h2 | h3
      · have hr2' : r = 2 :=
          (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_two).1 (hrprime.dvd_of_dvd_pow h2)
        omega
      · have hr3 : r = 3 :=
          (Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).1 (hrprime.dvd_of_dvd_pow h3)
        omega
    · have hr5 : r = 5 := (Nat.prime_dvd_prime_iff_eq hrprime (by norm_num)).1 h5
      omega

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
