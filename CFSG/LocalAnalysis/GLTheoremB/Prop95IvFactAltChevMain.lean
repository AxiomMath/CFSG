module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactAltChevDispatch
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95L2Three

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremB.Prop95Parts CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)


theorem two_pow_not_dvd_factorial {n : ℕ} (hn : n ≠ 0) : ¬ 2 ^ n ∣ n.factorial := by
  intro h
  have h1 := pow_dvd_iff_le_emultiplicity.mp h
  have h2 := Nat.emultiplicity_two_factorial_lt hn
  exact absurd h2 (not_lt.mpr h1)

theorem two_pow_succ_dvd_factorial {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ^ k ∣ n.factorial / 2) :
    2 ^ (k + 1) ∣ n.factorial := by
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have h := mul_dvd_mul_right hk 2
  rw [Nat.div_mul_cancel h2, ← pow_succ] at h
  exact h

theorem le_of_pow_dvd_of_not {k j m : ℕ} (hk : 2 ^ k ∣ m) (hnd : ¬ 2 ^ (j + 1) ∣ m) :
    k ≤ j := by
  by_contra hc
  exact hnd ((pow_dvd_pow 2 (by omega : j + 1 ≤ k)).trans hk)

theorem pow_lt_factorial_half : ∀ n : ℕ, 15 ≤ n → 2 ^ (3 * (n - 2)) < n.factorial / 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hfac : (n + 1).factorial / 2 = (n + 1) * (n.factorial / 2) := by
      rw [Nat.factorial_succ, Nat.mul_div_assoc _ h2]
    have hexp : 3 * (n + 1 - 2) = 3 * (n - 2) + 3 := by omega
    have h8 : 8 ≤ n + 1 := by omega
    rw [hfac, hexp, pow_add]
    have h3 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h3]
    nlinarith [Nat.mul_le_mul_right (n.factorial / 2) h8]

theorem magnitude_lt (n : ℕ) (hn : 7 ≤ n) (h8 : n ≠ 8) (h9 : n ≠ 9) (h10 : n ≠ 10) (k : ℕ)
    (hk : 2 ^ k ∣ n.factorial / 2) : 2 ^ (3 * k) < n.factorial / 2 := by
  rcases (show n = 7 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ 15 ≤ n by omega) with
    rfl | rfl | rfl | rfl | rfl | h15
  · have hk3 : k ≤ 3 := le_of_pow_dvd_of_not (j := 3) hk (by decide)
    calc 2 ^ (3 * k) ≤ 2 ^ (3 * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < Nat.factorial 7 / 2 := by decide
  · have hk7 : k ≤ 7 := le_of_pow_dvd_of_not (j := 7) hk (by decide)
    calc 2 ^ (3 * k) ≤ 2 ^ (3 * 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < Nat.factorial 11 / 2 := by decide
  · have hk9 : k ≤ 9 := le_of_pow_dvd_of_not (j := 9) hk (by decide)
    calc 2 ^ (3 * k) ≤ 2 ^ (3 * 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < Nat.factorial 12 / 2 := by decide
  · have hk9 : k ≤ 9 := le_of_pow_dvd_of_not (j := 9) hk (by decide)
    calc 2 ^ (3 * k) ≤ 2 ^ (3 * 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < Nat.factorial 13 / 2 := by decide
  · have hk10 : k ≤ 10 := le_of_pow_dvd_of_not (j := 10) hk (by decide)
    calc 2 ^ (3 * k) ≤ 2 ^ (3 * 10) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < Nat.factorial 14 / 2 := by decide
  · have hdvd := two_pow_succ_dvd_factorial (by omega) hk
    have hlt : k + 1 < n := by
      by_contra hc
      exact two_pow_not_dvd_factorial (by omega : n ≠ 0)
        ((pow_dvd_pow 2 (by omega : n ≤ k + 1)).trans hdvd)
    calc 2 ^ (3 * k) ≤ 2 ^ (3 * (n - 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < n.factorial / 2 := pow_lt_factorial_half n h15

theorem card_of_small (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h : (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) :
    Nat.card G = 168 ∨ Nat.card G = 6048 := by
  obtain ⟨x, hv⟩ := d
  rcases h with ⟨q, hq7, hx⟩ | ⟨q, hq3, hx⟩
  · obtain rfl : x = .A 1 q := hx
    have hL := CFSG.Models.lieModel_A 1 q hv e
    have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    have h7 : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq7
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hB, h7]
    exact Or.inl (by decide)
  · obtain rfl : x = .twistedA 2 q := hx
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 2 q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
    have hL := CFSG.Models.lieModel_twistedA 2 q hv e
    rw [hc, hf] at hL
    have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    have h3 : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq3
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hB, h3]
    exact Or.inr (by decide)

theorem altNotChevTwo_holds : AltNotChevTwo := by
  intro n hn h5 h6 h8 hC
  unfold IsChevTwo at hC
  have hcard : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 :=
    card_alt n (by omega)
  rcases hC with ⟨d, hd, ⟨e⟩⟩ | ⟨n', hn', ⟨e⟩⟩ | ⟨d, hsmall, ⟨e⟩⟩
  · have h1 : Char2Order (n.factorial / 2) := by
      rw [← hcard]
      exact char2Order_of_chev2 d hd _ e
    by_cases h9 : n = 9
    · subst h9
      have e9 : Nat.factorial 9 / 2 = 181440 := by decide
      rw [e9] at h1
      exact not_char2Order_181440 h1
    by_cases h10 : n = 10
    · subst h10
      have e10 : Nat.factorial 10 / 2 = 1814400 := by decide
      rw [e10] at h1
      exact not_char2Order_1814400 h1
    obtain ⟨k, hk, hb⟩ := char2Order_bound h1
    have hm := magnitude_lt n (by omega) h8 h9 h10 k hk
    omega
  · have hc := Nat.card_congr e.toEquiv
    rw [hcard, card_alt n' (by omega)] at hc
    have h2n : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have h2n' : 2 ∣ n'.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hm1 := Nat.mul_div_cancel' h2n
    have hm2 := Nat.mul_div_cancel' h2n'
    have hfac : n.factorial = n'.factorial := by omega
    have hnn : n = n' := (Nat.factorial_inj (by omega)).mp hfac
    omega
  · have hcases : n = 7 ∨ 9 ≤ n := by
      rcases Nat.lt_or_ge n 9 with h | h
      · interval_cases n
        · exact (h5 rfl).elim
        · exact (h6 rfl).elim
        · exact Or.inl rfl
        · exact (h8 rfl).elim
      · exact Or.inr h
    have hc := card_of_small d _ e hsmall
    rw [hcard] at hc
    rcases hcases with rfl | h9'
    · norm_num [Nat.factorial] at hc
    · have hle := Nat.factorial_le h9'
      have e9 : Nat.factorial 9 / 2 = 181440 := by decide
      omega

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
