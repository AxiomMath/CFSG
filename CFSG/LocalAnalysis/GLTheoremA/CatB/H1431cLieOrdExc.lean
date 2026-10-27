module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOrdFam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open Finset
open CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem lieSOrd_orderE6 {q : ℕ} (hq : IsPrimePow q) (hN : orderE6 q ∈ lieSOrdN) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q - 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 3 (q - 1) * orderE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := lieSOrd_gen_bound hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul hN
  omega

theorem lieSOrd_orderTwistedE6 {q : ℕ} (hq : IsPrimePow q) (hN : orderTwistedE6 q ∈ lieSOrdN) :
    False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 3 (q + 1) ∣ q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (add_one_dvd_sq_sub_one q (by omega))) _) _
  have hmul : Nat.gcd 3 (q + 1) * orderTwistedE6 q = q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) *
      (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderTwistedE6
    rw [show q ^ 36 * ((q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1)) = q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := lieSOrd_gen_bound hq (by norm_num)
    (coprime_of_dvd_add_one (Nat.gcd_dvd_right _ _)) hmul hN
  omega

theorem lieSOrd_orderE7 {q : ℕ} (hq : IsPrimePow q) (hN : orderE7 q ∈ lieSOrdN) : False := by
  have hq2 := hq.two_le
  have hGd : Nat.gcd 2 (q - 1) ∣ q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans
      (sub_one_dvd_sq_sub_one q)) _) _
  have hmul : Nat.gcd 2 (q - 1) * orderE7 q = q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) := by
    have := Nat.mul_div_cancel' hGd
    unfold orderE7
    rw [show q ^ 63 * ((q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1)) = q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
      (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1) by ring] at this ⊢
    exact this
  obtain ⟨-, he⟩ := lieSOrd_gen_bound hq (by norm_num)
    (coprime_of_dvd_sub_one hq2 (Nat.gcd_dvd_right _ _)) hmul hN
  omega

theorem lieSOrd_orderE8 {q : ℕ} (hq : IsPrimePow q) (hN : orderE8 q ∈ lieSOrdN) : False := by
  obtain ⟨-, he⟩ := lieSOrd_gen_bound' (e := 120) (R := (q ^ 30 - 1) * (q ^ 24 - 1) *
    (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)) hq
    (by norm_num) (by unfold orderE8; ring) hN
  omega

theorem lieSOrd_orderF4 {q : ℕ} (hq : IsPrimePow q) (hN : orderF4 q ∈ lieSOrdN) : False := by
  obtain ⟨-, he⟩ := lieSOrd_gen_bound' (e := 24) (R := (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderF4; ring) hN
  omega

theorem lieSOrd_orderG2 {q : ℕ} (hq : IsPrimePow q) (hN : orderG2 q ∈ lieSOrdN) : False := by
  obtain ⟨hq25, -⟩ := lieSOrd_gen_bound' (e := 6) (R := (q ^ 6 - 1) * (q ^ 2 - 1)) hq
    (by norm_num) (by unfold orderG2; ring) hN
  have grid : ∀ q ∈ lieSOrdQ, orderG2 q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid q hq25 hN

theorem lieSOrd_orderTrialityD4 {q : ℕ} (hq : IsPrimePow q) (hN : orderTrialityD4 q ∈ lieSOrdN) :
    False := by
  obtain ⟨hq25, -⟩ := lieSOrd_gen_bound' (e := 12) (R := (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1)) hq (by norm_num) (by unfold orderTrialityD4; ring) hN
  have grid : ∀ q ∈ lieSOrdQ, orderTrialityD4 q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid q hq25 hN

theorem lieSOrd_orderSuzuki {q : ℕ} (hq : IsPrimePow q) (hN : orderSuzuki q ∈ lieSOrdN) :
    False := by
  obtain ⟨hq25, -⟩ := lieSOrd_gen_bound' (e := 2) (R := (q ^ 2 + 1) * (q - 1)) hq
    (by norm_num) (by unfold orderSuzuki; ring) hN
  have grid : ∀ q ∈ lieSOrdQ, orderSuzuki q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid q hq25 hN

theorem lieSOrd_orderRee {q : ℕ} (hq : IsPrimePow q) (hN : orderRee q ∈ lieSOrdN) : False := by
  obtain ⟨hq25, -⟩ := lieSOrd_gen_bound' (e := 3) (R := (q ^ 3 + 1) * (q - 1)) hq
    (by norm_num) (by unfold orderRee; ring) hN
  have grid : ∀ q ∈ lieSOrdQ, orderRee q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid q hq25 hN

theorem lieSOrd_orderTwistedF4 {q : ℕ} (hq : IsPrimePow q) (hN : orderTwistedF4 q ∈ lieSOrdN) :
    False := by
  obtain ⟨hq25, -⟩ := lieSOrd_gen_bound' (e := 12) (R := (q ^ 6 + 1) * (q ^ 4 - 1) *
    (q ^ 3 + 1) * (q - 1)) hq (by norm_num) (by unfold orderTwistedF4; ring) hN
  have grid : ∀ q ∈ lieSOrdQ, orderTwistedF4 q ∉ lieSOrdN := by
    unfold lieSOrdQ lieSOrdN
    decide +kernel
  exact grid q hq25 hN

theorem lieSOrd_orderTits (hN : orderTits ∈ lieSOrdN) : False := by
  revert hN
  unfold orderTits lieSOrdN
  decide +kernel

theorem lieSOrd_p_eq {q : TauCeti.PrimePower} {r k : ℕ} (hr : r.Prime) (h : q.card = r ^ k) :
    q.p = r := by
  have h1 : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  rw [h] at h1
  exact lieSOrd_eq_of_dvd_pow q.prime_p hr h1

theorem lieSOrd_cases {e : TauCeti.LieTypeIndex} (he : e.Valid)
    (hN : lieOrderFormula e ∈ lieSOrdN) :
    (∃ q : TauCeti.PrimePower, e = .B 3 q ∧ q.card = 2 ∧ lieOrderFormula e = 1451520) ∨
    (∃ q : TauCeti.PrimePower, e = .A 1 q ∧ q.card = 729 ∧ lieOrderFormula e = 193709880) ∨
    (∃ q : TauCeti.PrimePower, e = .B 2 q ∧ q.card = 8 ∧ lieOrderFormula e = 1056706560) := by
  have hs : e.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q =>
    obtain ⟨rfl, hq, hv⟩ := lieSOrd_orderA hs.1 q.isPrimePow_card hN
    exact Or.inr (Or.inl ⟨q, rfl, hq, hv⟩)
  | twistedA n q => exact (lieSOrd_orderTwistedA hs.1 q.isPrimePow_card hN).elim
  | B n q =>
    obtain ⟨hn2, -⟩ := hs
    rcases lieSOrd_orderBC (by omega : 1 ≤ n) q.isPrimePow_card hN with
      ⟨rfl, hq, hv⟩ | ⟨rfl, hq, hv⟩ | ⟨rfl, hq, hv⟩
    · exact Or.inl ⟨q, rfl, hq, hv⟩
    · exact Or.inr (Or.inr ⟨q, rfl, hq, hv⟩)
    · omega
  | C n q =>
    obtain ⟨hn3, hp2⟩ := hs
    exfalso
    rcases lieSOrd_orderBC (by omega : 1 ≤ n) q.isPrimePow_card hN with
      ⟨rfl, hq, -⟩ | ⟨rfl, hq, -⟩ | ⟨rfl, hq, -⟩
    · exact hp2 (lieSOrd_p_eq Nat.prime_two (k := 1) (by rw [hq]; norm_num))
    · omega
    · omega
  | D n q => exact (lieSOrd_orderD hs q.isPrimePow_card hN).elim
  | twistedD n q => exact (lieSOrd_orderTwistedD hs q.isPrimePow_card hN).elim
  | E6 q => exact (lieSOrd_orderE6 q.isPrimePow_card hN).elim
  | E7 q => exact (lieSOrd_orderE7 q.isPrimePow_card hN).elim
  | E8 q => exact (lieSOrd_orderE8 q.isPrimePow_card hN).elim
  | F4 q => exact (lieSOrd_orderF4 q.isPrimePow_card hN).elim
  | G2 q => exact (lieSOrd_orderG2 q.isPrimePow_card hN).elim
  | twistedE6 q => exact (lieSOrd_orderTwistedE6 q.isPrimePow_card hN).elim
  | trialityD4 q => exact (lieSOrd_orderTrialityD4 q.isPrimePow_card hN).elim
  | suzuki m =>
    exact (lieSOrd_orderSuzuki (Nat.prime_two.isPrimePow.pow (by omega)) hN).elim
  | reeG2 m => exact (lieSOrd_orderRee (Nat.prime_three.isPrimePow.pow (by omega)) hN).elim
  | reeF4 m =>
    exact (lieSOrd_orderTwistedF4 (Nat.prime_two.isPrimePow.pow (by omega)) hN).elim
  | tits => exact (lieSOrd_orderTits hN).elim

theorem lieSOrd_not_alt {X : Type} {n : ℕ} (ψ : X ≃ alternatingGroup (Fin n))
    (hN : Nat.card X ∈ lieSOrdN) (h : n = 5 ∨ n = 6 ∨ n = 8) : False := by
  have hc := Nat.card_congr ψ
  revert hc hN
  rcases h with rfl | rfl | rfl <;>
  · intro hN hc
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    rw [hc] at hN
    revert hN
    unfold lieSOrdN
    decide +kernel

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
