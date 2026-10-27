module

public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74.GLS

theorem nb_not_dvd_orders {q r : ℕ} (hq : 1 ≤ q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ q ^ 2 + 1) :
    ¬ r ∣ q * (q ^ 2 - 1) ∧ ¬ r ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∧
      ¬ r ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  have hsq : q ^ 2 + 1 = (q + 1) * (q - 1) + 2 := by zify [hq]; ring
  have h0 : ¬ r ∣ q := fun h =>
    hr.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_pow h two_ne_zero)).1 hrq))
  have h1 : ¬ r ∣ q ^ 2 - 1 := fun h => by
    have key : q ^ 2 + 1 = (q ^ 2 - 1) + 2 := by
      have := Nat.one_le_pow 2 q hq
      omega
    exact h2 ((Nat.dvd_add_right h).1 (key ▸ hrq))
  have h3 : ¬ r ∣ q ^ 3 - 1 := fun h => by
    have key : q ^ 3 - 1 + (q + 1) = q * (q ^ 2 + 1) := by
      zify [Nat.one_le_pow 3 q hq]
      ring
    have h4 : r ∣ q + 1 := (Nat.dvd_add_right h).1 (key ▸ hrq.mul_left q)
    rw [hsq] at hrq
    exact h2 ((Nat.dvd_add_right (h4.mul_right _)).1 hrq)
  have h4 : ¬ r ∣ q ^ 3 + 1 := fun h => by
    have key : q ^ 3 + 1 + (q - 1) = q * (q ^ 2 + 1) := by zify [hq]; ring
    have h5 : r ∣ q - 1 := (Nat.dvd_add_right h).1 (key ▸ hrq.mul_left q)
    rw [hsq] at hrq
    exact h2 ((Nat.dvd_add_right (h5.mul_left _)).1 hrq)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    exacts [h0 h, h1 h]
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      exacts [h0 (hr.dvd_of_dvd_pow h), h1 h]
    · exact h3 h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      exacts [h0 (hr.dvd_of_dvd_pow h), h1 h]
    · exact h4 h

theorem nb_not_dvd_card_of_isLnEps3 {J : Type} [Group J] [Finite J] {p n : ℕ} (hp : p.Prime)
    {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) (hJ : IVK.IsLnEps 3 J δ (p ^ n)) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrq : r ∣ (p ^ n) ^ 2 + 1) : ¬ r ∣ Nat.card J := by
  obtain ⟨-, hL, hU⟩ := nb_not_dvd_orders (Nat.one_le_pow n p hp.pos) hr hr2 hrq
  intro hdvd
  rcases hδ with rfl | rfl
  · rcases hJ with ⟨-, F, _, _, hF, ⟨e⟩⟩ | ⟨h, -⟩
    · have hc := IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F)
      rw [show Nat.card F = p ^ n from hF] at hc
      rw [Nat.card_congr e.toEquiv] at hdvd
      exact hL (by rw [← hc]; exact hdvd.mul_right _)
    · norm_num at h
  · rcases hJ with ⟨h, -⟩ | ⟨-, F, _, _, hF, ⟨e⟩⟩
    · norm_num at h
    · have hF' : Nat.card F = (p ^ n) ^ 2 := hF
      have hn : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have := Finite.one_lt_card (α := F)
          rw [pow_zero, one_pow] at hF'
          omega
        · exact hn
      have hc := IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul
        (show LocalAnalysis.ComponentInitial.UnitaryFieldData p n F from
          ⟨hp, hn, by rw [hF', ← pow_mul, mul_comm]⟩)
      rw [Nat.card_congr e.toEquiv] at hdvd
      exact hU (by rw [← hc]; exact hdvd.mul_right _)

theorem nb_not_dvd_card_sl2 {K : Type} [Group K] {p n : ℕ} (hp : p.Prime)
    (hK : HasSL2Model K (fun r => r = p ^ n)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : r ∣ (p ^ n) ^ 2 + 1) : ¬ r ∣ Nat.card K := by
  obtain ⟨hq, -, -⟩ := nb_not_dvd_orders (Nat.one_le_pow n p hp.pos) hr hr2 hrq
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK
  rw [Nat.card_congr (e.toEquiv.trans
      (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm.toEquiv),
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, show Nat.card F = p ^ n from hF]
  exact hq

theorem nb_q_prime_pow {K : Type} [Group K] {q : ℕ} (hK : HasSL2Model K (fun r => r = q)) :
    ∃ p n : ℕ, p.Prime ∧ 1 ≤ n ∧ q = p ^ n := by
  obtain ⟨F, _, _, hF, -⟩ := hK
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, -, n, hp, hn⟩ := FiniteField.card' (K := F)
  exact ⟨p, n, hp, n.pos, by rw [← show Nat.card F = q from hF, Nat.card_eq_fintype_card, hn]⟩

end CFSG.GH74.Generic.S1.Exo
