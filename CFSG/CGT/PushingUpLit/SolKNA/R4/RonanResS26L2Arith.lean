module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

lemma val_two_of_dvd_two_mul_not_dvd {d u : ℕ} (hd0 : d ≠ 0) (hu0 : u ≠ 0)
    (hd : d ∣ 2 * u) (hnd : ¬ d ∣ u) :
    padicValNat 2 d = padicValNat 2 u + 1 := by
  have h2u : 2 * u ≠ 0 := mul_ne_zero two_ne_zero hu0
  have hle : d.factorization ≤ (2 * u).factorization :=
    (Nat.factorization_le_iff_dvd hd0 h2u).mpr hd
  rw [Nat.factorization_mul two_ne_zero hu0, Nat.Prime.factorization Nat.prime_two] at hle
  have hnle : ¬ d.factorization ≤ u.factorization := by
    rwa [Nat.factorization_le_iff_dvd hd0 hu0]
  have hp2 : d.factorization 2 ≤ 1 + u.factorization 2 := by
    have := hle 2
    simpa using this
  have hsame : ∀ p, p ≠ 2 → d.factorization p ≤ u.factorization p := by
    intro p hp
    have := hle p
    simpa [Finsupp.single_apply, hp, Ne.symm hp] using this
  have key : d.factorization 2 = u.factorization 2 + 1 := by
    by_contra hne
    apply hnle
    refine fun p => ?_
    by_cases hp : p = 2
    · subst hp
      omega
    · exact hsame p hp
  rwa [Nat.factorization_def d Nat.prime_two, Nat.factorization_def u Nat.prime_two] at key

lemma nat_core {r u w d : ℕ} (hr : 4 ≤ r) (hu : 2 ^ (r - 1) ∣ u) (hu0 : u ≠ 0)
    (hw : w = u + 2 ∨ u = w + 2) (hd0 : d ≠ 0) (hd : d ∣ 2 * u) (hnd : ¬ d ∣ u) :
    r ≤ padicValNat 2 (u * w) ∧ padicValNat 2 d = padicValNat 2 (u * w) := by
  have h4 : 4 ∣ u := by
    have h := (pow_dvd_pow 2 (show 2 ≤ r - 1 by omega)).trans hu
    simpa using h
  have hw0 : w ≠ 0 := by omega
  have hw4 : w % 4 = 2 := by omega
  have hw1 : padicValNat 2 w = 1 := by
    have hA : 2 ^ 1 ∣ w := by
      norm_num
      omega
    have hB : ¬ 2 ^ 2 ∣ w := by
      norm_num
      omega
    have hA' := (padicValNat_dvd_iff_le (p := 2) hw0).mp hA
    have hB' : ¬ 2 ≤ padicValNat 2 w := fun h => hB ((padicValNat_dvd_iff_le (p := 2) hw0).mpr h)
    omega
  have hu_val : r - 1 ≤ padicValNat 2 u := (padicValNat_dvd_iff_le (p := 2) hu0).mp hu
  have hmul : padicValNat 2 (u * w) = padicValNat 2 u + 1 := by
    rw [padicValNat.mul (p := 2) hu0 hw0, hw1]
  have hd_val : padicValNat 2 d = padicValNat 2 u + 1 :=
    val_two_of_dvd_two_mul_not_dvd hd0 hu0 hd hnd
  refine ⟨?_, by rw [hd_val, hmul]⟩
  rw [hmul]
  omega

theorem l2_nu_facts {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 4 ≤ r) {α γ : Kˣ} {ε q : ℕ}
    (hα : orderOf α = 2 ^ (r - 1)) (hε : ε ≤ 1) (hqq : q * q = Nat.card K) (hodd : Odd q)
    (h0 : ε = 0 → α ^ (q + 1) = 1 ∧ γ ^ (q + 1) = -1)
    (h1 : ε = 1 → 1 ≤ q ∧ α ^ (q - 1) = 1 ∧ γ ^ (q - 1) = -1) :
    r ≤ padicValNat 2 (Nat.card K - 1) ∧
    padicValNat 2 (orderOf γ) = padicValNat 2 (Nat.card K - 1) ∧
    ∃ δ : Kˣ, δ ^ 2 = α := by
  have hN1 : 1 < Nat.card K := Finite.one_lt_card
  have hNodd : Odd (Nat.card K) := by
    rw [← hqq]
    exact hodd.mul hodd
  have hNmod : Nat.card K % 2 = 1 := Nat.odd_iff.mp hNodd
  obtain ⟨k, hk⟩ := hodd
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · interval_cases q <;> omega
    · exact h
  have hsq : Nat.card K - 1 = (q + 1) * (q - 1) := by
    rw [← hqq]
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    have e : (m + 1) * (m + 1) = (m + 1 + 1) * (m + 1 - 1) + 1 := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e]
    simp
  obtain ⟨u, w, hNu, hw, hαu, hγu, hu0⟩ :
      ∃ u w : ℕ, Nat.card K - 1 = u * w ∧ (w = u + 2 ∨ u = w + 2) ∧ α ^ u = 1 ∧
        γ ^ u = -1 ∧ u ≠ 0 := by
    rcases (show ε = 0 ∨ ε = 1 by omega) with h | h
    · obtain ⟨hα', hγ'⟩ := h0 h
      exact ⟨q + 1, q - 1, hsq, Or.inr (by omega), hα', hγ', by omega⟩
    · obtain ⟨-, hα', hγ'⟩ := h1 h
      exact ⟨q - 1, q + 1, by rw [hsq, mul_comm], Or.inl (by omega), hα', hγ', by omega⟩
  have hu2 : 2 ^ (r - 1) ∣ u := by
    have h := orderOf_dvd_of_pow_eq_one hαu
    rwa [hα] at h
  have h4 : 4 ∣ u := by
    have h := (pow_dvd_pow 2 (show 2 ≤ r - 1 by omega)).trans hu2
    simpa using h
  have hw2 : 2 ∣ w := by omega
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hF : ringChar K ≠ 2 := by
    intro h
    have h' := FiniteField.even_card_iff_char_two.mp h
    rw [hcard] at h'
    omega
  have hd : orderOf γ ∣ 2 * u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul', hγu]
    norm_num
  have hnd : ¬ orderOf γ ∣ u := by
    intro h
    rw [orderOf_dvd_iff_pow_eq_one, hγu] at h
    have h' : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h'
    exact Ring.neg_one_ne_one_of_char_ne_two hF h'
  have hd0 : orderOf γ ≠ 0 := by
    intro h0'
    rw [h0', zero_dvd_iff] at hd
    omega
  obtain ⟨hA, hB⟩ := nat_core hr hu2 hu0 hw hd0 hd hnd
  have hαpow : α ^ (Fintype.card K / 2) = 1 := by
    have hhalf : Fintype.card K / 2 = u * (w / 2) := by
      rw [hcard, ← Nat.mul_div_assoc u hw2]
      have hX : 2 ∣ u * w := Dvd.dvd.mul_left hw2 u
      omega
    rw [hhalf]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hα]
    exact dvd_mul_of_dvd_left hu2 _
  obtain ⟨δ, hδ⟩ := (FiniteField.unit_isSquare_iff hF α).mpr hαpow
  rw [hNu]
  refine ⟨hA, hB, δ, ?_⟩
  rw [hδ, pow_two]

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
