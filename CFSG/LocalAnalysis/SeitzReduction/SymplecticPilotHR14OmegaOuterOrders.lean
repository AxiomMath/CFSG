module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)

section Ell

theorem exists_oddPrime_dvd_two_pow_add_one {g : ℕ} (hg : 1 ≤ g) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ℓ ∣ 2 ^ g + 1 := by
  have h1 : 2 ^ g + 1 ≠ 1 := by have := Nat.one_le_two_pow (n := g); omega
  have hp := Nat.minFac_prime h1
  refine ⟨_, hp, ?_, Nat.minFac_dvd _⟩
  rcases hp.eq_two_or_odd' with h2 | h2
  · exfalso
    have hd := Nat.minFac_dvd (2 ^ g + 1)
    rw [h2] at hd
    have : 2 ∣ 2 ^ g := dvd_pow_self 2 (by omega)
    omega
  · exact h2

variable {ℓ r : ℕ}

theorem dvd_pow_two_mul_sub_one (hℓ : ℓ ∣ r + 1) (i : ℕ) : ℓ ∣ r ^ (2 * i) - 1 := by
  have h1 : r + 1 ∣ r ^ 2 - 1 := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · exact ⟨r - 1, by
        rw [show r ^ 2 = r * r by ring]
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega⟩
  have h2 : r ^ 2 - 1 ∣ r ^ (2 * i) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (r ^ 2) 1 i
  exact hℓ.trans (h1.trans h2)

theorem not_dvd_pow_two_mul_add_one (hℓ : ℓ.Prime) (hℓo : Odd ℓ) (hℓr : ℓ ∣ r + 1) (hr : 1 ≤ r)
    (i : ℕ) : ¬ ℓ ∣ r ^ (2 * i) + 1 := by
  intro h
  have h1 := dvd_pow_two_mul_sub_one hℓr i
  have hpos : 1 ≤ r ^ (2 * i) := Nat.one_le_pow _ _ hr
  have h2 := Nat.dvd_sub h h1
  rw [show r ^ (2 * i) + 1 - (r ^ (2 * i) - 1) = 2 by omega] at h2
  have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
  rw [this] at hℓo
  exact absurd hℓo (by decide)

theorem dvd_pow_add_one_of_odd (hℓr : ℓ ∣ r + 1) {N : ℕ} (hN : Odd N) : ℓ ∣ r ^ N + 1 := by
  have := hN.nat_add_dvd_pow_add_pow r 1
  rw [one_pow] at this
  exact hℓr.trans this

theorem dvd_pow_sub_one_of_even (hℓr : ℓ ∣ r + 1) {N : ℕ} (hN : Even N) : ℓ ∣ r ^ N - 1 := by
  obtain ⟨M, rfl⟩ := hN
  rw [← two_mul]
  exact dvd_pow_two_mul_sub_one hℓr M

end Ell

section Orders

open CFSG.Open

theorem prod_pow_two_mul_sub_one_ne_zero {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (r ^ (2 * i) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 := (Finset.mem_Icc.1 hi).1
  have : 2 ≤ r ^ (2 * i) := by
    calc 2 ≤ r := hr
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (2 * i) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem odd_pow_two_pow_sub_one {g m : ℕ} (hg : 1 ≤ g) (hm : 1 ≤ m) : Odd ((2 ^ g) ^ m - 1) := by
  rw [← pow_mul]
  have h2 : 2 ∣ 2 ^ (g * m) := dvd_pow_self 2 (by positivity)
  have h1 : 1 ≤ 2 ^ (g * m) := Nat.one_le_two_pow
  obtain ⟨c, hc⟩ := h2
  refine ⟨c - 1, ?_⟩
  have : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · omega
    · exact h
  omega

theorem odd_pow_two_pow_add_one {g m : ℕ} (hg : 1 ≤ g) (hm : 1 ≤ m) : Odd ((2 ^ g) ^ m + 1) := by
  rw [← pow_mul]
  have h2 : 2 ∣ 2 ^ (g * m) := dvd_pow_self 2 (by positivity)
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by omega⟩

theorem gcd_four_of_odd {x : ℕ} (hx : Odd x) : Nat.gcd 4 x = 1 := by
  have : Nat.Coprime (2 ^ 2) x := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hx)
  simpa using this

theorem ordD_two_pow_eq {g N : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) :
    ordD N (2 ^ g) = (2 ^ g) ^ (N * (N - 1)) * ((2 ^ g) ^ N - 1) *
      ∏ i ∈ Finset.Icc 1 (N - 1), ((2 ^ g) ^ (2 * i) - 1) := by
  rw [ordD, gcd_four_of_odd (odd_pow_two_pow_sub_one hg hN), Nat.div_one]

theorem ordTwistedD_two_pow_eq {g N : ℕ} (hg : 1 ≤ g) (hN : 1 ≤ N) :
    ordTwistedD N (2 ^ g) = (2 ^ g) ^ (N * (N - 1)) * ((2 ^ g) ^ N + 1) *
      ∏ i ∈ Finset.Icc 1 (N - 1), ((2 ^ g) ^ (2 * i) - 1) := by
  rw [ordTwistedD, gcd_four_of_odd (odd_pow_two_pow_add_one hg hN), Nat.div_one]

variable {K : Type} [Field K] [Finite K]

theorem card_statedSp_eq_mul {r : ℕ} (hr : 1 ≤ r) (hK : Nat.card K = r ^ 2) (n : ℕ) :
    Nat.card (StatedSp n K) = r ^ (2 * n ^ 2) * ((∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) - 1)) *
      ∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) + 1)) := by
  rw [SymplecticFlag.card_statedSp, hK, ← pow_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 1 ≤ r ^ (2 * i) := Nat.one_le_pow _ _ (by omega)
  rw [← pow_mul, show 2 * (2 * i) = 2 * i + 2 * i by ring, pow_add]
  zify [h1, show 1 ≤ r ^ (2 * i) * r ^ (2 * i) from Nat.one_le_iff_ne_zero.2 (by positivity)]
  ring

theorem dvd_of_mul_dvd_card_statedSp {r A B n : ℕ} (hr : 2 ≤ r) (hK : Nat.card K = r ^ 2)
    (h : B * A * ∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) - 1) ∣ Nat.card (StatedSp n K)) :
    A ∣ r ^ (2 * n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) + 1) := by
  rw [card_statedSp_eq_mul (by omega) hK] at h
  have hX := Nat.pos_of_ne_zero (prod_pow_two_mul_sub_one_ne_zero hr n)
  refine Nat.dvd_of_mul_dvd_mul_right hX ?_
  have h1 : A * ∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) - 1) ∣
      B * A * ∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) - 1) :=
    Nat.mul_dvd_mul_right (Dvd.intro_left B rfl) _
  refine h1.trans (h.trans (dvd_of_eq ?_))
  ring

theorem not_dvd_card_statedSp_of_prime {r p A B n : ℕ} (hr : 2 ≤ r) (hK : Nat.card K = r ^ 2)
    (hp : p.Prime) (hpr : ¬ p ∣ r) (hpA : p ∣ A)
    (hpY : ∀ i ∈ Finset.Icc 1 n, ¬ p ∣ r ^ (2 * i) + 1) :
    ¬ B * A * ∏ i ∈ Finset.Icc 1 n, (r ^ (2 * i) - 1) ∣ Nat.card (StatedSp n K) := by
  intro h
  have h1 := hpA.trans (dvd_of_mul_dvd_card_statedSp hr hK h)
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact hpr (hp.dvd_of_dvd_pow h2)
  · obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h2
    exact hpY i hi hpi

theorem not_dvd_two_pow_of_odd {ℓ g : ℕ} (hℓ : ℓ.Prime) (hℓo : Odd ℓ) : ¬ ℓ ∣ 2 ^ g := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h)
  rw [this] at hℓo
  exact absurd hℓo (by decide)

theorem not_ordD_dvd_card_statedSp_of_even {N g : ℕ} (hN : 2 ≤ N) (hNe : Even N) (hg : 1 ≤ g)
    (hK : Nat.card K = 2 ^ (2 * g)) : ¬ Open.ordD N (2 ^ g) ∣ Nat.card (StatedSp (N - 1) K) := by
  have hK' : Nat.card K = (2 ^ g) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hr : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  obtain ⟨ℓ, hℓ, hℓo, hℓr⟩ := exists_oddPrime_dvd_two_pow_add_one hg
  rw [ordD_two_pow_eq hg (by omega)]
  exact not_dvd_card_statedSp_of_prime hr hK' hℓ (not_dvd_two_pow_of_odd hℓ hℓo)
    (dvd_pow_sub_one_of_even hℓr hNe)
    (fun i _ => not_dvd_pow_two_mul_add_one hℓ hℓo hℓr (by omega) i)

theorem not_ordTwistedD_dvd_card_statedSp_of_odd {N g : ℕ} (hNo : Odd N) (hg : 1 ≤ g)
    (hK : Nat.card K = 2 ^ (2 * g)) :
    ¬ Open.ordTwistedD N (2 ^ g) ∣ Nat.card (StatedSp (N - 1) K) := by
  have hK' : Nat.card K = (2 ^ g) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hr : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  obtain ⟨ℓ, hℓ, hℓo, hℓr⟩ := exists_oddPrime_dvd_two_pow_add_one hg
  rw [ordTwistedD_two_pow_eq hg (by obtain ⟨k, rfl⟩ := hNo; omega)]
  exact not_dvd_card_statedSp_of_prime hr hK' hℓ (not_dvd_two_pow_of_odd hℓ hℓo)
    (dvd_pow_add_one_of_odd hℓr hNo)
    (fun i _ => not_dvd_pow_two_mul_add_one hℓ hℓo hℓr (by omega) i)

theorem not_ordD_dvd_card_statedSp_of_odd {N g : ℕ} (hN : 5 ≤ N) (hNo : Odd N) (hg : 1 ≤ g)
    (hK : Nat.card K = 2 ^ (2 * g)) : ¬ Open.ordD N (2 ^ g) ∣ Nat.card (StatedSp (N - 1) K) := by
  have hK' : Nat.card K = (2 ^ g) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hr : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hk2 : 2 ≤ g * N := by nlinarith
  have hk6 : g * N ≠ 6 := by
    intro h6
    have hN6 : N ∣ 6 := ⟨g, by rw [← h6, mul_comm]⟩
    have := Nat.le_of_dvd (by norm_num) hN6
    interval_cases N <;> simp_all (config := { decide := true })
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
  have hk0 : 0 < g * N := by omega
  rw [ordD_two_pow_eq hg (by omega)]
  refine not_dvd_card_statedSp_of_prime hr hK' hp.prime ?_ (by rw [← pow_mul]; exact hp.dvd) ?_
  · intro h
    exact hp.ne_two hk0 ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1
      (hp.prime.dvd_of_dvd_pow h))
  · intro i hi h
    have hi' := Finset.mem_Icc.1 hi
    rw [← pow_mul] at h
    obtain ⟨h1, -⟩ := (hp.dvd_add_one_iff hk0 (g * (2 * i))).1 h
    have h2 : N ∣ 4 * i := by
      obtain ⟨c, hc⟩ := h1
      refine ⟨c, Nat.eq_of_mul_eq_mul_left (show 0 < g by omega) ?_⟩
      rw [show g * (4 * i) = 2 * (g * (2 * i)) by ring, hc]
      ring
    have h3 : N ∣ i := (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hNo)).dvd_of_dvd_mul_left
      (by simpa using h2)
    have := Nat.le_of_dvd (by omega) h3
    omega

end Orders

section LieModel

variable {K : Type} [Field K] [Finite K]

theorem not_card_dvd_card_statedSp_of_lieModel {Y : Type} [Group Y] {τ : StatedLieTag}
    {N g : ℕ} (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) (hN : 5 ≤ N) (hg : 1 ≤ g)
    (hY : LieModel Y τ N 2 g) (hK : Nat.card K = 2 ^ (2 * g))
    (hex : ¬ (τ = .POmegaMinus ∧ Even N)) :
    ¬ Nat.card Y ∣ Nat.card (StatedSp (N - 1) K) := by
  rcases hτ with rfl | rfl
  · rw [F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hY]
    change ¬ Open.ordD N (2 ^ g) ∣ _
    rcases Nat.even_or_odd N with hNe | hNo
    · exact not_ordD_dvd_card_statedSp_of_even (by omega) hNe hg hK
    · exact not_ordD_dvd_card_statedSp_of_odd hN hNo hg hK
  · rw [F4Pilot.card_eq_evenLieOrder_of_mem_classicalTags (by decide) hY]
    change ¬ Open.ordTwistedD N (2 ^ g) ∣ _
    rcases Nat.even_or_odd N with hNe | hNo
    · exact absurd ⟨rfl, hNe⟩ hex
    · exact not_ordTwistedD_dvd_card_statedSp_of_odd hNo hg hK

theorem not_injective_of_lieModel {Y : Type} [Group Y] {τ : StatedLieTag}
    {N g : ℕ} (hτ : τ = .POmegaPlus ∨ τ = .POmegaMinus) (hN : 5 ≤ N) (hg : 1 ≤ g)
    (hY : LieModel Y τ N 2 g) (hK : Nat.card K = 2 ^ (2 * g))
    (hex : ¬ (τ = .POmegaMinus ∧ Even N)) (φ : Y →* StatedSp (N - 1) K) :
    ¬ Function.Injective φ := by
  intro hφ
  apply not_card_dvd_card_statedSp_of_lieModel hτ hN hg hY hK hex
  exact Subgroup.card_dvd_of_injective φ hφ

end LieModel

end CFSG.SeitzReduction.SymplecticPilot
