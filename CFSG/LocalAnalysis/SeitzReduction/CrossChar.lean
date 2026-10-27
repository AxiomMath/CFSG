module

public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharOdd

public section

namespace CFSG.SeitzReduction.CrossChar

open Finset CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.RankOne.LieOdd

theorem exists_odd_mul_of_ordProj {q' T : ℕ} (hq : 3 ≤ q') (hodd : Odd q')
    (hT : ordProj[2] (q' - 1) * ordProj[2] (q' + 1) = 2 * T) :
    ∃ k, Odd k ∧ (q' - 1 = k * T ∨ q' + 1 = k * T) := by
  have hdecomp : ∀ x : ℕ, x ≠ 0 → ordProj[2] x = T → ∃ k, Odd k ∧ x = k * T := by
    intro x hx hxT
    refine ⟨x / ordProj[2] x, ?_, ?_⟩
    · exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hx)
    · rw [← hxT, mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  obtain ⟨c, rfl⟩ := hodd
  rw [show 2 * c + 1 - 1 = 2 * c by omega, show 2 * c + 1 + 1 = 2 * (c + 1) by ring] at hT ⊢
  rcases Nat.even_or_odd c with hc | hc
  · have h1 : ordProj[2] (2 * (c + 1)) = 2 := by
      rw [show 2 * (c + 1) = 2 ^ 1 * (c + 1) by ring, ordProj_two_pow_mul_odd hc.add_one, pow_one]
    rw [h1, mul_comm] at hT
    obtain ⟨k, hk, hx⟩ := hdecomp (2 * c) (by omega) (by omega)
    exact ⟨k, hk, Or.inl hx⟩
  · have h1 : ordProj[2] (2 * c) = 2 := by
      rw [show 2 * c = 2 ^ 1 * c by ring, ordProj_two_pow_mul_odd hc, pow_one]
    rw [h1] at hT
    obtain ⟨k, hk, hx⟩ := hdecomp (2 * (c + 1)) (by omega) (by omega)
    exact ⟨k, hk, Or.inr hx⟩

theorem card_eq_of_PSL_two_two {f M : ℕ} (hf : 1 ≤ f)
    (hM : M * lieOrderDivisor .PSL 2 (2 ^ f) = lieOrderNumerator .PSL 2 (2 ^ f)) :
    M = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hD : lieOrderDivisor .PSL 2 (2 ^ f) = 1 := by
    show Nat.gcd 2 (2 ^ f - 1) = 1
    have : Odd (2 ^ f - 1) := by
      have h2 : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact Nat.Even.sub_odd (by omega) this odd_one
    exact Nat.coprime_two_left.mpr this
  rw [hD, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator]

theorem two_mul_card_eq_of_PSL_two_odd {q' M : ℕ} (hq : 3 ≤ q') (hodd : Odd q')
    (hM : M * lieOrderDivisor .PSL 2 q' = lieOrderNumerator .PSL 2 q') :
    2 * M = q' * ((q' - 1) * (q' + 1)) := by
  have hD : lieOrderDivisor .PSL 2 q' = 2 := by
    show Nat.gcd 2 (q' - 1) = 2
    obtain ⟨c, rfl⟩ := hodd
    rw [show 2 * c + 1 - 1 = 2 * c by omega]
    exact Nat.gcd_mul_right_right c 2
  have hN : lieOrderNumerator .PSL 2 q' = q' * (q' ^ 2 - 1) := by simp [lieOrderNumerator]
  rw [hD, hN, mul_comm] at hM
  rw [hM, show q' ^ 2 - 1 = (q' - 1) * (q' + 1) by
    rw [show q' ^ 2 = q' * q' by ring]
    obtain ⟨y, rfl⟩ : ∃ y, q' = y + 1 := ⟨q' - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf; omega]

theorem eq_of_PSL_two_odd {t : StatedLieTag} {n f q' M : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) (hq5 : 5 ≤ q')
    (hodd : Odd q') (h2M : 2 * M = q' * ((q' - 1) * (q' + 1))) :
    (t = .PSL ∧ n = 2 ∧ f = 2 ∧ q' = 5) ∨ (t = .PSL ∧ n = 3 ∧ f = 1 ∧ q' = 7) := by
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hE2, hE3⟩ := lt_cube_of_two hadm hM
  have hT := ordProj_two_eq_of_two hadm hM
  have hM0 : M ≠ 0 := by
    rintro rfl
    have : q' * ((q' - 1) * (q' + 1)) ≠ 0 :=
      mul_ne_zero (by omega) (mul_ne_zero (by omega) (by omega))
    omega
  have h2T : ordProj[2] (q' - 1) * ordProj[2] (q' + 1) = 2 * ordProj[2] M := by
    have h : ordProj[2] (2 * M) = ordProj[2] (q' * ((q' - 1) * (q' + 1))) := by rw [h2M]
    rw [Nat.ordProj_mul 2 two_ne_zero hM0, Nat.ordProj_mul 2 (by omega)
      (mul_ne_zero (by omega) (by omega)), Nat.ordProj_mul 2 (by omega) (by omega),
      ordProj_two_of_odd hodd, one_mul,
      show ordProj[2] 2 = 2 by rw [Nat.Prime.factorization_self Nat.prime_two, pow_one]] at h
    exact h.symm
  obtain ⟨k, hk, hu⟩ := exists_odd_mul_of_ordProj (by omega) hodd h2T
  have hT1 : 1 ≤ ordProj[2] M := Nat.one_le_pow _ _ two_pos
  generalize ordProj[2] M = T at hE2 hE3 hT h2T hu hT1
  have hL2 : t = .PSL → n = 2 → T = 2 ^ f ∧ M = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rintro rfl rfl
    exact ⟨by rw [hT]; simp [lieSylowExponent], card_eq_of_PSL_two_two hf hM⟩
  have hL3 : t = .PSL → n = 3 → f = 1 → T = 8 ∧ M = 168 := by
    rintro rfl rfl rfl
    exact ⟨by rw [hT]; rfl, eq_of_mul_eq_mul (hM.trans (by decide)) (by decide)⟩
  rcases (by obtain ⟨j, rfl⟩ := hk; omega : k = 1 ∨ 3 ≤ k) with rfl | hk3
  · rw [one_mul] at hu
    rcases hu with hu | hu
    ·
      obtain rfl : q' = T + 1 := by omega
      by_cases h2 : t = .PSL ∧ n = 2
      · obtain ⟨hTq, hMq⟩ := hL2 h2.1 h2.2
        rw [← hTq] at hMq
        have key : T * (T + 1) * (2 * (T - 1)) = T * (T + 1) * (T + 2) := by
          have e1 : T ^ 2 - 1 = (T - 1) * (T + 1) := by
            rw [show T ^ 2 - 1 = T ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq, mul_comm]
          rw [hMq, e1, Nat.add_sub_cancel] at h2M
          linarith
        have hT4 : T = 4 := by
          have := Nat.eq_of_mul_eq_mul_left (by positivity) key
          omega
        have hf2 : f = 2 := by
          have h4 : (2 : ℕ) ^ f = 2 ^ 2 := by rw [← hTq, hT4]; norm_num
          exact Nat.pow_right_injective le_rfl h4
        exact Or.inl ⟨h2.1, h2.2, hf2, by omega⟩
      · by_cases h3 : t = .PSL ∧ n = 3 ∧ f = 1
        · obtain ⟨hT8, hM168⟩ := hL3 h3.1 h3.2.1 h3.2.2
          subst hT8 hM168
          norm_num at h2M
        · have h4 := hE3 h2 h3
          rw [Nat.add_sub_cancel] at h2M
          have : T ^ 3 ≤ 2 * ((T + 1) * (T * (T + 1 + 1))) := by nlinarith
          omega
    ·
      by_cases h2 : t = .PSL ∧ n = 2
      · obtain ⟨hTq, hMq⟩ := hL2 h2.1 h2.2
        rw [← hTq, ← hu] at hMq
        rw [hMq] at h2M
        have e1 : (q' + 1) ^ 2 - 1 = q' * (q' + 2) := by
          rw [show (q' + 1) ^ 2 = q' * (q' + 2) + 1 by ring, Nat.add_sub_cancel]
        rw [e1] at h2M
        have : q' * (q' + 1) * (q' - 1) < q' * (q' + 1) * (2 * (q' + 2)) :=
          Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
        nlinarith
      · by_cases h3 : t = .PSL ∧ n = 3 ∧ f = 1
        · exact Or.inr ⟨h3.1, h3.2.1, h3.2.2, by have := (hL3 h3.1 h3.2.1 h3.2.2).1; omega⟩
        · have h4 := hE3 h2 h3
          rw [← hu] at h4
          obtain ⟨y, rfl⟩ : ∃ y, q' = y + 5 := ⟨q' - 5, by omega⟩
          rw [show y + 5 - 1 = y + 4 by omega] at h2M
          nlinarith
  ·
    exfalso
    have h3T : 3 * T ≤ q' + 1 := by
      rcases hu with hu | hu
      · have := Nat.mul_le_mul_right T hk3; omega
      · have := Nat.mul_le_mul_right T hk3; omega
    have hT2 : T ≤ q' - 1 := by omega
    have hle : T * (T * (3 * T)) ≤ q' * ((q' - 1) * (q' + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul hT2 h3T)
    have e : T * (T * (3 * T)) = 3 * T ^ 3 := by ring
    omega

theorem crossChar_arith {t t' : StatedLieTag} {n n' f p g M : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hadm' : StatedLieAdmissible t' n' p g) (hp2 : p ≠ 2)
    (hM : M * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f))
    (hM' : M * lieOrderDivisor t' n' (p ^ g) = lieOrderNumerator t' n' (p ^ g)) :
    (t = .PSL ∧ n = 2 ∧ f = 2 ∧ t' = .PSL ∧ n' = 2 ∧ p ^ g = 5) ∨
      (t = .PSL ∧ n = 3 ∧ f = 1 ∧ t' = .PSL ∧ n' = 2 ∧ p ^ g = 7) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1 ∧ t' = .PSp ∧ n' = 2 ∧ p ^ g = 3) := by
  have hT := ordProj_two_eq_of_two hadm hM
  rcases ordProj_two_cube_le_of_odd hadm' hp2 hM' with hO | ⟨rfl, rfl⟩ | ⟨-, -, -, rfl⟩ |
      ⟨rfl, rfl, hq3, rfl⟩
  · exact absurd hO (not_le.mpr (lt_cube_of_two hadm hM).1)
  ·
    have hp : p.Prime := hadm'.1
    have hqodd : Odd (p ^ g) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨-, hg, -, -, hq3⟩ := hadm'
    have hq5 : 5 ≤ p ^ g := by
      have h3 : 3 ≤ p ^ g := by
        have := hp.two_le
        have : p ≤ p ^ g := Nat.le_self_pow (by omega) p
        have : p ≠ 2 := hp2
        omega
      have : p ^ g ≠ 3 := fun h => hq3 (by rw [h])
      obtain ⟨c, hc⟩ := hqodd
      omega
    rcases eq_of_PSL_two_odd hadm hM hq5 hqodd
        (two_mul_card_eq_of_PSL_two_odd (by omega) hqodd hM') with
      ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h2, h3, rfl, rfl, h4⟩
    · exact Or.inr (Or.inl ⟨h1, h2, h3, rfl, rfl, h4⟩)
  ·
    rw [show (6048 : ℕ) = 2 ^ 5 * 189 by norm_num, ordProj_two_pow_mul_odd (by decide)] at hT
    obtain ⟨rfl, rfl, rfl⟩ :=
      eq_of_sylow_mul_eq_five hadm (Nat.pow_right_injective le_rfl hT).symm
    exact absurd hM (by decide)
  ·
    rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num, ordProj_two_pow_mul_odd (by decide)] at hT
    rcases eq_of_sylow_mul_eq_six hadm (Nat.pow_right_injective le_rfl hT).symm with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩
    · exact absurd hM (by decide)
    · exact absurd hM (by decide)
    · exact absurd hM (by decide)
    · exact absurd hM (by decide)
    · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, hq3⟩)
    · exact absurd hM (by decide)

theorem eq_of_crossChar_arith {t t' : StatedLieTag} {n n' f q' : ℕ}
    (h : (t = .PSL ∧ n = 2 ∧ f = 2 ∧ t' = .PSL ∧ n' = 2 ∧ q' = 5) ∨
      (t = .PSL ∧ n = 3 ∧ f = 1 ∧ t' = .PSL ∧ n' = 2 ∧ q' = 7) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1 ∧ t' = .PSp ∧ n' = 2 ∧ q' = 3)) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) := by
  rcases h with ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩
  exacts [Or.inl ⟨h1, h2, h3⟩, Or.inr (Or.inl ⟨h1, h2, h3⟩), Or.inr (Or.inr ⟨h1, h2, h3⟩)]

theorem statedLieAdmissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem eq_of_lieModel_two_of_oddLieType (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hX : LieModel X t n 2 f) (hodd : OddLieType X) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) := by
  have hadm := statedLieAdmissible_of_lieModel hX
  obtain ⟨t', n', p, g, -, hp2, hadm', hY⟩ := hodd
  exact eq_of_crossChar_arith
    (crossChar_arith hadm hadm' hp2 (hO X t n 2 f hadm hX).2.1 (hO X t' n' p g hadm' hY).2.1)

theorem not_oddLieType_of_lieModel_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hX : LieModel X t n 2 f) (h1 : ¬ (t = .PSL ∧ n = 2 ∧ f = 2))
    (h2 : ¬ (t = .PSL ∧ n = 3 ∧ f = 1)) (h3 : ¬ (t = .PSU ∧ n = 4 ∧ f = 1)) : ¬ OddLieType X :=
  fun hodd => by
    rcases eq_of_lieModel_two_of_oddLieType hO hX hodd with h | h | h
    exacts [h1 h, h2 h, h3 h]

end CFSG.SeitzReduction.CrossChar
