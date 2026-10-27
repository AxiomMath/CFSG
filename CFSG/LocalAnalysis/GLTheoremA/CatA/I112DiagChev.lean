module

public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem i112d_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem i112d_card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem i112d_card_m22 : Nat.card TauCeti.SporadicName.M22.Group = 443520 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h1 := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
  have h2 := CFSG.Sporadic.Bridge.M22.le_card_native
  rw [Nat.card_congr e.toEquiv] at h2
  omega

private theorem i112d_eq_of_sylow_mul_eq_seven {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n 2 f)
    (h : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f = 7) :
    t = .PSL ∧ n = 2 ∧ f = 7 := by
  have hf : 1 ≤ f := hadm.2.1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 7 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
      omega
    have hn5 : n ≤ 5 := by
      by_contra hlt
      have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    · exact ⟨rfl, rfl, by norm_num at h; omega⟩
    all_goals (norm_num at h; omega)
  case PSU =>
    obtain ⟨-, -, hn, hn3⟩ := hadm
    simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h
    have hN : n * (n - 1) / 2 ≤ 7 := by
      have := Nat.le_mul_of_pos_right (n * (n - 1) / 2) (show 0 < f by omega)
      omega
    have hn5 : n ≤ 5 := by
      by_contra hlt
      have : 6 * 5 ≤ n * (n - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    all_goals (norm_num at h; omega)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h
    have h4 : 4 ≤ n ^ 2 := by nlinarith
    have h7 : n ^ 2 ≤ 7 := by nlinarith
    have hn2 : n = 2 := by nlinarith
    subst hn2
    omega
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h
    have h12 : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    have := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    omega
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h
    have h12 : 12 ≤ n * (n - 1) := Nat.mul_le_mul (by omega : 4 ≤ n) (by omega : 3 ≤ n - 1)
    have := Nat.le_mul_of_pos_right (n * (n - 1)) (show 0 < f by omega)
    omega
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  all_goals simp only [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h; omega

private theorem i112d_two_pow_mod (n : ℕ) : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem i112d_two_pow_mod_nine_A (n : ℕ) :
    (2 ^ n % 9 = 4 ∨ 2 ^ n % 9 = 7) ↔ (n % 6 = 2 ∨ n % 6 = 4) := by
  rw [i112d_two_pow_mod n]
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = r at *
  interval_cases r <;> simp

theorem i112d_two_pow_mod_nine_U (n : ℕ) :
    (2 ^ n % 9 = 2 ∨ 2 ^ n % 9 = 5) ↔ (n % 6 = 1 ∨ n % 6 = 5) := by
  rw [i112d_two_pow_mod n]
  have h6 : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize n % 6 = r at *
  interval_cases r <;> simp

private theorem i112d_hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
  CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

theorem i112d_lie_or_card {S : Type} [Group S] (h : IsChevSimple 2 S) :
    (∃ (t : CFSG.Open.StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f) ∨
      Nat.card S = 360 ∨ Nat.card S = 6048 := by
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases h with h1 | he | hPSU
  · exact Or.inl h1
  · obtain ⟨e⟩ := he
    exact Or.inr (Or.inl ((Nat.card_congr e.toEquiv).trans i112d_card_alt_six))
  · refine Or.inr (Or.inr ?_)
    have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
    have h6 := (i112d_hO S .PSU 3 3 1 (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 from by
        decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) = 1 from rfl] at h6
    omega

theorem i112d_not_chev_alt7 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 7)) :
    ¬ IsChevSimple 2 S := by
  intro h
  have hc : Nat.card S = 2520 := (Nat.card_congr e.toEquiv).trans i112d_card_alt_seven
  rcases i112d_lie_or_card h with ⟨t, n, f, hX⟩ | h' | h'
  · exact CFSG.ComponentClassification.CatFC.not_lieModel_two_card_2520 i112d_hO hc
      (CFSG.Blueprint.LieModel.admissible hX) hX
  · omega
  · omega

theorem i112d_not_lieModel_two_card_443520 {Y : Type} [Group Y] (hcard : Nat.card Y = 443520)
    {t : CFSG.Open.StatedLieTag} {n f : ℕ} (hadm : CFSG.Open.StatedLieAdmissible t n 2 f)
    (hY : CFSG.Blueprint.LieModel Y t n 2 f) : False := by
  obtain ⟨-, hM, -⟩ := i112d_hO Y t n 2 f hadm hY
  rw [hcard] at hM
  have hT := CFSG.SeitzReduction.CrossChar.ordProj_two_eq_of_two hadm hM
  rw [show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num,
    CFSG.SeitzReduction.RankOne.LieOdd.ordProj_two_pow_mul_odd (by decide)] at hT
  have hNf : CFSG.ComponentClassification.CatLeaf.lieSylowExponent t n * f = 7 :=
    (Nat.pow_right_injective le_rfl hT).symm
  obtain ⟨rfl, rfl, rfl⟩ := i112d_eq_of_sylow_mul_eq_seven hadm hNf
  revert hM
  decide

theorem i112d_not_chev_m22 {S : Type} [Group S] (e : S ≃* TauCeti.SporadicName.M22.Group) :
    ¬ IsChevSimple 2 S := by
  intro h
  have hc : Nat.card S = 443520 := (Nat.card_congr e.toEquiv).trans i112d_card_m22
  rcases i112d_lie_or_card h with ⟨t, n, f, hX⟩ | h' | h'
  · exact i112d_not_lieModel_two_card_443520 hc (CFSG.Blueprint.LieModel.admissible hX) hX
  · omega
  · omega

theorem i112d_not_chev_of_odd_large {S : Type} [Group S] (hodd : CFSG.Blueprint.OddLieType S)
    (hbig : 25920 < Nat.card S) : ¬ IsChevSimple 2 S := by
  intro h
  rcases i112d_lie_or_card h with ⟨t', n', f', hX⟩ | h' | h'
  · have hadm := CFSG.Blueprint.LieModel.admissible hX
    have hcard := (i112d_hO S t' n' 2 f' hadm hX).2.1
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType i112d_hO hX hodd with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 from by
          decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 from rfl]
        at hcard
      omega
    · rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 from by
          decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 from rfl]
        at hcard
      omega
    · rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 from by
          decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 from rfl]
        at hcard
      omega
  · omega
  · omega

theorem i112d_chev_A2_char {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 Q).Valid) (hq : Q.card % 9 = 4 ∨ Q.card % 9 = 7)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 Q, hv⟩) (h : IsChevSimple 2 S) : Q.p = 2 := by
  by_contra hp2
  have hm := CFSG.Models.lieModel_A 2 Q hv e
  have hb : CFSG.Blueprint.LieModel S .PSL 3 Q.p Q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm
  have hodd : CFSG.Blueprint.OddLieType S := ⟨.PSL, 3, Q.p, Q.exponent, Q.prime_p, hp2, hm.1, hb⟩
  have hcard := (i112d_hO S .PSL 3 Q.p Q.exponent hm.1 hb).2.1
  have hqc : Q.card = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
  have hqodd : Odd (Q.p ^ Q.exponent) := (Q.prime_p.odd_of_ne_two hp2).pow
  rw [hqc] at hq
  generalize Q.p ^ Q.exponent = q at hcard hq hqodd
  have hq7 : 7 ≤ q := by
    rw [Nat.odd_iff] at hqodd
    omega
  have hdiv : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 q ≤ 3 :=
    Nat.gcd_le_left _ (by norm_num)
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 q =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by decide)]
    all_goals norm_num
  have hbig : 25920 < Nat.card S := by
    by_contra hle
    rw [not_lt] at hle
    have h1 := Nat.mul_le_mul hle hdiv
    rw [hcard, hnum] at h1
    have h3 : 7 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq7 3
    have h2 : 7 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq7 2
    have h4 : 343 * (48 * 342) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    omega
  exact i112d_not_chev_of_odd_large hodd hbig h

theorem i112d_chev_twistedA2_char {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid) (hq : Q.card % 9 = 2 ∨ Q.card % 9 = 5)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 Q, hv⟩) (h : IsChevSimple 2 S) :
    Q.p = 2 := by
  by_contra hp2
  have hm := CFSG.Models.lieModel_twistedA 2 Q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩ =
      Q.p := TauCeti.LieTypeIndex.characteristic_twistedA 2 Q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 Q, hv⟩ =
      Q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 2 Q
  rw [hc, hf] at hm
  have hb : CFSG.Blueprint.LieModel S .PSU 3 Q.p Q.exponent :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by decide) hm
  have hodd : CFSG.Blueprint.OddLieType S := ⟨.PSU, 3, Q.p, Q.exponent, Q.prime_p, hp2, hm.1, hb⟩
  have hcard := (i112d_hO S .PSU 3 Q.p Q.exponent hm.1 hb).2.1
  have hqc : Q.card = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
  have hqodd : Odd (Q.p ^ Q.exponent) := (Q.prime_p.odd_of_ne_two hp2).pow
  rw [hqc] at hq
  generalize Q.p ^ Q.exponent = q at hcard hq hqodd
  have hq5 : 5 ≤ q := by
    rw [Nat.odd_iff] at hqodd
    omega
  have hdiv : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 q ≤ 3 :=
    Nat.gcd_le_left _ (by norm_num)
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 q =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
    rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by decide)]
    all_goals norm_num
  have hbig : 25920 < Nat.card S := by
    by_contra hle
    rw [not_lt] at hle
    have h1 := Nat.mul_le_mul hle hdiv
    rw [hcard, hnum] at h1
    have h3 : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
    have h2 : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
    have h4 : 125 * (24 * 126) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    omega
  exact i112d_not_chev_of_odd_large hodd hbig h

end CFSG.LocalAnalysis.GLTheoremA
