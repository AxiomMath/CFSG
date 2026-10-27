module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupCof
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupGrow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpOrders

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.Assembly.LowTwoRank

theorem prime_dvd_alt10 {p : ℕ} (hp : p.Prime) (h : p ∣ 1814400) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  rw [show (1814400 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 ^ 2 * 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h7
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h5
    · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h3)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h5))))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h7)))

theorem lieModel_card_ne_alt9 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 181440 :=
  CFSG.ComponentClassification.SolMax.lieModel_card_ne_alt_nine hO hadm hX

theorem lieModel_card_ne_alt10 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 1814400 := by
  intro hc
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hE := lieSylowExponent_pos hadm
  obtain ⟨-, -, hfac⟩ := hO X t n p f hadm hX
  have hdvd : p ^ (lieSylowExponent t n * f) ∣ 1814400 := hc ▸ hfac ▸ Nat.ordProj_dvd _ _
  have hpd : p ∣ 1814400 :=
    (dvd_pow_self p (Nat.mul_ne_zero (by omega) (by omega))).trans hdvd
  rcases prime_dvd_alt10 hp hpd with rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 10) (by rw [hc]; decide)
    rw [hc] at hord
    rcases lie_casework hadm hb with
      ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, hf1, hf2⟩
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
        interval_cases n <;> interval_cases f <;> norm_num at hb <;> revert hord <;> decide
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
        simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
        revert hord <;> simp only [lieOrderNumerator, lieOrderDivisor] <;> decide

theorem card_eq_of_equiv_alt {Y : Type} [Group Y] {m : ℕ} (hm : 2 ≤ m)
    (e : Y ≃* alternatingGroup (Fin m)) : Nat.card Y = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 hm
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem dvd_factorial_div_two {m : ℕ} (hm : 9 ≤ m) : 181440 ∣ m.factorial / 2 := by
  have h : 2 * 181440 ∣ m.factorial := by
    have := Nat.factorial_dvd_factorial hm
    norm_num [Nat.factorial] at this ⊢
    exact this
  exact Nat.dvd_div_of_mul_dvd (by simpa [mul_comm] using h)

theorem dvd_card_of_isLargeAlt {Y : Type} [Group Y] (h : IsLargeAlt Y) :
    181440 ∣ Nat.card Y := by
  obtain ⟨m, hm, ⟨e⟩⟩ := h
  rw [card_eq_of_equiv_alt (by omega) e]
  exact dvd_factorial_div_two hm

theorem false_of_lieModel_alt (hO : LieOrderFormulasInput) {m : ℕ} (hm : 9 ≤ m) {Y : Type}
    [Group Y] (e : Y ≃* alternatingGroup (Fin m)) {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hY : Blueprint.LieModel Y t n p f) : False := by
  have hcard := card_eq_of_equiv_alt (by omega) e
  rcases Nat.lt_or_ge m 11 with hlt | hge
  · have h9 : m = 9 ∨ m = 10 := by omega
    rcases h9 with rfl | rfl
    · exact lieModel_card_ne_alt9 hO hadm hY (by rw [hcard]; norm_num [Nat.factorial])
    · exact lieModel_card_ne_alt10 hO hadm hY (by rw [hcard]; norm_num [Nat.factorial])
  · obtain ⟨-, hord, hfac⟩ := hO Y t n p f hadm hY
    have hd : 1 ≤ lieOrderDivisor t n (p ^ f) :=
      Nat.one_le_iff_ne_zero.2 (lieOrderDivisor_ne_zero hadm)
    have h1 : Nat.card Y ≤ (p ^ (lieSylowExponent t n * f)) ^ 3 := by
      calc Nat.card Y ≤ Nat.card Y * lieOrderDivisor t n (p ^ f) := Nat.le_mul_of_pos_right _ hd
        _ = lieOrderNumerator t n (p ^ f) := hord
        _ = (p ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (p ^ f) :=
            lieOrderNumerator_eq hadm
        _ ≤ (p ^ f) ^ lieSylowExponent t n * (p ^ f) ^ (2 * lieSylowExponent t n) :=
            Nat.mul_le_mul_left _ (lieOrderCofactor_le hadm)
        _ = (p ^ (lieSylowExponent t n * f)) ^ 3 := by
            rw [← pow_add, ← pow_mul, ← pow_mul]
            congr 1
            ring
    have hdvd : p ^ (lieSylowExponent t n * f) ∣ m.factorial / 2 := by
      rw [← hcard, ← hfac]
      exact Nat.ordProj_dvd _ _
    exact not_le_cube_of_pow_dvd hge hadm.1 hdvd (hcard ▸ h1)

theorem altNotLieType (hO : LieOrderFormulasInput) {m : ℕ} (hm : 9 ≤ m) :
    ¬ ∃ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f ∧
      Blueprint.LieModel (alternatingGroup (Fin m)) t n p f := by
  rintro ⟨t, n, p, f, hadm, hY⟩
  exact false_of_lieModel_alt hO hm (MulEquiv.refl _) hadm hY

theorem not_oddLieType_alt (hO : LieOrderFormulasInput) {m : ℕ} (hm : 9 ≤ m) :
    ¬ OddLieType (alternatingGroup (Fin m)) := by
  rintro ⟨t, n, p, f, -, -, hadm, hY⟩
  exact altNotLieType hO hm ⟨t, n, p, f, hadm, hY⟩

theorem not_evenLieType_alt (hO : LieOrderFormulasInput) {m : ℕ} (hm : 9 ≤ m) :
    ¬ EvenLieType (alternatingGroup (Fin m)) := by
  rintro ⟨t, n, f, hadm, hY⟩
  exact altNotLieType hO hm ⟨t, n, 2, f, hadm, hY⟩

end CFSG.OddStandard.AltStdSec
