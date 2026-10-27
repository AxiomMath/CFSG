module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpU4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem eq_of_lieModel_psl_two {Y : Type} [Group Y] {p f p' f' : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (h1 : Blueprint.LieModel Y .PSL 2 p (2 * f)) (h2 : Blueprint.LieModel Y .PSL 2 p' (2 * f')) :
    p = p' ∧ f = f' := by
  have c1 := card_of_lieModel_psl_two hp2 h1
  have c2 := card_of_lieModel_psl_two hp2' h2
  have hQ : Odd (p ^ (2 * f)) := (hp.odd_of_ne_two hp2).pow
  have hQ' : Odd (p' ^ (2 * f')) := (hp'.odd_of_ne_two hp2').pow
  have e : p ^ (2 * f) * ((p ^ (2 * f)) ^ 2 - 1) = p' ^ (2 * f') * ((p' ^ (2 * f')) ^ 2 - 1) := by
    rw [← two_mul_ordA_one hQ, ← two_mul_ordA_one hQ', ← c1, ← c2]
  have hmono : ∀ a b : ℕ, 0 < a → a < b → a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
    intro a b ha hab
    have h1a : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    have hsq : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
    calc a * (a ^ 2 - 1) ≤ b * (a ^ 2 - 1) := Nat.mul_le_mul_right _ hab.le
      _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hpos : 0 < p ^ (2 * f) := pow_pos hp.pos _
  have hpos' : 0 < p' ^ (2 * f') := pow_pos hp'.pos _
  have hQQ : p ^ (2 * f) = p' ^ (2 * f') := by
    rcases lt_trichotomy (p ^ (2 * f)) (p' ^ (2 * f')) with hlt | heq | hgt
    · exact absurd e (hmono _ _ hpos hlt).ne
    · exact heq
    · exact absurd e.symm (hmono _ _ hpos' hgt).ne
  have hpp : p = p' := by
    have hdvd : p ∣ p' ^ (2 * f') := hQQ ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp hp').1 (hp.dvd_of_dvd_pow hdvd)
  subst hpp
  have : 2 * f = 2 * f' := Nat.pow_right_injective hp.two_le hQQ
  exact ⟨rfl, by omega⟩

theorem cfRow516NoPSp : CFRow516NoPSp := by
  intro H _ _ h hrow hin p f hp hp2 hf hJ w hw hwW hw2 hτ
  obtain ⟨hZ, p', f', hp', hp2', hf', hJ', hK⟩ := inner_structure h hrow hin
  obtain ⟨rfl, rfl⟩ := eq_of_lieModel_psl_two hp' hp2' hf' hp hp2 hJ' hJ
  rcases hK with ⟨hq, F, _, _, hF, ⟨e⟩⟩ | ⟨hq, K', _, hUF, ⟨e⟩⟩
  · exact noPSp_L4 h hrow hin hp' hp2' hJ' hZ hq hF e w hw hwW hw2 hτ
  · exact noPSp_U4 h hrow hin hp' hp2' hJ' hZ hq hUF e w hw hwW hw2 hτ

end CFSG.ComponentClassification.CatFactsL4U4
