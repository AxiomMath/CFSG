module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.LieType.SeitzGeneration.ExtSeitzG2Odd
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.SEITZ3.EvenFromMax

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem not_sq_dvd_G2_nine {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ^ 2 ∣ 9 ^ 6 * (9 ^ 6 - 1) * (9 ^ 2 - 1) := by
  intro h
  have hpd : p ∣ 9 ^ 6 * (9 ^ 6 - 1) * (9 ^ 2 - 1) := (dvd_pow_self p two_ne_zero).trans h
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hd
  have hN : (9 ^ 6 * (9 ^ 6 - 1) * (9 ^ 2 - 1) : ℕ) = 2 ^ 8 * 3 ^ 12 * 5 ^ 2 * 7 * 13 * 73 := by
    norm_num
  rw [hN] at hpd h
  simp only [Nat.Prime.dvd_mul hp] at hpd
  rcases hpd with ((((h1 | h1) | h1) | h1) | h1) | h1
  · have := key 2 Nat.prime_two (hp.dvd_of_dvd_pow h1)
    omega
  · have := key 3 Nat.prime_three (hp.dvd_of_dvd_pow h1)
    omega
  · have := key 5 Nat.prime_five (hp.dvd_of_dvd_pow h1)
    omega
  · have := key 7 (by norm_num) h1
    subst this
    norm_num at h
  · have := key 13 (by norm_num) h1
    subst this
    norm_num at h
  · have := key 73 (by norm_num) h1
    subst this
    norm_num at h

theorem card_eq_nine_of_exponent_ne_one {q : PrimePower} (h2 : q.p ≠ 2) (he : q.exponent ≠ 1)
    (h11 : q.card < 11) : q.card = 9 := by
  have hp := q.prime_p
  have hpos := q.exponent_pos
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  rw [hcard] at h11 ⊢
  generalize q.p = r at *
  generalize q.exponent = n at *
  have hn2 : 2 ≤ n := by omega
  have hsq : r ^ 2 ≤ r ^ n := Nat.pow_le_pow_right hp.pos hn2
  have hr : r < 4 := by
    by_contra h
    have h4 : 4 ≤ r := Nat.not_lt.mp h
    nlinarith [hsq, h11, h4]
  have hr2 := hp.two_le
  interval_cases r
  · exact absurd rfl h2
  · have hn : n = 2 := by
      by_contra hne
      have h3 : 3 ≤ n := by omega
      have : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      omega
    rw [hn]
    norm_num

section Models


theorem extSeitzAtInnerFor_G2_nine {q : PrimePower} (hq9 : q.card = 9) :
    ExtSeitzAtInnerFor (.G2 q) fun p => 7 ≤ p := by
  intro K _ _ _ hnab hiso p hp hp5 hpd hp7 E hE hcard hinner
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, hX, ⟨e⟩⟩ := exists_adjointG2_model hiso
  have hX9 : Nat.card X = 9 := by rw [hX, ← PrimePower.card_def, hq9]
  have hK : Nat.card K = 9 ^ 6 * (9 ^ 6 - 1) * (9 ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact (exact_G2_finite_order X hX9).2.1
  have hinj := conj_injective_of_simple hnab
  obtain ⟨hE₀, hmap⟩ := inner_preimage_data (p := p) hinj E hinner
  have hcard₀ : Nat.card (E.comap (MulAut.conj : K →* MulAut K)) = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact hcard
  have hdvd : p ^ 2 ∣ Nat.card K := hcard₀ ▸ Subgroup.card_subgroup_dvd_card _
  rw [hK] at hdvd
  exact not_sq_dvd_G2_nine hp hp7 hdvd

theorem extSeitzAtInnerFor_G2_geFive (hmax : SEITZ3.MaxSL2SL2G2) {q : PrimePower} :
    ExtSeitzAtInnerFor (.G2 q) fun p => ¬ (p = 5 ∧ q.card = 9) := by
  have hsmall : ExtSeitzAtInnerFor (.G2 q) fun _ => q.p ≠ 2 ∧ q.exponent = 1 ∧ q.card < 11 :=
    fun K _ _ _ hnab hiso p hp hp5 hpd hP E hE hcard hin =>
      extSeitzAtInner_G2_odd_small hP.1 hP.2.1 hP.2.2 K hnab hiso p hp hp5 hpd E hE hcard hin
  refine extSeitzAtInnerFor_union (P₁ := fun p => p ∣ q.card - 1)
    (P₂ := fun p => (q.p = 2 ∧ ¬ p ∣ q.card - 1) ∨ (q.p ≠ 2 ∧ 11 ≤ q.card ∧ ¬ p ∣ q.card - 1) ∨
      (q.p ≠ 2 ∧ q.exponent = 1 ∧ q.card < 11) ∨ (q.card = 9 ∧ 7 ≤ p)) ?_
    extSeitzAtInnerFor_G2_split ?_
  · intro p hp hp5 hP
    by_cases h1 : p ∣ q.card - 1
    · exact Or.inl h1
    refine Or.inr ?_
    by_cases h2 : q.p = 2
    · exact Or.inl ⟨h2, h1⟩
    refine Or.inr ?_
    by_cases h11 : 11 ≤ q.card
    · exact Or.inl ⟨h2, h11, h1⟩
    refine Or.inr ?_
    by_cases he : q.exponent = 1
    · exact Or.inl ⟨h2, he, by omega⟩
    refine Or.inr ?_
    have h9 : q.card = 9 := card_eq_nine_of_exponent_ne_one h2 he (by omega)
    have hp6 : p ≠ 6 := by
      rintro rfl
      exact absurd hp (by norm_num)
    have hp5' : p ≠ 5 := fun h => hP ⟨h, h9⟩
    exact ⟨h9, by omega⟩
  · refine extSeitzAtInnerFor_union (P₁ := fun p => q.p = 2 ∧ ¬ p ∣ q.card - 1)
      (P₂ := fun p => (q.p ≠ 2 ∧ 11 ≤ q.card ∧ ¬ p ∣ q.card - 1) ∨
        (q.p ≠ 2 ∧ q.exponent = 1 ∧ q.card < 11) ∨ (q.card = 9 ∧ 7 ≤ p))
      (fun p _ _ h => h)
      (ExtSeitzAtInnerFor.of_cond fun h => SEITZ3.extSeitzAtInnerFor_G2_even hmax h) ?_
    refine extSeitzAtInnerFor_union (P₁ := fun p => q.p ≠ 2 ∧ 11 ≤ q.card ∧ ¬ p ∣ q.card - 1)
      (P₂ := fun p => (q.p ≠ 2 ∧ q.exponent = 1 ∧ q.card < 11) ∨ (q.card = 9 ∧ 7 ≤ p))
      (fun p _ _ h => h) ?_ ?_
    · exact ExtSeitzAtInnerFor.of_cond fun h => ExtSeitzAtInnerFor.of_cond fun h' =>
        extSeitzAtInnerFor_G2_oddQPlus h h'
    · exact extSeitzAtInnerFor_union (P₁ := fun _ => q.p ≠ 2 ∧ q.exponent = 1 ∧ q.card < 11)
        (P₂ := fun p => q.card = 9 ∧ 7 ≤ p) (fun p _ _ h => h) hsmall
        (ExtSeitzAtInnerFor.of_cond fun h => extSeitzAtInnerFor_G2_nine h)

end Models

section Assembly


theorem seitzExcAnisotropicForAt_G2_proved (hmax : SEITZ3.MaxSL2SL2G2) :
    SeitzExcAnisotropicForAt IsG2Index
      fun d p => ∃ q : PrimePower, d = .G2 q ∧ 5 ≤ p ∧ ¬ (p = 5 ∧ q.card = 9) :=
  seitzExcAnisotropicForAt_family (c := LieTypeIndex.G2)
    (P := fun q p => ¬ (p = 5 ∧ q.card = 9)) (fun _ hv => finite_isSimpleGroup_cat_G2 hv)
    fun _ => extSeitzAtInnerFor_G2_geFive hmax

@[expose] def SeitzExcAnisotropicG2NineFive : Prop :=
  SeitzExcAnisotropicForAt IsG2Index
    fun d p => p = 5 ∧ ∃ q : PrimePower, d = .G2 q ∧ q.card = 9

theorem seitzExcAnisotropicForAt_G2_geFive (hmax : SEITZ3.MaxSL2SL2G2)
    (hres : SeitzExcAnisotropicG2NineFive) :
    SeitzExcAnisotropicForAt IsG2Index PrimeRange.geFive :=
  SeitzExcAnisotropicForAt.of_cover (fun d p _ _ hG hQ => by
    obtain ⟨q, rfl⟩ := hG
    by_cases h : p = 5 ∧ q.card = 9
    · exact Or.inr ⟨h.1, q, rfl, h.2⟩
    · exact Or.inl ⟨q, rfl, hQ, h⟩) (seitzExcAnisotropicForAt_G2_proved hmax) hres

end Assembly

end CFSG.LieType.SeitzGeneration
