module

public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks

public section

namespace CFSG.AGLEmbedding

open Polynomial Matrix CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary

variable {K : Type} [Field K] {n : ℕ}

theorem aeval_toLin'_X_pow_three_sub_one {a : GL (Fin n) K} (ha : a ^ 3 = 1) :
    aeval (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) (X ^ 3 - C (1 : K)) = 0 := by
  have h3 : (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) ^ 3 = 1 := by
    rw [← toLinAlgEquiv'_eq_toLin', ← map_pow, ← Units.val_pow_eq_pow_val, ha, Units.val_one,
      map_one]
  simp [h3]

theorem squarefree_minpoly_of_pow_three (h3 : (3 : K) ≠ 0) {a : GL (Fin n) K} (ha : a ^ 3 = 1) :
    Squarefree (minpoly K (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) := by
  have hsep : (X ^ 3 - C (1 : K)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast h3) one_ne_zero
  exact hsep.squarefree.squarefree_of_dvd (minpoly.dvd K _ (aeval_toLin'_X_pow_three_sub_one ha))

theorem natDegree_le_two_of_mem_primaryFactors {a : GL (Fin n) K} (ha : a ^ 3 = 1) {b : K[X]}
    (hb : b ∈ primaryFactors (Matrix.toLin' (a : Matrix (Fin n) (Fin n) K))) :
    b.natDegree ≤ 2 := by
  obtain ⟨hirr, -, hdvd⟩ := mem_primaryFactors.mp hb
  have h1 : b ∣ (X - C 1) * (X ^ 2 + X + 1) := by
    have h2 := hdvd.trans (minpoly.dvd K _ (aeval_toLin'_X_pow_three_sub_one ha))
    convert h2 using 1
    simp only [map_one]
    ring
  rcases hirr.prime.dvd_or_dvd h1 with h | h
  · have := natDegree_le_of_dvd h (X_sub_C_ne_zero 1)
    rw [natDegree_X_sub_C] at this
    omega
  · have hne : (X ^ 2 + X + 1 : K[X]) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [natDegree_zero] at this
      have h2 : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
      omega
    have := natDegree_le_of_dvd h hne
    have h2 : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
    omega

theorem card_efac (x : Module.End K (Fin n → K)) (b : primaryFactors x) :
    Nat.card (Efac x b) = Nat.card K ^ (b : K[X]).natDegree := by
  have hb0 : (b : K[X]) ≠ 0 := (irreducible_of_mem_primaryFactors b.2).ne_zero
  rw [Nat.card_congr (AdjoinRoot.powerBasis hb0).basis.equivFun.toEquiv, Nat.card_fun,
    Nat.card_fin, AdjoinRoot.powerBasis_dim]

theorem not_dvd_two_pow_mul_three_pow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b : ℕ) :
    ¬ p ∣ 2 ^ a * 3 ^ b := fun h => by
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega

theorem not_dvd_card_GL_of_small {E : Type*} [Field E] [Fintype E] {m p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hm : m = 0 ∨ (m = 1 ∧ Fintype.card E ≤ 4) ∨ (m = 2 ∧ Fintype.card E ≤ 3)) :
    ¬ p ∣ Nat.card (GL (Fin m) E) := by
  rw [Matrix.card_GL_field]
  have hq2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  rcases hm with rfl | ⟨rfl, hq⟩ | ⟨rfl, hq⟩
  · simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.dvd_one]
    exact hp.ne_one
  · simp only [Fin.prod_univ_one, Fin.val_zero, pow_zero, pow_one]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    interval_cases hc : Fintype.card E
    · exact not_dvd_two_pow_mul_three_pow hp hp5 1 1
    · exact not_dvd_two_pow_mul_three_pow hp hp5 4 1

theorem three_ne_zero_of_card_eq_two [Finite K] (hK : Nat.card K = 2) : (3 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
  have h3 : (3 : K) = 1 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (3 : K) = 2 + 1 := by norm_num
      _ = 1 := by rw [h2, zero_add]
  rw [h3]
  exact one_ne_zero

open scoped _root_.Classical in
theorem eq_one_of_mem_centralizer_of_card_eq_two [Finite K] (hK : Nat.card K = 2)
    {a g : GL (Fin n) K} (ha : a ^ 3 = 1)
    (hfree : ∀ Q : Subgroup (GL (Fin n) K), Q ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) →
      ⁅Q, Q⁆ = Q → Q = ⊥)
    (hg : g ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)))
    (hg6 : Nat.Coprime 6 (orderOf g)) : g = 1 := by
  set x := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K) with hxdef
  have hx := squarefree_minpoly_of_pow_three (three_ne_zero_of_card_eq_two hK) ha
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (orderOf_eq_one_iff.not.mpr hne)
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    by_contra h5
    have h6 : p ∣ 6 := by
      interval_cases p <;> first | decide | (exfalso; norm_num at hp)
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hg6 h6 hpg)
  have hhC : g ^ (orderOf g / p) ∈ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) :=
    Subgroup.pow_mem _ hg _
  have hh : orderOf (g ^ (orderOf g / p)) = p :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hpg
  rw [← range_commutantUnitsToGL_eq_centralizer (x := x) a rfl, ← range_blockTheta hx] at hhC
  obtain ⟨w, hw⟩ := hhC
  have hwp : orderOf w = p := by
    rw [← orderOf_injective (blockTheta hx) (blockTheta_injective hx) w, hw, hh]
  obtain ⟨b, hb⟩ : ∃ b, w b ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : w = 1 := funext hall
    rw [h1, orderOf_one] at hwp
    exact hp.one_lt.ne hwp
  have hbp : orderOf (w b) = p := by
    refine orderOf_eq_prime ?_ hb
    have h1 := congrFun (pow_orderOf_eq_one w) b
    rw [hwp] at h1
    simpa using h1
  have hdvd : p ∣ Nat.card (GL (Fin (mult x b)) (Efac x b)) :=
    hbp ▸ orderOf_dvd_natCard (w b)
  have hE := card_efac x b
  rw [hK] at hE
  have : Finite (Efac x b) := Nat.finite_of_card_ne_zero (by rw [hE]; positivity)
  have := Fintype.ofFinite (Efac x b)
  have hdeg := natDegree_le_two_of_mem_primaryFactors ha b.2
  by_cases hbig : 2 ≤ mult x b ∧ (3 ≤ mult x b ∨ ∃ s : Finset (Efac x b), s.card = 4)
  · have hQ : CFSG.IsQuasisimple (blockImage hx b) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx))
        (isQuasisimple_blockSL (E := Efac x) (m := mult x) b hbig.1 hbig.2)
    have hle : blockImage hx b ≤ Subgroup.centralizer ({a} : Set (GL (Fin n) K)) := by
      rw [← range_commutantUnitsToGL_eq_centralizer (x := x) a rfl]
      exact blockImage_le_range hx b
    have hbot := hfree _ hle (Subgroup.isPerfect_iff.mp hQ.1)
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    rw [hbot] at hnt
    exact not_nontrivial _ hnt
  · refine not_dvd_card_GL_of_small hp hp5 ?_ hdvd
    have hcard : Fintype.card (Efac x b) = 2 ^ (b : K[X]).natDegree := by
      rw [← Nat.card_eq_fintype_card, hE]
    have h4 : Fintype.card (Efac x b) ≤ 4 := by
      rw [hcard]
      calc 2 ^ (b : K[X]).natDegree ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hdeg
        _ = 4 := by norm_num
    rcases (show mult x b = 0 ∨ mult x b = 1 ∨ 2 ≤ mult x b by omega) with h0 | h1 | h2
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨h1, h4⟩)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · by_contra h3
        exact hbig ⟨h2, Or.inl (by omega)⟩
      · by_contra h3
        obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Efac x b))
          (n := 4) (by rw [Finset.card_univ]; omega)
        exact hbig ⟨h2, Or.inr ⟨t, ht⟩⟩

end CFSG.AGLEmbedding
