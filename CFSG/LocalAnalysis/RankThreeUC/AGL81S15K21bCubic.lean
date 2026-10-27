module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21bCubicProof

theorem blk_mul {F : Type} [Field F] (t p q r s : F) (hr : r = p + t * q)
    (hs : s = q + t * r) :
    !![p, q, 0; q, r, 0; 0, 0, 1] * !![0, 1, 0; 1, t, 0; 0, 0, 1] =
      !![q, r, 0; r, s, 0; 0, 0, 1] := by
  subst hs
  subst hr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem blk_pow_step {F : Type} [Field F] (t : F) (k : ℕ) (p q r s : F)
    (hpow : !![0, 1, 0; 1, t, 0; 0, 0, 1] ^ k = !![p, q, 0; q, r, 0; 0, 0, 1])
    (hr : r = p + t * q) (hs : s = q + t * r) :
    !![0, 1, 0; 1, t, 0; 0, 0, 1] ^ (k + 1) = !![q, r, 0; r, s, 0; 0, 0, 1] := by
  rw [pow_succ, hpow]
  exact blk_mul t p q r s hr hs

theorem inv_cubic_root {F : Type} [Field F] {t u : F} (htu : t * u = 1)
    (hB : t ^ 3 + t ^ 2 + 1 = 0) : u ^ 3 + u + 1 = 0 := by
  linear_combination u ^ 3 * hB + (-(t ^ 2 * u ^ 2 + t * u + 1) - u * (t * u + 1)) * htu

end K21bCubicProof

theorem exists_root_cubic_of_card_eight (F : Type) [Field F] [Finite F] (hF : Nat.card F = 8) :
    (2 : F) = 0 ∧ ∃ t : F, t ^ 3 + t + 1 = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have h8 : ringChar F ^ (n : ℕ) = 8 := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hF]
  have hdvd8 : ringChar F ∣ 8 := by
    rw [← h8]
    exact dvd_pow_self _ (PNat.ne_zero n)
  have hdvd : ringChar F ∣ 2 ^ 3 := by
    simpa using hdvd8
  have hchar : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  have h2F : (2 : F) = 0 := by
    have h := CharP.cast_eq_zero F (ringChar F)
    rw [hchar] at h
    simpa using h
  refine ⟨h2F, ?_⟩
  have hex : ∃ t₀ : F, t₀ ≠ 0 ∧ t₀ ≠ 1 := by
    by_contra hcon
    have hcon' : ∀ x : F, x ≠ 0 → x = 1 := fun x hx => by
      by_contra h1
      exact hcon ⟨x, hx, h1⟩
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro x _
      by_cases hx : x = 0
      · simp [hx]
      · simp [hcon' x hx]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at hle
    have h2le : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨t₀, ht₀0, ht₀1⟩ := hex
  have h7 : t₀ ^ 7 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one t₀ ht₀0
    rw [← Nat.card_eq_fintype_card, hF] at h
    simpa using h
  have hfac : (t₀ - 1) * ((t₀ ^ 3 + t₀ + 1) * (t₀ ^ 3 + t₀ ^ 2 + 1)) = 0 := by
    linear_combination h7 + (t₀ ^ 4 - t₀ ^ 3) * h2F
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) ht₀1
  · rcases mul_eq_zero.mp h with hA | hB
    · exact ⟨t₀, hA⟩
    · exact ⟨t₀⁻¹, K21bCubicProof.inv_cubic_root (mul_inv_cancel₀ ht₀0) hB⟩

theorem exists_orderOf_nine_sl3 (F : Type) [Field F] (h2 : (2 : F) = 0) {t : F}
    (ht : t ^ 3 + t + 1 = 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, orderOf g = 9 := by
  have hdet0 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det = -1 := by
    rw [Matrix.det_fin_three]
    simp
  have hdet : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [hdet0]
    linear_combination (-1 : F) * h2
  have e1 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 1 =
      !![0, 1, 0; 1, t, 0; 0, 0, 1] := pow_one _
  have e2 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 2 = _ :=
    K21bCubicProof.blk_pow_step t 1 0 1 t (t ^ 2 + 1) e1 (by ring) (by ring)
  have e3 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 3 = _ :=
    K21bCubicProof.blk_pow_step t 2 1 t (t ^ 2 + 1) (t + 1) e2 (by ring)
      (by linear_combination (-1 : F) * ht + h2)
  have e4 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 4 = _ :=
    K21bCubicProof.blk_pow_step t 3 t (t ^ 2 + 1) (t + 1) (t + 1) e3
      (by linear_combination (-1 : F) * ht + h2) (by linear_combination (-t ^ 2) * h2)
  have e5 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 5 = _ :=
    K21bCubicProof.blk_pow_step t 4 (t ^ 2 + 1) (t + 1) (t + 1) (t ^ 2 + 1) e4
      (by linear_combination (-t ^ 2) * h2) (by linear_combination (-t) * h2)
  have e6 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 6 = _ :=
    K21bCubicProof.blk_pow_step t 5 (t + 1) (t + 1) (t ^ 2 + 1) t e5
      (by linear_combination (-t) * h2) (by linear_combination (-1 : F) * ht)
  have e7 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 7 = _ :=
    K21bCubicProof.blk_pow_step t 6 (t + 1) (t ^ 2 + 1) t 1 e6
      (by linear_combination (-1 : F) * ht) (by linear_combination (-t ^ 2) * h2)
  have e8 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 8 = _ :=
    K21bCubicProof.blk_pow_step t 7 (t ^ 2 + 1) t 1 0 e7
      (by linear_combination (-t ^ 2) * h2) (by linear_combination (-t) * h2)
  have e9 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 9 = _ :=
    K21bCubicProof.blk_pow_step t 8 t 1 0 1 e8
      (by linear_combination (-t) * h2) (by ring)
  have hM9 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 9 = 1 := by
    rw [Matrix.one_fin_three]
    exact e9
  have hne3 : (!![0, 1, 0; 1, t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 3 ≠ 1 := by
    intro h
    have h01 := congrFun (congrFun (e3.symm.trans h) 0) 1
    rw [Matrix.one_apply_ne (show (0 : Fin 3) ≠ 1 by decide)] at h01
    have hent : t ^ 2 + 1 = 0 := by simpa using h01
    have h10 : (1 : F) = 0 := by linear_combination ht - t * hent
    exact one_ne_zero h10
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 3) F,
      (g : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, t, 0; 0, 0, 1] :=
    ⟨⟨!![0, 1, 0; 1, t, 0; 0, 0, 1], hdet⟩, rfl⟩
  refine ⟨g, ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnot : ¬ g ^ (3 ^ 1) = 1 := by
    intro h
    have h' : ((g ^ (3 ^ 1) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((1 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [h]
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hg] at h'
    exact hne3 h'
  have hfin : g ^ (3 ^ (1 + 1)) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hg]
    exact hM9
  exact (orderOf_eq_prime_pow hnot hfin).trans (by norm_num)

end CFSG.LocalAnalysis.RankThreeUC.S15
