module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix

variable {F : Type} [Field F]

theorem trace_mul_self_fin_two (X : Matrix (Fin 2) (Fin 2) F) :
    (X * X).trace = X.trace ^ 2 - 2 * X.det := by
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem mul_self_fin_two (X : Matrix (Fin 2) (Fin 2) F) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring

theorem one_add_pow_of_mul_self_eq_zero {R : Type*} [Ring R] {N : R} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + k • N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have h1 : (k • N) * N = 0 := by rw [smul_mul_assoc, hN, smul_zero]
    rw [add_mul, one_mul, mul_add, mul_one, h1, add_zero, succ_nsmul]
    abel

theorem false_of_conj_pow_two (h7 : (7 : F) ≠ 0) {x y : GL (Fin 2) F} (hx7 : x ^ 7 = 1)
    (hx1 : x ≠ 1) (hxy : y * x * y⁻¹ = x ^ 2) : False := by
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  have hdet : X.det = 1 := by
    have h := congrArg (fun g : GL (Fin 2) F => (Matrix.GeneralLinearGroup.det g : Fˣ)) hxy
    simp only [map_mul, map_inv, map_pow] at h
    have h' : Matrix.GeneralLinearGroup.det x = 1 := by
      rw [mul_comm (Matrix.GeneralLinearGroup.det y), mul_assoc, mul_inv_cancel, mul_one] at h
      have h2 : Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det x =
          Matrix.GeneralLinearGroup.det x * 1 := by rw [mul_one, ← pow_two]; exact h.symm
      exact mul_left_cancel h2
    have := congrArg (fun u : Fˣ => (u : F)) h'
    simpa [hX] using this
  have htr : X.trace = (X * X).trace := by
    have h := congrArg (fun g : GL (Fin 2) F => ((g : Matrix (Fin 2) (Fin 2) F)).trace) hxy
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_two] at h
    rw [← hX] at h
    rw [← h, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
  rw [trace_mul_self_fin_two, hdet] at htr
  have hfac : (X.trace - 2) * (X.trace + 1) = 0 := by linear_combination -htr
  have hsq := mul_self_fin_two X
  rw [hdet, one_smul] at hsq
  rcases mul_eq_zero.mp hfac with ht | ht
  ·
    have ht2 : X.trace = 2 := by linear_combination ht
    rw [ht2] at hsq
    set N : Matrix (Fin 2) (Fin 2) F := X - 1 with hN
    have hNN : N * N = 0 := by
      rw [hN, sub_mul, mul_sub, mul_one, one_mul, hsq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> ring
    have hX7 : X ^ 7 = 1 := by
      have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hx7
      simpa [hX] using this
    have hXN : X = 1 + N := by rw [hN]; abel
    rw [hXN, one_add_pow_of_mul_self_eq_zero hNN] at hX7
    have h7N : ((7 : ℕ) : F) • N = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact add_eq_left.mp hX7
    have hN0 : N = 0 := by
      rcases smul_eq_zero.mp h7N with h | h
      · exact absurd (by simpa using h) h7
      · exact h
    apply hx1
    refine Units.ext ?_
    rw [Units.val_one, ← hX, hXN, hN0, add_zero]
  ·
    have ht1 : X.trace = -1 := by linear_combination ht
    rw [ht1] at hsq
    have hX3 : X * X * X = 1 := by
      calc X * X * X = ((-1 : F) • X - (1 : Matrix (Fin 2) (Fin 2) F)) * X := by rw [hsq]
        _ = (-1 : F) • (X * X) - X := by rw [sub_mul, smul_mul_assoc, one_mul]
        _ = 1 := by
          rw [hsq, smul_sub, smul_smul]
          simp only [neg_mul, one_mul, neg_neg, one_smul, neg_smul, smul_neg]
          abel
    have hx3 : x ^ 3 = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one, ← hX, pow_succ, pow_two]
      exact hX3
    have h1 : orderOf x ∣ Nat.gcd 7 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx7) (orderOf_dvd_of_pow_eq_one hx3)
    have h2 : orderOf x = 1 := by
      have : Nat.gcd 7 3 = 1 := by norm_num
      rw [this] at h1
      exact Nat.dvd_one.mp h1
    exact hx1 (orderOf_eq_one_iff.mp h2)

theorem two_ne_zero_of_odd_card [Finite F] (hodd : ¬ 2 ∣ Nat.card F) : (2 : F) ≠ 0 := by
  intro h
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : ringChar F = 2 := by
    have : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp (by exact_mod_cast h)
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F _) Nat.prime_two).mp this
  have h3 := FiniteField.even_card_iff_char_two.mp h2
  exact hodd (by rw [Nat.card_eq_fintype_card]; exact Nat.dvd_of_mod_eq_zero h3)

theorem card_GL_two [Finite F] :
    Nat.card (GL (Fin 2) F) = (Nat.card F - 1) ^ 2 * (Nat.card F * (Nat.card F + 1)) := by
  classical
  have := Fintype.ofFinite F
  have hq' : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  rw [Matrix.card_GL_field, hq', Fin.prod_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 2 := by nlinarith
  zify [h1, h2, hq1.le]
  ring

theorem polarize (A B : Matrix (Fin 2) (Fin 2) F) :
    A * B + B * A = A.trace • B + B.trace • A +
      ((A * B).trace - A.trace * B.trace) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem mul_eq_trace_smul {e g : Matrix (Fin 2) (Fin 2) F} (hee : e * e = e) (htr : e.trace = 1)
    (hc : g * e = e * g) : e * g = (e * g).trace • e := by
  have hp := polarize e g
  rw [hc, htr, one_smul, one_mul] at hp
  have h3 : e * g + e * g = e * g + (e * g).trace • e := by
    have h2 := congrArg (fun M => e * M) hp
    simp only [mul_add, mul_smul_comm, mul_one, ← mul_assoc, hee] at h2
    rw [h2, add_assoc, ← add_smul]
    congr 2
    ring
  exact add_left_cancel h3

theorem trace_eq_one_of_idempotent {e : Matrix (Fin 2) (Fin 2) F} (hee : e * e = e) (h0 : e ≠ 0)
    (h1 : e ≠ 1) : e.trace = 1 := by
  have e00 := congrFun (congrFun hee 0) 0
  have e01 := congrFun (congrFun hee 0) 1
  have e10 := congrFun (congrFun hee 1) 0
  have e11 := congrFun (congrFun hee 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.trace_fin_two]
  by_cases hb : e 0 1 = 0
  · by_cases hc : e 1 0 = 0
    · rw [hb, hc] at e00 e11
      have ha : e 0 0 = 0 ∨ e 0 0 = 1 := by
        have : e 0 0 * (e 0 0 - 1) = 0 := by linear_combination e00
        rcases mul_eq_zero.mp this with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      have hd : e 1 1 = 0 ∨ e 1 1 = 1 := by
        have : e 1 1 * (e 1 1 - 1) = 0 := by linear_combination e11
        rcases mul_eq_zero.mp this with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.mp h)
      rcases ha with ha | ha <;> rcases hd with hd | hd
      · exact absurd (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]) h0
      · rw [ha, hd]; simp
      · rw [ha, hd]; simp
      · exact absurd (by ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]) h1
    · have : e 1 0 * (e 0 0 + e 1 1) = e 1 0 * 1 := by linear_combination e10
      exact mul_left_cancel₀ hc this
  · have : e 0 1 * (e 0 0 + e 1 1) = e 0 1 * 1 := by linear_combination e01
    exact mul_left_cancel₀ hb this

theorem exists_char_of_idempotent {T : Subgroup (GL (Fin 2) F)} {e : Matrix (Fin 2) (Fin 2) F}
    (hee : e * e = e) (htr : e.trace = 1)
    (hc : ∀ g ∈ T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e =
      e * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    ∃ χ : T →* Fˣ, ∀ g : T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e =
      ((χ g : Fˣ) : F) • e := by
  have he0 : e ≠ 0 := by
    intro h
    rw [h, Matrix.trace_zero] at htr
    exact zero_ne_one htr
  let lam : T → F := fun g => (e * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).trace
  have hlam : ∀ g : T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e = lam g • e := by
    intro g
    rw [hc g g.2]
    exact mul_eq_trace_smul hee htr (hc g g.2)
  have hmul : ∀ g h : T, lam (g * h) = lam g * lam h := by
    intro g h
    have e1 : (((g * h : T) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e =
        (lam g * lam h) • e := by
      rw [show (((g * h : T) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from by simp, mul_assoc, hlam h,
        mul_smul_comm, hlam g, smul_smul, mul_comm]
    rw [hlam (g * h)] at e1
    exact smul_left_injective F he0 e1
  have hone : lam 1 = 1 := by
    simp [lam, htr]
  have hne : ∀ g : T, lam g ≠ 0 := by
    intro g h0
    have := hmul g g⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  exact ⟨MonoidHom.mk' (fun g => Units.mk0 (lam g) (hne g)) (fun g h => Units.ext (hmul g h)),
    fun g => hlam g⟩

theorem card_dvd_of_commute_involution [Finite F] (h2 : (2 : F) ≠ 0)
    {Z : Matrix (Fin 2) (Fin 2) F} (hZ : Z * Z = 1) (h1 : Z ≠ 1) (hm1 : Z ≠ -1)
    {T : Subgroup (GL (Fin 2) F)}
    (hc : ∀ g ∈ T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Z =
      Z * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    Nat.card T ∣ (Nat.card F - 1) ^ 2 := by
  classical
  set e : Matrix (Fin 2) (Fin 2) F := (2 : F)⁻¹ • (1 + Z) with he
  set e' : Matrix (Fin 2) (Fin 2) F := (2 : F)⁻¹ • (1 - Z) with he'
  have h2inv : (2 : F)⁻¹ ≠ 0 := inv_ne_zero h2
  have hsum : e + e' = 1 := by
    rw [he, he', ← smul_add]
    have : (1 + Z) + (1 - Z) = (2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [two_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hee : e * e = e := by
    have h1' : (1 + Z) * (1 + Z) = (2 : F) • (1 + Z) := by
      have : (1 + Z) * (1 + Z) = 1 + Z + Z + Z * Z := by noncomm_ring
      rw [this, hZ, two_smul]; abel
    rw [he, smul_mul_smul_comm, h1', smul_smul]
    congr 1
    field_simp
  have hee' : e' * e' = e' := by
    have h1' : (1 - Z) * (1 - Z) = (2 : F) • (1 - Z) := by
      have : (1 - Z) * (1 - Z) = 1 - Z - Z + Z * Z := by noncomm_ring
      rw [this, hZ, two_smul]; abel
    rw [he', smul_mul_smul_comm, h1', smul_smul]
    congr 1
    field_simp
  have h2e : (2 : F) • e = 1 + Z := by rw [he, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have h2e' : (2 : F) • e' = 1 - Z := by rw [he', smul_smul, mul_inv_cancel₀ h2, one_smul]
  have he0 : e ≠ 0 := by
    intro h
    apply hm1
    rw [h, smul_zero] at h2e
    exact eq_neg_of_add_eq_zero_right h2e.symm
  have he1 : e ≠ 1 := by
    intro h
    apply h1
    rw [h, two_smul] at h2e
    exact (add_left_cancel h2e).symm
  have he'0 : e' ≠ 0 := by
    intro h
    apply h1
    rw [h, smul_zero] at h2e'
    exact (sub_eq_zero.mp h2e'.symm).symm
  have he'1 : e' ≠ 1 := by
    intro h
    apply hm1
    rw [h, two_smul] at h2e'
    have h3 : (1 : Matrix (Fin 2) (Fin 2) F) + 1 = 1 + -Z := by rw [h2e', sub_eq_add_neg]
    exact (neg_eq_iff_eq_neg.mp (add_left_cancel h3).symm)
  have htr := trace_eq_one_of_idempotent hee he0 he1
  have htr' := trace_eq_one_of_idempotent hee' he'0 he'1
  have hce : ∀ g ∈ T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e =
      e * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro g hg
    rw [he, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hc g hg]
  have hce' : ∀ g ∈ T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e' =
      e' * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro g hg
    rw [he', mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hc g hg]
  obtain ⟨χ, hχ⟩ := exists_char_of_idempotent hee htr hce
  obtain ⟨χ', hχ'⟩ := exists_char_of_idempotent hee' htr' hce'
  have hinj : Function.Injective (χ.prod χ') := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg1 : χ g = 1 := congrArg Prod.fst hg
    have hg2 : χ' g = 1 := congrArg Prod.snd hg
    have hgm : ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      calc ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (e + e') := by rw [hsum, mul_one]
        _ = ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e +
            ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * e' := mul_add _ _ _
        _ = ((χ g : Fˣ) : F) • e + ((χ' g : Fˣ) : F) • e' := by rw [hχ g, hχ' g]
        _ = e + e' := by rw [hg1, hg2]; simp
        _ = 1 := hsum
    exact Subtype.ext (Units.ext hgm)
  have h8 := Subgroup.card_dvd_of_injective (χ.prod χ') hinj
  rw [Nat.card_prod, Nat.card_units, ← pow_two] at h8
  exact h8

theorem eq_one_or_neg_one_of_odd_index [Finite F] (h2 : (2 : F) ≠ 0)
    {T : Subgroup (GL (Fin 2) F)} (hT : ¬ 2 ∣ T.index) {Z : Matrix (Fin 2) (Fin 2) F}
    (hZ : Z * Z = 1)
    (hc : ∀ g ∈ T, ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Z =
      Z * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    Z = 1 ∨ Z = -1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hm⟩ := card_dvd_of_commute_involution h2 hZ hcon.1 hcon.2 hc
  have hmi := Subgroup.card_mul_index T
  rw [card_GL_two, hm, mul_assoc] at hmi
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hidx : T.index = m * (Nat.card F * (Nat.card F + 1)) :=
    Nat.eq_of_mul_eq_mul_left hpos hmi
  apply hT
  rw [hidx]
  exact Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.even_mul_succ_self _)) _

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
