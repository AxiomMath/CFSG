module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10Ord

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.X10
open Subgroup

@[expose] def NoPSL2Odd (L : Type) [Group L] : Prop :=
  ∀ p f : ℕ, p.Prime → 5 ≤ p ^ f → Odd (Nat.card (center L)) →
    ¬ LieModel (L ⧸ center L) .PSL 2 p f

theorem NoPSL2Odd.of_mulEquiv {L M : Type} [Group L] [Group M] (e : L ≃* M)
    (h : NoPSL2Odd M) : NoPSL2Odd L := by
  intro p f hp h5 hodd hL
  have hc : Nat.card (center M) = Nat.card (center L) :=
    (Nat.card_congr ((MulEquiv.subgroupCongr (Subgroup.map_center_eq e)).symm.trans
      ((center L).equivMapOfInjective e.toMonoidHom e.injective).symm).toEquiv)
  exact h p f hp h5 (hc ▸ hodd) (LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hL)

theorem card_mul_gcd_of_psl_two (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p ^ f) (hX : LieModel X .PSL 2 p f) :
    Nat.card X * Nat.gcd 2 (p ^ f - 1) = p ^ f * ((p ^ f) ^ 2 - 1) ∧
      (Nat.card X).factorization p = f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  have hadm : StatedLieAdmissible .PSL 2 p f :=
    ⟨hp, hf, le_rfl, fun h => by simp only [Prod.mk.injEq, true_and] at h; omega,
      fun h => by simp only [Prod.mk.injEq, true_and] at h; omega⟩
  obtain ⟨-, hc, hfac⟩ := hO X .PSL 2 p f hadm hX
  refine ⟨?_, ?_⟩
  · have hc' : Nat.card X * Nat.gcd 2 (p ^ f - 1) =
        (p ^ f) ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ f) ^ i - 1) := hc
    rw [Finset.Icc_self, Finset.prod_singleton] at hc'
    simpa using hc'
  · have hfac' : (Nat.card X).factorization p = 2 * (2 - 1) / 2 * f := hfac
    simpa using hfac'

theorem le_add_one_of_pow_dvd {r k s : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hs : 2 ≤ s)
    (h : r ^ k ∣ s * ((s - 1) * (s + 1))) : r ^ k ≤ s + 1 := by
  have hcop : ∀ {a : ℕ}, ¬ r ∣ a → Nat.Coprime (r ^ k) a := fun ha =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 ha)
  have h01 : ¬ (r ∣ s ∧ r ∣ s - 1) := fun ⟨h1, h2⟩ => by
    have := Nat.dvd_sub h1 h2
    rw [Nat.sub_sub_self (by omega)] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have h02 : ¬ (r ∣ s ∧ r ∣ s + 1) := fun ⟨h1, h2⟩ => by
    have := Nat.dvd_sub h2 h1
    rw [Nat.add_sub_cancel_left] at this
    exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have h12 : ¬ (r ∣ s - 1 ∧ r ∣ s + 1) := fun ⟨h1, h2⟩ => by
    have := Nat.dvd_sub h2 h1
    rw [show s + 1 - (s - 1) = 2 by omega] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
  by_cases hs0 : r ∣ s
  · have hd : r ^ k ∣ s := Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.mul_right (hcop fun h => h01 ⟨hs0, h⟩) (hcop fun h => h02 ⟨hs0, h⟩)) h
    exact (Nat.le_of_dvd (by omega) hd).trans (Nat.le_succ s)
  · have h' : r ^ k ∣ (s - 1) * (s + 1) := Nat.Coprime.dvd_of_dvd_mul_left (hcop hs0) h
    by_cases hs1 : r ∣ s - 1
    · have hd : r ^ k ∣ s - 1 :=
        Nat.Coprime.dvd_of_dvd_mul_right (hcop fun h => h12 ⟨hs1, h⟩) h'
      exact (Nat.le_of_dvd (by omega) hd).trans (by omega)
    · exact Nat.le_of_dvd (by omega) (Nat.Coprime.dvd_of_dvd_mul_left (hcop hs1) h')

theorem false_of_psl_two_of_cofactor_le (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ' : StatedLieTag} {n' r e p f N C : ℕ} (hr2 : r ≠ 2)
    (hadm' : StatedLieAdmissible τ' n' r e) (hX' : LieModel X τ' n' r e) (hp : p.Prime)
    (hX : LieModel X .PSL 2 p f) (h5 : 5 ≤ p ^ f) (hN : lieSylowExponent τ' n' = N)
    (hN2 : 2 ≤ N) (hC : lieOrderCofactor τ' n' (r ^ e) ≤ (r ^ e) ^ C) (hNC : C + 1 ≤ 2 * N) :
    False := by
  have hr : r.Prime := hadm'.1
  obtain ⟨hcX, -⟩ := card_mul_gcd_of_psl_two hO hp h5 hX
  obtain ⟨-, hc', hfac'⟩ := hO X τ' n' r e hadm' hX'
  rw [hN] at hfac'
  have hQ3 : 3 ≤ r ^ e := three_le_pow hr hr2 hadm'.2.1
  have hXle : Nat.card X ≤ (r ^ e) ^ N * (r ^ e) ^ C := by
    have hdiv := Nat.pos_of_ne_zero (lieOrderDivisor_ne_zero hadm')
    calc Nat.card X ≤ Nat.card X * lieOrderDivisor τ' n' (r ^ e) :=
          Nat.le_mul_of_pos_right _ hdiv
      _ = lieOrderNumerator τ' n' (r ^ e) := hc'
      _ = (r ^ e) ^ N * lieOrderCofactor τ' n' (r ^ e) := by
          rw [lieOrderNumerator_eq hadm', hN]
      _ ≤ (r ^ e) ^ N * (r ^ e) ^ C := Nat.mul_le_mul_left _ hC
  have h1 : r ^ (N * e) ∣ Nat.card X := hfac' ▸ Nat.ordProj_dvd (Nat.card X) r
  have hm' : r ^ (N * e) = (r ^ e) ^ N := by rw [← pow_mul, mul_comm e N]
  generalize hs : p ^ f = s at hcX h5
  generalize hQ : r ^ e = Q at hXle hQ3 hm'
  have hsq : s ^ 2 - 1 = (s - 1) * (s + 1) := by
    have h1 : 1 ≤ s := by omega
    zify [h1, Nat.one_le_pow 2 s h1]
    ring
  have hdvd : r ^ (N * e) ∣ s * ((s - 1) * (s + 1)) :=
    h1.trans ⟨Nat.gcd 2 (s - 1), by rw [hcX, hsq]⟩
  have hms : Q ^ N ≤ s + 1 := hm' ▸ le_add_one_of_pow_dvd hr hr2 (by omega) hdvd
  have hm9 : 9 ≤ Q ^ N := nine_le_pow hQ3 hN2
  have hm3 : 3 * Q ^ C ≤ (Q ^ N) ^ 2 := by
    calc 3 * Q ^ C ≤ Q * Q ^ C := Nat.mul_le_mul_right _ hQ3
      _ = Q ^ (C + 1) := (pow_succ' Q C).symm
      _ ≤ Q ^ (2 * N) := Nat.pow_le_pow_right (by omega) hNC
      _ = (Q ^ N) ^ 2 := pow_mul' Q 2 N
  generalize hmdef : Q ^ N = m at hms hm9 hm3 hXle
  have hg : Nat.gcd 2 (s - 1) ≤ 2 := Nat.le_of_dvd two_pos (Nat.gcd_dvd_left 2 _)
  have h2X : s * ((s - 1) * (s + 1)) ≤ 2 * (m * Q ^ C) := by
    calc s * ((s - 1) * (s + 1)) = Nat.card X * Nat.gcd 2 (s - 1) := by rw [hcX, hsq]
      _ ≤ Nat.card X * 2 := Nat.mul_le_mul_left _ hg
      _ ≤ (m * Q ^ C) * 2 := Nat.mul_le_mul_right _ hXle
      _ = 2 * (m * Q ^ C) := mul_comm _ _
  have hs8 : 8 ≤ s := by omega
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h2X
  have hmu : m ^ 3 ≤ (u + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have key : 3 * ((u + 1) * (u * (u + 1 + 1))) ≤ 2 * (u + 2) ^ 3 := by
    calc 3 * ((u + 1) * (u * (u + 1 + 1))) ≤ 3 * (2 * (m * Q ^ C)) :=
          Nat.mul_le_mul_left _ h2X
      _ = 2 * m * (3 * Q ^ C) := by ring
      _ ≤ 2 * m * m ^ 2 := Nat.mul_le_mul_left _ hm3
      _ = 2 * m ^ 3 := by ring
      _ ≤ 2 * (u + 2) ^ 3 := Nat.mul_le_mul_left _ hmu
  have h7 : 7 ≤ u := by omega
  have hA : 7 * u ^ 2 ≤ u ^ 3 :=
    calc 7 * u ^ 2 ≤ u * u ^ 2 := Nat.mul_le_mul_right _ h7
      _ = u ^ 3 := by ring
  have hB : 7 * u ≤ u ^ 2 :=
    calc 7 * u ≤ u * u := Nat.mul_le_mul_right _ h7
      _ = u ^ 2 := by ring
  nlinarith

theorem false_of_psl_two_of_excCompTag (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ' : StatedLieTag} {n' r e p f : ℕ} (hr2 : r ≠ 2) (ht : ExcCompTag τ' n')
    (hA1 : ¬ (τ' = .PSL ∧ n' = 2)) (hadm' : StatedLieAdmissible τ' n' r e)
    (hX' : LieModel X τ' n' r e) (hp : p.Prime) (hX : LieModel X .PSL 2 p f)
    (h5 : 5 ≤ p ^ f) : False := by
  have hr : r.Prime := hadm'.1
  have hQ3 : 3 ≤ r ^ e := three_le_pow hr hr2 hadm'.2.1
  have hQ2 : 2 ≤ r ^ e := by omega
  have s1 : ∀ k, (r ^ e) ^ k - 1 ≤ (r ^ e) ^ k := fun k => Nat.sub_le _ _
  have a1 : ∀ k, (r ^ e) ^ k + 1 ≤ (r ^ e) ^ (k + 1) := pow_add_one_le hQ2
  rcases ht with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hA1 ⟨rfl, rfl⟩
  · exact false_of_psl_two_of_cofactor_le (N := 15) (C := 20) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_pow_sub_one_le _ _ fun i => i).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 28) (C := 35) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_pow_sub_one_le _ _ fun i => i).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 15) (C := 22) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_unitary_le hQ2 _).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 28) (C := 38) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_unitary_le hQ2 _).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 9) (C := 12) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 16) (C := 20) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 16) (C := 20) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 20) (C := 25) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((mul_le_pow (s1 5) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 30) (C := 36) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((mul_le_pow (s1 6) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 56) (C := 64) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((mul_le_pow (s1 8) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 20) (C := 26) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) ((mul_le_pow (a1 5) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq
        (by rfl)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 6) (C := 8) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (s1 6) (s1 2)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 24) (C := 28) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (s1 8)) (s1 6)) (s1 2))
      (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 36) (C := 42) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (s1 9))
        (s1 8)) (s1 6)) (s1 5)) (s1 2)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 63) (C := 70) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow
        (s1 18) (s1 14)) (s1 12)) (s1 10)) (s1 8)) (s1 6)) (s1 2)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 120) (C := 128) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow
        (mul_le_pow (s1 30) (s1 24)) (s1 20)) (s1 18)) (s1 14)) (s1 12)) (s1 8)) (s1 2))
      (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 36) (C := 44) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (a1 9))
        (s1 8)) (s1 6)) (a1 5)) (s1 2)) (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 12) (C := 17) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (mul_le_pow (triality_factor_le hQ2) (s1 6)) (s1 2))
      (by norm_num)
  · exact false_of_psl_two_of_cofactor_le (N := 3) (C := 5) hO hr2 hadm' hX' hp hX h5 rfl
      (by norm_num) (mul_le_pow (a1 3) ((Nat.sub_le _ _).trans (pow_one _).ge)) (by norm_num)

theorem noPSL2Odd_of_lieModel (hO : LieOrderFormulasInput) {L : Type} [Group L]
    {τ' : StatedLieTag} {n' r e : ℕ} (hr2 : r ≠ 2) (ht : ExcCompTag τ' n')
    (hA1 : ¬ (τ' = .PSL ∧ n' = 2)) (hadm' : StatedLieAdmissible τ' n' r e)
    (hL : LieModel (L ⧸ center L) τ' n' r e) : NoPSL2Odd L :=
  fun _ _ hp h5 _ hm => false_of_psl_two_of_excCompTag hO hr2 ht hA1 hadm' hL hp hm h5

theorem noPSL2Odd_of_mulEquiv_SL2 {L : Type} [Group L] {K : Type} [Field K]
    (hK : ringChar K ≠ 2) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) K) : NoPSL2Odd L := by
  intro p f _ _ hodd _
  have hc : e.symm (-1) ∈ center L := Subgroup.mem_center_iff.mpr fun g => by
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, mul_neg_one, neg_one_mul]
  have hne : (-1 : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := fun h => by
    have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact Ring.neg_one_ne_one_of_char_ne_two hK h00
  have ho : orderOf (⟨e.symm (-1), hc⟩ : center L) = 2 := by
    rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [neg_one_sq]) hne
  have h2 := orderOf_dvd_natCard (⟨e.symm (-1), hc⟩ : center L)
  rw [ho] at h2
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
