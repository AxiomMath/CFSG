module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecOrd

public section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open Subgroup

@[expose] def NoPSp4 (p : ℕ) (L : Type) [Group L] : Prop :=
  ∀ f : ℕ, 5 ≤ p ^ f → ¬ LieModel (L ⧸ center L) .PSp 2 p f

theorem three_le_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) : 3 ≤ p ^ e :=
  le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)

theorem nine_le_pow {Q k : ℕ} (hQ : 3 ≤ Q) (hk : 2 ≤ k) : 9 ≤ Q ^ k :=
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
    _ ≤ Q ^ k := Nat.pow_le_pow_right (by omega) hk

theorem two_mul_pow_six_lt {q : ℕ} (hq : 2 ≤ q) :
    2 * q ^ 6 < 3 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  obtain ⟨b, hb⟩ : ∃ b, q ^ 2 = b + 1 := ⟨q ^ 2 - 1, by omega⟩
  have h4 : q ^ 4 = (b + 1) ^ 2 := by rw [← hb]; ring
  have h6 : q ^ 6 = (b + 1) ^ 3 := by rw [← hb]; ring
  have hb3 : 3 ≤ b := by omega
  have e4 : (b + 1) ^ 2 - 1 = b ^ 2 + 2 * b := by
    have : (b + 1) ^ 2 = b ^ 2 + 2 * b + 1 := by ring
    omega
  rw [h4, h6, hb, Nat.add_sub_cancel, e4]
  nlinarith

theorem mul_lt_pow_eight_sub_one {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2 - 1) * (q ^ 4 - 1) < q ^ 8 - 1 := by
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  obtain ⟨b, hb⟩ : ∃ b, q ^ 2 = b + 1 := ⟨q ^ 2 - 1, by omega⟩
  have h4 : q ^ 4 = (b + 1) ^ 2 := by rw [← hb]; ring
  have h8 : q ^ 8 = (b + 1) ^ 4 := by rw [← hb]; ring
  have e4 : (b + 1) ^ 2 - 1 = b ^ 2 + 2 * b := by
    have : (b + 1) ^ 2 = b ^ 2 + 2 * b + 1 := by ring
    omega
  have e8 : (b + 1) ^ 4 - 1 = b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b := by
    have : (b + 1) ^ 4 = b ^ 4 + 4 * b ^ 3 + 6 * b ^ 2 + 4 * b + 1 := by ring
    omega
  rw [h4, h8, hb, Nat.add_sub_cancel, e4, e8]
  nlinarith

theorem prod_pow_sub_one_le (Q : ℕ) (s : Finset ℕ) (e : ℕ → ℕ) :
    ∏ i ∈ s, (Q ^ e i - 1) ≤ Q ^ ∑ i ∈ s, e i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun _ _ => Nat.sub_le _ _

theorem pow_add_one_le {Q : ℕ} (hQ : 2 ≤ Q) (i : ℕ) : Q ^ i + 1 ≤ Q ^ (i + 1) := by
  have : 1 ≤ Q ^ i := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

theorem prod_unitary_le {Q : ℕ} (hQ : 2 ≤ Q) (s : Finset ℕ) :
    ∏ i ∈ s, (if Even i then Q ^ i - 1 else Q ^ i + 1) ≤
      Q ^ ∑ i ∈ s, (if Even i then i else i + 1) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod fun i _ => ?_
  split_ifs
  · exact Nat.sub_le _ _
  · exact pow_add_one_le hQ i

theorem mul_le_pow {Q a b k m : ℕ} (ha : a ≤ Q ^ k) (hb : b ≤ Q ^ m) : a * b ≤ Q ^ (k + m) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

theorem triality_factor_le {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 8 + Q ^ 4 + 1 ≤ Q ^ 9 :=
  (GSThmB.X10Rec.triality_factor_lt hQ).le

theorem card_of_psp4 (hO : LieOrderFormulasInput) {X : Type} [Group X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hX : LieModel X .PSp 2 p f) :
    Nat.card X * 2 = (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) ∧
      (Nat.card X).factorization p = 4 * f := by
  have h3 := three_le_pow hp hp2 hf
  have hadm : StatedLieAdmissible .PSp 2 p f :=
    ⟨hp, hf, le_rfl, fun h => by simp only [Prod.mk.injEq, true_and] at h; omega⟩
  obtain ⟨-, hc, hfac⟩ := hO X .PSp 2 p f hadm hX
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (Dvd.intro k rfl)
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  refine ⟨?_, ?_⟩
  · have hc' : Nat.card X * Nat.gcd 2 (p ^ f - 1) =
        (p ^ f) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ f) ^ (2 * i) - 1) := hc
    rw [hg, hI, Finset.prod_pair (by norm_num)] at hc'
    simpa using hc'
  · have hfac' : (Nat.card X).factorization p = 2 ^ 2 * f := hfac
    rw [hfac']
    ring

theorem false_of_psp4_of_cofactor_le (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ' : StatedLieTag} {n' p f' f N C : ℕ} (hp2 : p ≠ 2)
    (hadm' : StatedLieAdmissible τ' n' p f') (hX' : LieModel X τ' n' p f')
    (hX : LieModel X .PSp 2 p f) (h5 : 5 ≤ p ^ f) (hN : lieSylowExponent τ' n' = N)
    (hC : lieOrderCofactor τ' n' (p ^ f') ≤ (p ^ f') ^ C)
    (h9 : N * f' = 4 * f → 2 * C ≤ 3 * N ∧ 9 ≤ (p ^ f') ^ (3 * N - 2 * C)) : False := by
  have hp : p.Prime := hadm'.1
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  obtain ⟨h4c, h4f⟩ := card_of_psp4 hO hp hp2 hf hX
  obtain ⟨-, hc', hfac'⟩ := hO X τ' n' p f' hadm' hX'
  rw [hN] at hfac'
  have hNf : N * f' = 4 * f := hfac'.symm.trans h4f
  obtain ⟨h2C, h9'⟩ := h9 hNf
  have hQN : (p ^ f') ^ N = (p ^ f) ^ 4 := by
    rw [← pow_mul, ← pow_mul, mul_comm f' N, hNf, mul_comm]
  have hXle : Nat.card X ≤ (p ^ f') ^ (N + C) := by
    have hdiv := Nat.pos_of_ne_zero (lieOrderDivisor_ne_zero hadm')
    calc Nat.card X ≤ Nat.card X * lieOrderDivisor τ' n' (p ^ f') :=
          Nat.le_mul_of_pos_right _ hdiv
      _ = lieOrderNumerator τ' n' (p ^ f') := hc'
      _ = (p ^ f') ^ N * lieOrderCofactor τ' n' (p ^ f') := by
          rw [lieOrderNumerator_eq hadm', hN]
      _ ≤ (p ^ f') ^ N * (p ^ f') ^ C := Nat.mul_le_mul_left _ hC
      _ = (p ^ f') ^ (N + C) := (pow_add _ _ _).symm
  have hsq : 9 * Nat.card X ^ 2 ≤ (p ^ f) ^ 20 :=
    calc 9 * Nat.card X ^ 2 ≤ (p ^ f') ^ (3 * N - 2 * C) * ((p ^ f') ^ (N + C)) ^ 2 :=
          Nat.mul_le_mul h9' (Nat.pow_le_pow_left hXle 2)
      _ = ((p ^ f') ^ N) ^ 5 := by
          rw [← pow_mul (p ^ f') (N + C) 2, ← pow_add, ← pow_mul (p ^ f') N 5]
          congr 1
          omega
      _ = (p ^ f) ^ 20 := by rw [hQN, ← pow_mul]
  set q := p ^ f with hq
  have hkey := two_mul_pow_six_lt (q := q) (by omega)
  set A := (q ^ 2 - 1) * (q ^ 4 - 1) with hA
  have h36 : 9 * (q ^ 4 * A) ^ 2 ≤ 4 * q ^ 20 := by
    rw [← h4c]
    nlinarith
  have hq8 : 0 < q ^ 8 := by positivity
  have h' : 9 * A ^ 2 ≤ 4 * q ^ 12 := by
    have : q ^ 8 * (9 * A ^ 2) ≤ q ^ 8 * (4 * q ^ 12) :=
      calc q ^ 8 * (9 * A ^ 2) = 9 * (q ^ 4 * A) ^ 2 := by ring
        _ ≤ 4 * q ^ 20 := h36
        _ = q ^ 8 * (4 * q ^ 12) := by ring
    exact Nat.le_of_mul_le_mul_left this hq8
  have hsq' : (2 * q ^ 6) ^ 2 < (3 * A) ^ 2 := Nat.pow_lt_pow_left hkey (by norm_num)
  nlinarith

@[expose] def ExcCompTag (τ' : StatedLieTag) (n' : ℕ) : Prop :=
  τ' = .PSL ∧ (n' = 2 ∨ n' = 6 ∨ n' = 8) ∨ τ' = .PSU ∧ (n' = 6 ∨ n' = 8) ∨
    τ' = .PSp ∧ (n' = 3 ∨ n' = 4) ∨ τ' = .POmegaOdd ∧ n' = 4 ∨
    τ' = .POmegaPlus ∧ (n' = 5 ∨ n' = 6 ∨ n' = 8) ∨ τ' = .POmegaMinus ∧ n' = 5 ∨
    τ' = .G2 ∨ τ' = .F4 ∨ τ' = .E6 ∨ τ' = .E7 ∨ τ' = .E8 ∨ τ' = .twistedE6 ∨
    τ' = .trialityD4 ∨ τ' = .twistedG2

theorem false_of_psp4_of_psl_two (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {p f' f : ℕ} (hp2 : p ≠ 2) (hadm' : StatedLieAdmissible .PSL 2 p f')
    (hX' : LieModel X .PSL 2 p f') (hX : LieModel X .PSp 2 p f) (h5 : 5 ≤ p ^ f) : False := by
  have hp : p.Prime := hadm'.1
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  obtain ⟨h4c, h4f⟩ := card_of_psp4 hO hp hp2 hf hX
  obtain ⟨-, hc', hfac'⟩ := hO X .PSL 2 p f' hadm' hX'
  have hfac'' : (Nat.card X).factorization p = 1 * f' := hfac'
  have hf' : f' = 4 * f := by omega
  have hQ : p ^ f' = (p ^ f) ^ 4 := by rw [hf', ← pow_mul, mul_comm]
  have hodd : Odd (p ^ f') := (hp.odd_of_ne_two hp2).pow
  have hg : Nat.gcd 2 (p ^ f' - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (Dvd.intro k rfl)
  have hc2 : Nat.card X * Nat.gcd 2 (p ^ f' - 1) =
      (p ^ f') ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, ((p ^ f') ^ i - 1) := hc'
  rw [hg, Finset.Icc_self, Finset.prod_singleton, hQ] at hc2
  set q := p ^ f with hq
  have hq2 : 2 ≤ q := by omega
  have e1 : (q ^ 4) ^ (2 * (2 - 1) / 2) * ((q ^ 4) ^ 2 - 1) = q ^ 4 * (q ^ 8 - 1) := by
    rw [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, ← pow_mul q 4 2]
  have e : q ^ 4 * (q ^ 8 - 1) = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
    rw [← e1, ← hc2, h4c]
  have := Nat.eq_of_mul_eq_mul_left (by positivity) e
  have := mul_lt_pow_eight_sub_one hq2
  omega

theorem false_of_psp4_of_excCompTag (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ' : StatedLieTag} {n' p f' f : ℕ} (hp2 : p ≠ 2) (ht : ExcCompTag τ' n')
    (hadm' : StatedLieAdmissible τ' n' p f') (hX' : LieModel X τ' n' p f')
    (hX : LieModel X .PSp 2 p f) (h5 : 5 ≤ p ^ f) : False := by
  have hp : p.Prime := hadm'.1
  have hQ3 : 3 ≤ p ^ f' := three_le_pow hp hp2 hadm'.2.1
  have hQ2 : 2 ≤ p ^ f' := by omega
  have s1 : ∀ k, (p ^ f') ^ k - 1 ≤ (p ^ f') ^ k := fun k => Nat.sub_le _ _
  have a1 : ∀ k, (p ^ f') ^ k + 1 ≤ (p ^ f') ^ (k + 1) := pow_add_one_le hQ2
  have n9 : ∀ k, 2 ≤ k → 9 ≤ (p ^ f') ^ k := fun k hk => nine_le_pow hQ3 hk
  rcases ht with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact false_of_psp4_of_psl_two hO hp2 hadm' hX' hX h5
  · refine false_of_psp4_of_cofactor_le (N := 15) (C := 20) hO hp2 hadm' hX' hX h5 rfl
      ((prod_pow_sub_one_le _ _ fun i => i).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 5 le_add_self⟩
  · refine false_of_psp4_of_cofactor_le (N := 28) (C := 35) hO hp2 hadm' hX' hX h5 rfl
      ((prod_pow_sub_one_le _ _ fun i => i).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 14 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 15) (C := 22) hO hp2 hadm' hX' hX h5 rfl
      ((prod_unitary_le hQ2 _).trans_eq (by rfl)) fun hNf => ⟨by norm_num, ?_⟩
    have hNf' : 15 * f' = 4 * f := hNf
    have := hadm'.2.1
    have hf4 : 4 ≤ f' := by omega
    calc 9 ≤ 3 ^ 4 := by norm_num
      _ ≤ 3 ^ f' := Nat.pow_le_pow_right (by norm_num) hf4
      _ ≤ p ^ f' := Nat.pow_le_pow_left (by have := hp.two_le; omega) f'
      _ = (p ^ f') ^ (3 * 15 - 2 * 22) := by norm_num
  · refine false_of_psp4_of_cofactor_le (N := 28) (C := 38) hO hp2 hadm' hX' hX h5 rfl
      ((prod_unitary_le hQ2 _).trans_eq (by rfl)) fun _ => ⟨by norm_num, n9 8 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 9) (C := 12) hO hp2 hadm' hX' hX h5 rfl
      ((prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 3 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 16) (C := 20) hO hp2 hadm' hX' hX h5 rfl
      ((prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 8 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 16) (C := 20) hO hp2 hadm' hX' hX h5 rfl
      ((prod_pow_sub_one_le _ _ fun i => 2 * i).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 8 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 20) (C := 25) hO hp2 hadm' hX' hX h5 rfl
      ((mul_le_pow (s1 5) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 10 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 30) (C := 36) hO hp2 hadm' hX' hX h5 rfl
      ((mul_le_pow (s1 6) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 18 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 56) (C := 64) hO hp2 hadm' hX' hX h5 rfl
      ((mul_le_pow (s1 8) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 40 (by norm_num)⟩
  · refine false_of_psp4_of_cofactor_le (N := 20) (C := 26) hO hp2 hadm' hX' hX h5 rfl
      ((mul_le_pow (a1 5) (prod_pow_sub_one_le _ _ fun i => 2 * i)).trans_eq (by rfl)) fun _ =>
        ⟨by norm_num, n9 8 (by norm_num)⟩
  · exact false_of_psp4_of_cofactor_le (N := 6) (C := 8) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (s1 6) (s1 2)) fun _ => ⟨by norm_num, n9 2 le_rfl⟩
  · exact false_of_psp4_of_cofactor_le (N := 24) (C := 28) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (s1 8)) (s1 6)) (s1 2)) fun _ =>
        ⟨by norm_num, n9 16 (by norm_num)⟩
  · exact false_of_psp4_of_cofactor_le (N := 36) (C := 42) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (s1 9)) (s1 8))
        (s1 6)) (s1 5)) (s1 2)) fun _ => ⟨by norm_num, n9 24 (by norm_num)⟩
  · exact false_of_psp4_of_cofactor_le (N := 63) (C := 70) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 18) (s1 14))
        (s1 12)) (s1 10)) (s1 8)) (s1 6)) (s1 2)) fun _ => ⟨by norm_num, n9 49 (by norm_num)⟩
  · exact false_of_psp4_of_cofactor_le (N := 120) (C := 128) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow
        (s1 30) (s1 24)) (s1 20)) (s1 18)) (s1 14)) (s1 12)) (s1 8)) (s1 2)) fun _ =>
        ⟨by norm_num, n9 104 (by norm_num)⟩
  · exact false_of_psp4_of_cofactor_le (N := 36) (C := 44) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (mul_le_pow (s1 12) (a1 9)) (s1 8))
        (s1 6)) (a1 5)) (s1 2)) fun _ => ⟨by norm_num, n9 20 (by norm_num)⟩
  · exact false_of_psp4_of_cofactor_le (N := 12) (C := 17) hO hp2 hadm' hX' hX h5 rfl
      (mul_le_pow (mul_le_pow (triality_factor_le hQ2) (s1 6)) (s1 2)) fun _ =>
        ⟨by norm_num, n9 2 le_rfl⟩
  ·
    obtain ⟨k, hk⟩ := hadm'.2.2.2.2.1
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · rw [h0, pow_zero] at h5
        omega
      · exact h0
    have h4f := (card_of_psp4 hO hp hp2 hf hX).2
    have h3f : (Nat.card X).factorization p = 3 * f' := (hO X _ n' p f' hadm' hX').2.2
    omega

theorem noPSp4_of_lieModel (hO : LieOrderFormulasInput) {L : Type} [Group L] {τ' : StatedLieTag}
    {n' p f' : ℕ} (hp2 : p ≠ 2) (ht : ExcCompTag τ' n') (hadm' : StatedLieAdmissible τ' n' p f')
    (hL : LieModel (L ⧸ center L) τ' n' p f') : NoPSp4 p L :=
  fun _ h5 hm => false_of_psp4_of_excCompTag hO hp2 ht hadm' hL hm h5

theorem noPSp4_of_card_le (hO : LieOrderFormulasInput) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Type} [Group L] [Finite L] (h : Nat.card L ≤ 504) : NoPSp4 p L := by
  intro f h5 hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  have hc := (card_of_psp4 hO hp hp2 hf hm).1
  have hle : Nat.card (L ⧸ center L) ≤ 504 :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans h
  have := GSThmB.X10Rec.two_mul_pow_eight_lt h5
  have h8 : 6 ^ 8 ≤ (p ^ f + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  omega

end CFSG.ComponentClassification.Burgoyne.X10
