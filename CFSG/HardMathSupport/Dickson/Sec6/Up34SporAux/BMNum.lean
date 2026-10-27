module

public import CFSG.Open.MonsterDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Classes

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.HardMathSupport.Solomon.Coordinator.YS08

theorem dvd_of_pow_three_dvd_cube_mul {r K R : ℕ} (hR : ∀ n : ℕ, n ^ 3 ∣ R → n = 1)
    (h : r ^ 3 ∣ K ^ 3 * R) : r ∣ K := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact dvd_zero r
  obtain ⟨g, r', K', hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right r hK)
  have h2 : g ^ 3 * r' ^ 3 ∣ g ^ 3 * (K' ^ 3 * R) := by
    have e1 : (r' * g) ^ 3 = g ^ 3 * r' ^ 3 := by ring
    have e2 : (K' * g) ^ 3 * R = g ^ 3 * (K' ^ 3 * R) := by ring
    rwa [e1, e2] at h
  have h3 : r' ^ 3 ∣ K' ^ 3 * R := Nat.dvd_of_mul_dvd_mul_left (pow_pos hg 3) h2
  have h4 : r' ^ 3 ∣ R := (Nat.Coprime.pow 3 3 hcop).dvd_of_dvd_mul_left h3
  rw [hR r' h4, one_mul]
  exact dvd_mul_left g K'

theorem l3_forall_of_cubeRoot {N K R : ℕ} (hNR : 3 * N = K ^ 3 * R)
    (hR : ∀ n : ℕ, n ^ 3 ∣ R → n = 1) (P : ℕ → Bool → ℕ → Prop)
    (h : ∀ r : ℕ, r ∣ K → ∀ (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Ord r ε ∣ N * e →
      P r ε e) :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → L3Ord r ε ∣ N * e →
      P r ε e := by
  intro r ε e he _ hdvd
  have h1 : r ^ 3 ∣ L3Ord r ε := by
    unfold L3Ord
    exact (dvd_mul_right _ _).mul_right _
  have h2 : N * e ∣ 3 * N := by
    rcases he with rfl | rfl
    · exact ⟨3, by ring⟩
    · exact ⟨1, by ring⟩
  refine h r (dvd_of_pow_three_dvd_cube_mul hR ?_) ε e he hdvd
  rw [← hNR]
  exact h1.trans (hdvd.trans h2)

@[expose] def primePowProd : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: t => p ^ e * primePowProd t

@[expose] def primePowDivs : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p, e) :: t => (List.range (e + 1)).flatMap fun i => (primePowDivs t).map fun d => p ^ i * d

theorem mem_primePowDivs {L : List (ℕ × ℕ)} (hL : ∀ x ∈ L, x.1.Prime) {r : ℕ}
    (hr : r ∣ primePowProd L) : r ∈ primePowDivs L := by
  induction L generalizing r with
  | nil =>
    rw [primePowProd, Nat.dvd_one] at hr
    simp [primePowDivs, hr]
  | cons x t ih =>
    obtain ⟨p, e⟩ := x
    have hp : p.Prime := hL (p, e) List.mem_cons_self
    have ht : ∀ y ∈ t, y.1.Prime := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    rw [primePowProd] at hr
    obtain ⟨k₁, k₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.1 hr
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 h₁
    rw [primePowDivs, List.mem_flatMap]
    exact ⟨i, List.mem_range.2 (by omega), List.mem_map.2 ⟨k₂, ih (r := k₂) ht h₂, rfl⟩⟩

@[expose] def cubeFreeCheck (L : List (ℕ × ℕ)) (R : ℕ) : Bool :=
  (primePowDivs L).all fun n => decide (n ^ 3 ∣ R → n = 1)

theorem cubeFree_of_check {L : List (ℕ × ℕ)} {R : ℕ} (hL : ∀ x ∈ L, x.1.Prime)
    (hR : primePowProd L = R) (h : cubeFreeCheck L R = true) :
    ∀ n : ℕ, n ^ 3 ∣ R → n = 1 := by
  intro n hn
  have hnR : n ∣ primePowProd L := by
    rw [hR]
    exact (dvd_pow_self n (by norm_num)).trans hn
  unfold cubeFreeCheck at h
  exact of_decide_eq_true (List.all_eq_true.1 h n (mem_primePowDivs hL hnR)) hn

@[expose] def l3DivCheck (L : List (ℕ × ℕ)) (N : ℕ) (P : ℕ → Bool → ℕ → Prop)
    [∀ r ε e, Decidable (P r ε e)] : Bool :=
  (primePowDivs L).all fun r => [true, false].all fun ε => [1, 3].all fun e =>
    decide (l3CondB r ε = true → L3Ord r ε ∣ N * e → P r ε e)

theorem l3_forall_of_divCheck {N K R : ℕ} {LK LR : List (ℕ × ℕ)} (hNR : 3 * N = K ^ 3 * R)
    (hLK : ∀ x ∈ LK, x.1.Prime) (hK : primePowProd LK = K) (hLR : ∀ x ∈ LR, x.1.Prime)
    (hR : primePowProd LR = R) (hcf : cubeFreeCheck LR R = true)
    (P : ℕ → Bool → ℕ → Prop) [∀ r ε e, Decidable (P r ε e)] (h : l3DivCheck LK N P = true) :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε → L3Ord r ε ∣ N * e →
      P r ε e := by
  have hmain : ∀ r : ℕ, r ∣ K → ∀ (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) →
      L3Ord r ε ∣ N * e → L3Cond r ε → P r ε e := by
    intro r hrK ε e he hdvd hc
    have hmem : r ∈ primePowDivs LK := by
      refine mem_primePowDivs hLK ?_
      rw [hK]
      exact hrK
    unfold l3DivCheck at h
    have h1 := List.all_eq_true.1 h r hmem
    have h2 := List.all_eq_true.1 h1 ε (by cases ε <;> simp)
    have h3 := List.all_eq_true.1 h2 e (by rcases he with rfl | rfl <;> simp)
    exact of_decide_eq_true h3 (l3CondB_of_cond hc) hdvd
  intro r ε e he hc hdvd
  exact l3_forall_of_cubeRoot hNR (cubeFree_of_check hLR hR hcf)
    (fun r ε e => L3Cond r ε → P r ε e) hmain r ε e he hc hdvd hc

theorem l3_forall_of_check_B (P : ℕ → Bool → ℕ → Prop) [∀ r ε e, Decidable (P r ε e)]
    (h : l3DivCheck [(2, 13), (3, 4), (5, 2)] 4154781481226426191177580544000000 P = true) :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε →
      L3Ord r ε ∣ 4154781481226426191177580544000000 * e → P r ε e :=
  l3_forall_of_divCheck (K := 16588800) (R := 2730389017356)
    (LR := [(2, 2), (3, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (47, 1)])
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel)
    (by decide +kernel) P h

theorem l3_forall_of_check_M (P : ℕ → Bool → ℕ → Prop) [∀ r ε e, Decidable (P r ε e)]
    (h : l3DivCheck [(2, 15), (3, 7), (5, 3), (7, 2), (13, 1)]
      808017424794512875886459904961710757005754368000000000 P = true) :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε →
      L3Ord r ε ∣ 808017424794512875886459904961710757005754368000000000 * e → P r ε e :=
  l3_forall_of_divCheck (K := 5706215424000) (R := 13046604315895546)
    (LR := [(2, 1), (11, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (47, 1),
      (59, 1), (71, 1)])
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by decide +kernel)
    (by decide +kernel) P h

theorem noL3Eq_B : NoL3Eq 4154781481226426191177580544000000 := by
  intro r ε e he hc heq
  exact l3_forall_of_check_B (fun r ε e => 4154781481226426191177580544000000 * e ≠ L3Ord r ε)
    (by decide +kernel) r ε e he hc (dvd_of_eq heq.symm) heq

theorem noL3Eq_M : NoL3Eq 808017424794512875886459904961710757005754368000000000 := by
  intro r ε e he hc heq
  exact l3_forall_of_check_M
    (fun r ε e => 808017424794512875886459904961710757005754368000000000 * e ≠ L3Ord r ε)
    (by decide +kernel) r ε e he hc (dvd_of_eq heq.symm) heq

theorem noL3DvdPrime_B_seven : NoL3DvdPrime 4154781481226426191177580544000000 7 := by
  intro r ε e he hc hd
  exact l3_forall_of_check_B (fun r ε _ => 7 ∣ L3Ord r ε) (by decide +kernel) r ε e he hc hd

theorem l3_not_dvd_sq_B_fi22 :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε →
      L3Ord r ε ∣ 4154781481226426191177580544000000 * e →
        ¬ 64561751654400 ∣ L3Ord r ε ^ 2 := by
  intro r ε e he hc hd
  exact l3_forall_of_check_B (fun r ε _ => ¬ 64561751654400 ∣ L3Ord r ε ^ 2)
    (by decide +kernel) r ε e he hc hd

theorem l3_not_dvd_sq_M_fi23 :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε →
      L3Ord r ε ∣ 808017424794512875886459904961710757005754368000000000 * e →
        ¬ 4089470473293004800 ∣ L3Ord r ε ^ 2 := by
  intro r ε e he hc hd
  exact l3_forall_of_check_M (fun r ε _ => ¬ 4089470473293004800 ∣ L3Ord r ε ^ 2)
    (by decide +kernel) r ε e he hc hd

theorem l3_not_dvd_sq_M_th :
    ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε →
      L3Ord r ε ∣ 808017424794512875886459904961710757005754368000000000 * e →
        ¬ 90745943887872000 ∣ L3Ord r ε ^ 2 := by
  intro r ε e he hc hd
  exact l3_forall_of_check_M (fun r ε _ => ¬ 90745943887872000 ∣ L3Ord r ε ^ 2)
    (by decide +kernel) r ε e he hc hd

theorem le_eight_of_pow_le_B {k : ℕ} (hk : 6720 ^ k ≤ 4154781481226426191177580544000000) :
    k ≤ 8 := by
  by_contra h
  have h9 : 6720 ^ 9 ≤ 6720 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h9.trans hk
  norm_num at this

theorem le_fourteen_of_pow_le_M {k : ℕ}
    (hk : 6720 ^ k ≤ 808017424794512875886459904961710757005754368000000000) : k ≤ 14 := by
  by_contra h
  have h15 : 6720 ^ 15 ≤ 6720 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h15.trans hk
  norm_num at this

theorem factorial_lt_B_fi22 (k : ℕ) (hk : 6720 ^ k ≤ 4154781481226426191177580544000000) :
    k.factorial < 64561751654400 :=
  calc k.factorial ≤ (8).factorial := Nat.factorial_le (le_eight_of_pow_le_B hk)
    _ < 64561751654400 := by norm_num [Nat.factorial]

theorem factorial_lt_M_fi23 (k : ℕ)
    (hk : 6720 ^ k ≤ 808017424794512875886459904961710757005754368000000000) :
    k.factorial < 4089470473293004800 :=
  calc k.factorial ≤ (14).factorial := Nat.factorial_le (le_fourteen_of_pow_le_M hk)
    _ < 4089470473293004800 := by norm_num [Nat.factorial]

theorem factorial_lt_M_th (k : ℕ)
    (hk : 6720 ^ k ≤ 808017424794512875886459904961710757005754368000000000) :
    k.factorial < 90745943887872000 :=
  calc k.factorial ≤ (14).factorial := Nat.factorial_le (le_fourteen_of_pow_le_M hk)
    _ < 90745943887872000 := by norm_num [Nat.factorial]

theorem monsterOrder_eq_numeral :
    CFSG.Open.monsterOrder = 808017424794512875886459904961710757005754368000000000 := by
  unfold CFSG.Open.monsterOrder
  norm_num

theorem monsterBabyOrder_eq_numeral :
    CFSG.Open.monsterBabyOrder = 4154781481226426191177580544000000 := by
  unfold CFSG.Open.monsterBabyOrder
  norm_num

end CFSG.HardMathSupport.Dickson.Sec6.BM
