module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

@[expose] def lieSOrdN : List ℕ := [181440, 50232960, 1451520, 193709880, 1056706560]

@[expose] def lieSOrdM : ℕ := 2 ^ 12 * 3 ^ 6 * 5 * 7 ^ 2 * 13 * 17 * 19 * 73

@[expose] def lieSOrdQ : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 3, 9, 27, 81, 243, 729, 5, 7, 49, 13, 17,
    19, 73]

theorem lieSOrdM_lt : lieSOrdM < 2 ^ 48 := by
  unfold lieSOrdM
  norm_num

theorem lieSOrd_dvd_M : ∀ N ∈ lieSOrdN, N ∣ lieSOrdM := by
  unfold lieSOrdN lieSOrdM
  decide +kernel

theorem lieSOrd_mem_of_eq {N : ℕ}
    (h : N = 181440 ∨ N = 50232960 ∨ N = 1451520 ∨ N = 193709880 ∨ N = 1056706560) :
    N ∈ lieSOrdN := by
  unfold lieSOrdN
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem lieSOrd_eq_of_dvd_pow {p r k : ℕ} (hp : p.Prime) (hr : r.Prime) (h : p ∣ r ^ k) :
    p = r :=
  (Nat.prime_dvd_prime_iff_eq hp hr).1 (hp.dvd_of_dvd_pow h)

theorem lieSOrd_prime_dvd_M {p : ℕ} (hp : p.Prime) (h : p ∣ lieSOrdM) :
    p ∈ ([2, 3, 5, 7, 13, 17, 19, 73] : List ℕ) := by
  have hM : lieSOrdM = ([2 ^ 12, 3 ^ 6, 5, 7 ^ 2, 13, 17, 19, 73] : List ℕ).prod := by
    unfold lieSOrdM
    norm_num
  rw [hM, hp.prime.dvd_prod_iff] at h
  obtain ⟨a, ha, hpa⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [lieSOrd_eq_of_dvd_pow hp Nat.prime_two hpa]
    decide
  · rw [lieSOrd_eq_of_dvd_pow hp Nat.prime_three hpa]
    decide
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hpa]
    decide
  · rw [lieSOrd_eq_of_dvd_pow hp (by norm_num : Nat.Prime 7) hpa]
    decide
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 hpa]
    decide
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 hpa]
    decide
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19)).1 hpa]
    decide
  · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)).1 hpa]
    decide

theorem lieSOrd_pp_dvd {q e : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e) (h : q ^ e ∣ lieSOrdM) :
    q ∈ lieSOrdQ ∧ e ≤ 12 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  have hpp : p.Prime := hp
  have hpM : p ∣ lieSOrdM :=
    (dvd_pow_self p (by omega : k ≠ 0)).trans ((dvd_pow_self (p ^ k) (by omega : e ≠ 0)).trans h)
  have h8 := lieSOrd_prime_dvd_M hpp hpM
  have hm : p ^ (k * e) ∣ lieSOrdM := by rwa [pow_mul]
  have hlt : k * e < 48 := by
    by_contra hge
    push Not at hge
    have h1 : 2 ^ 48 ≤ 2 ^ (k * e) := Nat.pow_le_pow_right (by norm_num) hge
    have h2 : 2 ^ (k * e) ≤ p ^ (k * e) := Nat.pow_le_pow_left hpp.two_le _
    have h3 : p ^ (k * e) ≤ lieSOrdM := Nat.le_of_dvd (by unfold lieSOrdM; norm_num) hm
    have := lieSOrdM_lt
    omega
  have hkle : k ≤ k * e := Nat.le_mul_of_pos_right k he
  have hkF : p ^ k ∣ lieSOrdM := (pow_dvd_pow p hkle).trans hm
  have key : ∀ p ∈ ([2, 3, 5, 7, 13, 17, 19, 73] : List ℕ), ∀ m < 48, p ^ m ∣ lieSOrdM →
      m ≤ 12 := by
    unfold lieSOrdM
    decide +kernel
  have key2 : ∀ p ∈ ([2, 3, 5, 7, 13, 17, 19, 73] : List ℕ), ∀ m < 48, 1 ≤ m →
      p ^ m ∣ lieSOrdM → p ^ m ∈ lieSOrdQ := by
    unfold lieSOrdM lieSOrdQ
    decide +kernel
  refine ⟨key2 p h8 k (by omega) hk hkF, ?_⟩
  have := key p h8 (k * e) hlt hm
  have h7 : e ≤ k * e := Nat.le_mul_of_pos_left e hk
  omega

theorem lieSOrd_gen_bound {N G e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hG : Nat.Coprime q G) (hmul : G * N = q ^ e * R) (hN : N ∈ lieSOrdN) :
    q ∈ lieSOrdQ ∧ e ≤ 12 := by
  have h1 : q ^ e ∣ G * N := ⟨R, hmul⟩
  have h2 : q ^ e ∣ N := (Nat.Coprime.pow_left e hG).dvd_of_dvd_mul_left h1
  exact lieSOrd_pp_dvd hq he (h2.trans (lieSOrd_dvd_M N hN))

theorem lieSOrd_gen_bound' {N e R q : ℕ} (hq : IsPrimePow q) (he : 1 ≤ e)
    (hmul : N = q ^ e * R) (hN : N ∈ lieSOrdN) : q ∈ lieSOrdQ ∧ e ≤ 12 :=
  lieSOrd_gen_bound hq he (Nat.coprime_one_right q) (by rw [one_mul]; exact hmul) hN

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
