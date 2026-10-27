module

public import CFSG.GH74.Generic.S3.L3FRankDvd
public import CFSG.GH74.Generic.S3.L3FRankSize

public section

namespace CFSG.GH74.Generic.S3.L3Ord

open CFSG.GH74.Generic CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordRee ordSuzuki)

section Num

variable {N p' f' q : ℕ}

theorem bound_PSL (hq : 5 ≤ q) (hp' : p'.Prime) (hf' : 1 ≤ f') {n' : ℕ} (hn2 : 2 ≤ n')
    (hn5 : n' ≤ 5) (hcard : N = ordA (n' - 1) (p' ^ f'))
    (hkey : ∀ {k : ℕ}, (p' ^ f') ^ k ∣ N → (p' ^ f') ^ k ≤ q ^ 3)
    (h3N : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N) :
    FValue .PSL n' p' f' ≤ q ^ 4 * 6 := by
  have hq1 : 1 < p' ^ f' := Nat.one_lt_pow (by omega) hp'.one_lt
  obtain rfl | rfl | rfl | rfl : n' = 2 ∨ n' = 3 ∨ n' = 4 ∨ n' = 5 := by omega
  · have hd : (p' ^ f') ^ 1 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordA (m := 1) (q := p' ^ f') le_rfl (by omega)
    have e : FValue .PSL 2 p' f' = p' ^ f' * 6 := by simp [FValue, lieRankSq, lieTypeRank]
    rw [e]
    exact fb_A1 (by omega) (by simpa using hkey hd)
  · have hd : (p' ^ f') ^ 3 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordA (m := 2) (q := p' ^ f') (by norm_num) (by omega)
    have e : FValue .PSL 3 p' f' = (p' ^ f') ^ 4 * 6 := by simp [FValue, lieRankSq, lieTypeRank]
    rw [e]
    exact fb_A2 (hkey hd)
  · exfalso
    have hd : (p' ^ f') ^ 6 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordA (m := 3) (q := p' ^ f') (by norm_num) (by omega)
    have hs := size_L4 hq (by omega : 2 ≤ p' ^ f') (hkey hd)
    rw [show N = ordA 3 (p' ^ f') from hcard] at h3N
    exact absurd h3N (not_le.2 hs)
  · exfalso
    have hd : (p' ^ f') ^ 10 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordA (m := 4) (q := p' ^ f') (by norm_num) (by omega)
    have hs := size_L5 hq (by omega : 2 ≤ p' ^ f') (hkey hd)
    rw [show N = ordA 4 (p' ^ f') from hcard] at h3N
    exact absurd h3N (not_le.2 hs)


theorem bound_PSU_odd (hq : 5 ≤ q) (hp' : p'.Prime) (hf' : 1 ≤ f') {n' : ℕ} (hn3 : 3 ≤ n')
    (hn5 : n' ≤ 5) (hcard : N = ordTwistedA (n' - 1) (p' ^ f'))
    (hkey : ∀ {k : ℕ}, (p' ^ f') ^ k ∣ N → (p' ^ f') ^ k ≤ q ^ 3)
    (h3N : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N) :
    FValue .PSU n' p' f' ≤ q ^ 4 * 6 := by
  have hq1 : 1 < p' ^ f' := Nat.one_lt_pow (by omega) hp'.one_lt
  obtain rfl | rfl | rfl : n' = 3 ∨ n' = 4 ∨ n' = 5 := by omega
  · have hd : (p' ^ f') ^ 3 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordTwistedA (m := 2) (q := p' ^ f') (by norm_num)
    have e : FValue .PSU 3 p' f' = (p' ^ f') ^ 4 * 6 := by simp [FValue, lieRankSq, lieTypeRank]
    rw [e]
    exact fb_A2 (hkey hd)
  · exfalso
    have hd : (p' ^ f') ^ 6 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordTwistedA (m := 3) (q := p' ^ f') (by norm_num)
    have hs := size_U4 hq (by omega : 2 ≤ p' ^ f') (hkey hd)
    rw [show N = ordTwistedA 3 (p' ^ f') from hcard] at h3N
    exact absurd h3N (not_le.2 hs)
  · exfalso
    have hd : (p' ^ f') ^ 10 ∣ N := by
      rw [hcard]; simpa using pow_dvd_ordTwistedA (m := 4) (q := p' ^ f') (by norm_num)
    have hs := size_U5 hq (by omega : 2 ≤ p' ^ f') (hkey hd)
    rw [show N = ordTwistedA 4 (p' ^ f') from hcard] at h3N
    exact absurd h3N (not_le.2 hs)

theorem bound_PSU_even {n' : ℕ} (hn3 : 3 ≤ n') (hf' : 1 ≤ f') (h : f' * (n' - 2) ≤ 2) :
    FValue .PSU n' 2 f' ≤ 3750 := by
  have hn : n' ≤ 4 := by
    by_contra hc
    have : 3 ≤ n' - 2 := by omega
    have : 1 * 3 ≤ f' * (n' - 2) := Nat.mul_le_mul hf' this
    omega
  have hf2 : f' ≤ 2 := by
    by_contra hc
    have : 3 ≤ f' := by omega
    have : 3 * 1 ≤ f' * (n' - 2) := Nat.mul_le_mul this (by omega)
    omega
  obtain rfl | rfl : n' = 3 ∨ n' = 4 := by omega
  · obtain rfl | rfl : f' = 1 ∨ f' = 2 := by omega
    · simp [FValue, lieRankSq, lieTypeRank]
    · simp [FValue, lieRankSq, lieTypeRank]
  · obtain rfl : f' = 1 := by omega
    simp [FValue, lieRankSq, lieTypeRank]

theorem bound_PSp_odd (hq : 5 ≤ q) (hp' : p'.Prime) (hf' : 1 ≤ f') {n' : ℕ} (hn : n' = 2)
    (hcard : N = ordBC n' (p' ^ f'))
    (hkey : ∀ {k : ℕ}, (p' ^ f') ^ k ∣ N → (p' ^ f') ^ k ≤ q ^ 3) :
    FValue .PSp n' p' f' ≤ q ^ 4 * 6 := by
  subst hn
  have hq1 : 1 < p' ^ f' := Nat.one_lt_pow (by omega) hp'.one_lt
  have hd : (p' ^ f') ^ 4 ∣ N := by
    rw [hcard]; simpa using pow_dvd_ordBC (m := 2) (q := p' ^ f') (by norm_num) (by omega)
  have e : FValue .PSp 2 p' f' = (p' ^ f') ^ 4 * 6 + 3 := by simp [FValue, lieRankSq, lieTypeRank]
  rw [e]
  exact fb_C2 hq (hkey hd)

theorem bound_PSp_even {n' : ℕ} (hn2 : 2 ≤ n') (hf' : 1 ≤ f') (h : f' * (n' + 1) ≤ 4) :
    FValue .PSp n' 2 f' ≤ 3750 := by
  have hn : n' ≤ 3 := by
    by_contra hc
    have : 1 * 5 ≤ f' * (n' + 1) := Nat.mul_le_mul hf' (by omega)
    omega
  have hf1 : f' = 1 := by
    by_contra hc
    have : 2 * 3 ≤ f' * (n' + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  subst hf1
  obtain rfl | rfl : n' = 2 ∨ n' = 3 := by omega
  · simp [FValue, lieRankSq, lieTypeRank]
  · simp [FValue, lieRankSq, lieTypeRank]

theorem bound_G2 (hq : 5 ≤ q) {n' : ℕ} (hcard : N = ordG2 (p' ^ f'))
    (hkey : ∀ {k : ℕ}, (p' ^ f') ^ k ∣ N → (p' ^ f') ^ k ≤ q ^ 3) :
    FValue .G2 n' p' f' ≤ q ^ 4 * 6 := by
  have hd : (p' ^ f') ^ 6 ∣ N := by
    rw [hcard]; exact pow_dvd_ordG2 _
  have e : FValue .G2 n' p' f' = (p' ^ f') ^ 4 * 6 + 5 := by simp [FValue, lieRankSq, lieTypeRank]
  rw [e]
  exact fb_G2 hq (hkey hd)

theorem bound_D4 (hq : 5 ≤ q) (hp' : p'.Prime) (hf' : 1 ≤ f') (hcard : N = ordTrialityD4 (p' ^ f'))
    (hkey : ∀ {k : ℕ}, (p' ^ f') ^ k ∣ N → (p' ^ f') ^ k ≤ q ^ 3)
    (h3N : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N) : False := by
  have hq1 : 1 < p' ^ f' := Nat.one_lt_pow (by omega) hp'.one_lt
  have hd : (p' ^ f') ^ 12 ∣ N := by
    rw [hcard]; exact pow_dvd_ordTrialityD4 _
  have hs := size_3D4 hq (by omega : 2 ≤ p' ^ f') (hkey hd)
  rw [show N = ordTrialityD4 (p' ^ f') from hcard] at h3N
  exact absurd h3N (not_le.2 hs)

theorem bound_Ree {Q : ℕ} (hq : 5 ≤ q) (hQ : 2 ≤ Q) (hcard : N = ordRee Q)
    (hkey : Q ^ 3 ∣ N → Q ^ 3 ≤ q ^ 3)
    (h3N : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≤ 3 * N) : False := by
  have hd : Q ^ 3 ∣ N := by
    rw [hcard]; exact pow_dvd_ordRee _
  have hs := size_Ree hq hQ (hkey hd)
  rw [hcard] at h3N
  exact absurd h3N (not_le.2 hs)

theorem bound_Sz (hcard : N = ordSuzuki 8) (h124 : 124000 ≤ N) : False := by
  rw [hcard] at h124
  norm_num [ordSuzuki] at h124

end Num

end CFSG.GH74.Generic.S3.L3Ord
