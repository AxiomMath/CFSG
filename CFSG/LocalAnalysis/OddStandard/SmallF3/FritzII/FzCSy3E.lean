module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3E0

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] {x₁ x₂ : G}

private lemma fzc_sy3_pow4 {x : G} (h : orderOf x = 4) : x ^ 4 = 1 := by
  rw [← h]; exact pow_orderOf_eq_one x

private lemma fzc_sy3_sq_inv (x : G) : x ^ 2 * (x⁻¹ * x⁻¹) = 1 := by group

private lemma fzc_sy3_conj_mul (g a b : G) :
    g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) :=
  (conj_mul (a := a) (b := g) (c := b)).symm

private lemma fzc_sy3_conj_pow (g a : G) (n : ℕ) :
    g * a ^ n * g⁻¹ = (g * a * g⁻¹) ^ n :=
  (conj_pow (a := g) (b := a) (i := n)).symm

private lemma fzc_sy3_conj_mono (g : G) (a b : ℕ) :
    g * (x₁ ^ a * x₂ ^ b) * g⁻¹
      = (g * x₁ * g⁻¹) ^ a * (g * x₂ * g⁻¹) ^ b := by
  rw [fzc_sy3_conj_mul, fzc_sy3_conj_pow, fzc_sy3_conj_pow]

private lemma fzc_sy3_conj_inv_mono (g : G) (a b : ℕ) :
    g⁻¹ * (x₁ ^ a * x₂ ^ b) * g
      = (g⁻¹ * x₁ * g) ^ a * (g⁻¹ * x₂ * g) ^ b := by
  simpa using fzc_sy3_conj_mono (x₁ := x₁) (x₂ := x₂) (g := g⁻¹) a b

private lemma fzc_sy3_mono_mul (hc : Commute x₁ x₂) (a b c d : ℕ) :
    (x₁ ^ a * x₂ ^ b) * (x₁ ^ c * x₂ ^ d) = x₁ ^ (a + c) * x₂ ^ (b + d) := by
  have h2 : x₂ ^ b * x₁ ^ c = x₁ ^ c * x₂ ^ b := (hc.pow_pow c b).eq.symm
  calc (x₁ ^ a * x₂ ^ b) * (x₁ ^ c * x₂ ^ d)
      = x₁ ^ a * (x₂ ^ b * x₁ ^ c) * x₂ ^ d := by group
    _ = x₁ ^ a * (x₁ ^ c * x₂ ^ b) * x₂ ^ d := by rw [h2]
    _ = (x₁ ^ a * x₁ ^ c) * (x₂ ^ b * x₂ ^ d) := by group
    _ = x₁ ^ (a + c) * x₂ ^ (b + d) := by rw [pow_add, pow_add]

private lemma fzc_sy3_mono_pow (hc : Commute x₁ x₂) (a b n : ℕ) :
    (x₁ ^ a * x₂ ^ b) ^ n = x₁ ^ (a * n) * x₂ ^ (b * n) := by
  rw [(hc.pow_pow a b).mul_pow n, ← pow_mul, ← pow_mul]

private lemma fzc_sy3_mono_inv (hc : Commute x₁ x₂) (hx₁ : x₁ ^ 4 = 1) (hx₂ : x₂ ^ 4 = 1)
    (a b : ℕ) : (x₁ ^ a * x₂ ^ b)⁻¹ = x₁ ^ (3 * a) * x₂ ^ (3 * b) := by
  have p₁ : (x₁ ^ a)⁻¹ = x₁ ^ (3 * a) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show a + 3 * a = 4 * a by ring, pow_mul, hx₁, one_pow]
  have p₂ : (x₂ ^ b)⁻¹ = x₂ ^ (3 * b) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add, show b + 3 * b = 4 * b by ring, pow_mul, hx₂, one_pow]
  rw [mul_inv_rev, p₁, p₂, (hc.pow_pow (3 * a) (3 * b)).eq.symm]

private lemma fzc_sy3_sq (hc : Commute x₁ x₂) : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := by
  simpa using fzc_sy3_mono_pow (x₁ := x₁) (x₂ := x₂) hc 1 1 2

private lemma fzc_sy3_s_conj_mono (s : G) (hs₁ : s * x₁ * s⁻¹ = x₂)
    (hs₂ : s * x₂ * s⁻¹ = x₁) (a b : ℕ) :
    s * (x₁ ^ a * x₂ ^ b) * s⁻¹ = x₂ ^ a * x₁ ^ b := by
  rw [fzc_sy3_conj_mono, hs₁, hs₂]

private lemma fzc_sy3_c_conj_mono (c : G) (hc₁ : c⁻¹ * x₁ * c = x₂)
    (hc₂ : c⁻¹ * x₂ * c = x₁) (a b : ℕ) :
    c⁻¹ * (x₁ ^ a * x₂ ^ b) * c = x₂ ^ a * x₁ ^ b := by
  rw [fzc_sy3_conj_inv_mono, hc₁, hc₂]

private lemma fzc_sy3_shift_prod (c : G) (hc : Commute x₁ x₂) (hc₁ : c⁻¹ * x₁ * c = x₂)
    (hc₂ : c⁻¹ * x₂ * c = x₁) (i j : ℕ) :
    c⁻¹ * (x₁ ^ i * x₂ ^ j) * c * (x₁ ^ i * x₂ ^ j) = x₁ ^ (i + j) * x₂ ^ (i + j) := by
  have h1 : c⁻¹ * (x₁ ^ i * x₂ ^ j) * c = x₂ ^ i * x₁ ^ j :=
    fzc_sy3_c_conj_mono c hc₁ hc₂ i j
  have hcomm : x₂ ^ i * x₁ ^ j = x₁ ^ j * x₂ ^ i := (hc.pow_pow j i).eq.symm
  rw [h1, hcomm, fzc_sy3_mono_mul hc j i i j, Nat.add_comm j i]

private lemma fzc_sy3_shift_w1 (hc : Commute x₁ x₂) (k : ℕ) :
    x₂ ^ 2 * (x₁ * x₂) ^ k = x₁ ^ k * x₂ ^ (k + 2) := by
  have hp : (x₁ * x₂) ^ k = x₁ ^ k * x₂ ^ k := by
    simpa using fzc_sy3_mono_pow (x₁ := x₁) (x₂ := x₂) hc 1 1 k
  rw [hp]
  have hm := fzc_sy3_mono_mul (x₁ := x₁) (x₂ := x₂) hc 0 2 k k
  simpa [Nat.add_comm] using hm

private lemma fzc_sy3_shift_w (c : G) (hc : Commute x₁ x₂) (hx₁ : x₁ ^ 4 = 1)
    (hx₂ : x₂ ^ 4 = 1) (hc₁ : c⁻¹ * x₁ * c = x₂) (hc₂ : c⁻¹ * x₂ * c = x₁) (i j k : ℕ) :
    x₂ ^ 2 * (x₁ * x₂) ^ k * (c⁻¹ * (x₁ ^ i * x₂ ^ j) * c * (x₁ ^ i * x₂ ^ j))⁻¹
      = x₁ ^ (k + 3 * (i + j)) * x₂ ^ (k + 2 + 3 * (i + j)) := by
  have hprod := fzc_sy3_shift_prod (x₁ := x₁) (x₂ := x₂) c hc hc₁ hc₂ i j
  have hinv : (c⁻¹ * (x₁ ^ i * x₂ ^ j) * c * (x₁ ^ i * x₂ ^ j))⁻¹
      = x₁ ^ (3 * (i + j)) * x₂ ^ (3 * (i + j)) := by
    rw [hprod, fzc_sy3_mono_inv hc hx₁ hx₂]
  rw [hinv, fzc_sy3_shift_w1 hc]
  have hm := fzc_sy3_mono_mul (x₁ := x₁) (x₂ := x₂) hc k (k + 2) (3 * (i + j)) (3 * (i + j))
  rw [hm]

theorem fzc_sy3_shift {c : G} (hc : x₁ * x₂ = x₂ * x₁) (h₁ : orderOf x₁ = 4)
    (h₂ : orderOf x₂ = 4) (hinf : zpowers x₁ ⊓ zpowers x₂ = ⊥) (hc₁ : c⁻¹ * x₁ * c = x₂)
    (hc₂ : c⁻¹ * x₂ * c = x₁) {A : Subgroup G} (hAE : A ≤ baseGrp x₁ x₂) (k : ℕ) :
    ∃ e ∈ A, ∀ a ∈ A, a ^ 2 ≠ x₂ ^ 2 * (x₁ * x₂) ^ k * (c⁻¹ * e * c * e)⁻¹ := by
  have hx₁ : x₁ ^ 4 = 1 := fzc_sy3_pow4 h₁
  have hx₂ : x₂ ^ 4 = 1 := fzc_sy3_pow4 h₂
  have hcom : Commute x₁ x₂ := hc
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  ·
    by_cases hcase : ∃ e₀ ∈ A, ∃ i j : ℕ, i < 4 ∧ j < 4 ∧ e₀ = x₁ ^ i * x₂ ^ j ∧
      (i + j) % 2 = 1
    · obtain ⟨e₀, he₀, i, j, hi, hj, rfl, hodd⟩ := hcase
      refine ⟨x₁ ^ i * x₂ ^ j, he₀, ?_⟩
      intro a ha haeq
      obtain ⟨i', j', hi', hj', rfl⟩ := fzc_sy3_coord hc h₁ h₂ (hAE ha)
      rw [fzc_sy3_mono_pow hcom i' j' 2, fzc_sy3_shift_w c hcom hx₁ hx₂ hc₁ hc₂ i j k] at haeq
      have hcong := (fzc_sy3_coord_eq h₁ h₂ hinf).mp haeq
      omega
    · refine ⟨1, A.one_mem, ?_⟩
      intro a ha haeq
      obtain ⟨i', j', hi', hj', rfl⟩ := fzc_sy3_coord hc h₁ h₂ (hAE ha)
      have hsum : (i' + j') % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one (i' + j') with h | h
        · exact h
        · exact absurd ⟨x₁ ^ i' * x₂ ^ j', ha, i', j', hi', hj', rfl, h⟩ hcase
      have hone : c⁻¹ * (1 : G) * c * 1 = 1 := by group
      rw [hone, inv_one, mul_one, fzc_sy3_mono_pow hcom i' j' 2,
        fzc_sy3_shift_w1 hcom] at haeq
      have hcong := (fzc_sy3_coord_eq h₁ h₂ hinf).mp haeq
      omega
  ·
    refine ⟨1, A.one_mem, ?_⟩
    intro a ha haeq
    obtain ⟨i', j', hi', hj', rfl⟩ := fzc_sy3_coord hc h₁ h₂ (hAE ha)
    have hone : c⁻¹ * (1 : G) * c * 1 = 1 := by group
    rw [hone, inv_one, mul_one, fzc_sy3_mono_pow hcom i' j' 2,
      fzc_sy3_shift_w1 hcom] at haeq
    have hcong := (fzc_sy3_coord_eq h₁ h₂ hinf).mp haeq
    omega

private lemma fzc_sy3_conj_eq_mul (g x M : G) (h : g * x * g⁻¹ * x⁻¹ = M) :
    g * x * g⁻¹ = M * x := by
  have h1 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
  rw [h1, h]

private lemma fzc_sy3_image1 (hc : Commute x₁ x₂) {g : G} {a b : ℕ}
    (h : g * x₁ * g⁻¹ * x₁⁻¹ = x₁ ^ (2 * a) * x₂ ^ (2 * b)) :
    g * x₁ * g⁻¹ = x₁ ^ (2 * a + 1) * x₂ ^ (2 * b) := by
  rw [fzc_sy3_conj_eq_mul g x₁ _ h]
  have hm := fzc_sy3_mono_mul (x₁ := x₁) (x₂ := x₂) hc (2 * a) (2 * b) 1 0
  simpa using hm

private lemma fzc_sy3_image2 (hc : Commute x₁ x₂) {g : G} {a b : ℕ}
    (h : g * x₂ * g⁻¹ * x₂⁻¹ = x₁ ^ (2 * a) * x₂ ^ (2 * b)) :
    g * x₂ * g⁻¹ = x₁ ^ (2 * a) * x₂ ^ (2 * b + 1) := by
  rw [fzc_sy3_conj_eq_mul g x₂ _ h]
  have hm := fzc_sy3_mono_mul (x₁ := x₁) (x₂ := x₂) hc (2 * a) (2 * b) 0 1
  simpa using hm

theorem fzc_sy3_ax {g s e : G} (hc : x₁ * x₂ = x₂ * x₁) (h₁ : orderOf x₁ = 4)
    (h₂ : orderOf x₂ = 4) (hinf : zpowers x₁ ⊓ zpowers x₂ = ⊥) (hs₁ : s * x₁ * s⁻¹ = x₂)
    (hs₂ : s * x₂ * s⁻¹ = x₁) (hg₁ : g * x₁ * g⁻¹ * x₁⁻¹ ∈ fourGrp x₁ x₂)
    (hg₂ : g * x₂ * g⁻¹ * x₂⁻¹ ∈ fourGrp x₁ x₂)
    (hgs : g * x₂ * g⁻¹ * x₂⁻¹ = s * (g * x₁ * g⁻¹ * x₁⁻¹) * s⁻¹)
    (he : e ∈ baseGrp x₁ x₂) (he2 : e ^ 2 = (x₁ * x₂) ^ 2) (hge : g * e * g⁻¹ = e⁻¹) :
    (g * x₁ * g⁻¹ = x₁ ^ 3 ∧ g * x₂ * g⁻¹ = x₂ ^ 3) ∨
      (g * x₁ * g⁻¹ = x₁ * x₂ ^ 2 ∧ g * x₂ * g⁻¹ = x₁ ^ 2 * x₂) := by
  have hx₁ : x₁ ^ 4 = 1 := fzc_sy3_pow4 h₁
  have hx₂ : x₂ ^ 4 = 1 := fzc_sy3_pow4 h₂
  have hcom : Commute x₁ x₂ := hc
  obtain ⟨a, b, ha, hb, hM1⟩ := (fzc_sy3_mem_fourGrp hc h₁ h₂).mp hg₁
  obtain ⟨a', b', ha', hb', hM2⟩ := (fzc_sy3_mem_fourGrp hc h₁ h₂).mp hg₂
  have hx1 : g * x₁ * g⁻¹ = x₁ ^ (2 * a + 1) * x₂ ^ (2 * b) := fzc_sy3_image1 hcom hM1
  have hx2 : g * x₂ * g⁻¹ = x₁ ^ (2 * a') * x₂ ^ (2 * b' + 1) := fzc_sy3_image2 hcom hM2
  have hsM : s * (x₁ ^ (2 * a) * x₂ ^ (2 * b)) * s⁻¹ = x₂ ^ (2 * a) * x₁ ^ (2 * b) :=
    fzc_sy3_s_conj_mono s hs₁ hs₂ (2 * a) (2 * b)
  have hcomm : x₂ ^ (2 * a) * x₁ ^ (2 * b) = x₁ ^ (2 * b) * x₂ ^ (2 * a) :=
    (hcom.pow_pow (2 * b) (2 * a)).eq.symm
  have heq : x₁ ^ (2 * a') * x₂ ^ (2 * b') = x₁ ^ (2 * b) * x₂ ^ (2 * a) := by
    rw [← hM2, hgs, hM1, hsM, hcomm]
  have hab : a' = b ∧ b' = a := by
    have h := (fzc_sy3_coord_eq h₁ h₂ hinf).mp heq
    omega
  obtain ⟨hab1, hab2⟩ := hab
  have hx2' : g * x₂ * g⁻¹ = x₁ ^ (2 * b) * x₂ ^ (2 * a + 1) := by
    rw [← hab1, ← hab2]
    exact hx2
  obtain ⟨i, j, hi, hj, rfl⟩ := fzc_sy3_coord hc h₁ h₂ he
  have hij : x₁ ^ (i * 2) * x₂ ^ (j * 2) = x₁ ^ 2 * x₂ ^ 2 := by
    have hp := fzc_sy3_mono_pow (x₁ := x₁) (x₂ := x₂) hcom i j 2
    rw [hp, fzc_sy3_sq hcom] at he2
    exact he2
  have hodd : i % 2 = 1 ∧ j % 2 = 1 := by
    have h := (fzc_sy3_coord_eq h₁ h₂ hinf).mp hij
    omega
  have hge'' : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = x₁ ^ (3 * i) * x₂ ^ (3 * j) := by
    rw [hge, fzc_sy3_mono_inv hcom hx₁ hx₂]
  have hL : g * (x₁ ^ i * x₂ ^ j) * g⁻¹
      = x₁ ^ ((2 * a + 1) * i + 2 * b * j) * x₂ ^ (2 * b * i + (2 * a + 1) * j) := by
    rw [fzc_sy3_conj_mono, hx1, hx2', fzc_sy3_mono_pow hcom, fzc_sy3_mono_pow hcom,
      fzc_sy3_mono_mul hcom]
  have hge' : x₁ ^ ((2 * a + 1) * i + 2 * b * j) * x₂ ^ (2 * b * i + (2 * a + 1) * j)
      = x₁ ^ (3 * i) * x₂ ^ (3 * j) := by
    rw [← hL, hge'']
  have hcong := (fzc_sy3_coord_eq h₁ h₂ hinf).mp hge'
  interval_cases a <;> interval_cases b
  · exfalso; omega
  · right
    exact ⟨by simpa using hx1, by simpa using hx2'⟩
  · left
    exact ⟨by simpa using hx1, by simpa using hx2'⟩
  · exfalso; omega

theorem fzc_sy3_e2 {g s e : G} (hc : x₁ * x₂ = x₂ * x₁) (h₁ : orderOf x₁ = 4)
    (h₂ : orderOf x₂ = 4) (hinf : zpowers x₁ ⊓ zpowers x₂ = ⊥) (hs₁ : s * x₁ * s⁻¹ = x₂)
    (hs₂ : s * x₂ * s⁻¹ = x₁)
    (hg : (g * x₁ * g⁻¹ = x₁ ^ 3 ∧ g * x₂ * g⁻¹ = x₂ ^ 3) ∨
      (g * x₁ * g⁻¹ = x₁ * x₂ ^ 2 ∧ g * x₂ * g⁻¹ = x₁ ^ 2 * x₂))
    (he : e ∈ baseGrp x₁ x₂) (hfix : g * (s * e * s⁻¹) * g⁻¹ = e) :
    e ^ 2 * (g * e * g⁻¹ * e⁻¹) = 1 := by
  have hx₁ : x₁ ^ 4 = 1 := fzc_sy3_pow4 h₁
  have hx₂ : x₂ ^ 4 = 1 := fzc_sy3_pow4 h₂
  have hcom : Commute x₁ x₂ := hc
  obtain ⟨i, j, hi, hj, rfl⟩ := fzc_sy3_coord hc h₁ h₂ he
  have hse : s * (x₁ ^ i * x₂ ^ j) * s⁻¹ = x₂ ^ i * x₁ ^ j :=
    fzc_sy3_s_conj_mono s hs₁ hs₂ i j
  have hswap : x₂ ^ i * x₁ ^ j = x₁ ^ j * x₂ ^ i := (hcom.pow_pow j i).eq.symm
  rw [hse, hswap] at hfix
  rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
  ·
    have hge : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = x₁ ^ (3 * i) * x₂ ^ (3 * j) := by
      rw [fzc_sy3_conj_mono, hg1, hg2, ← pow_mul, ← pow_mul]
    have hinv : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = (x₁ ^ i * x₂ ^ j)⁻¹ := by
      rw [hge, fzc_sy3_mono_inv hcom hx₁ hx₂]
    rw [hinv]
    exact fzc_sy3_sq_inv (x₁ ^ i * x₂ ^ j)
  ·
    have hg1' : g * x₁ * g⁻¹ = x₁ ^ 1 * x₂ ^ 2 := by simpa using hg1
    have hg2' : g * x₂ * g⁻¹ = x₁ ^ 2 * x₂ ^ 1 := by simpa using hg2
    have hge : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = x₁ ^ (i + 2 * j) * x₂ ^ (2 * i + j) := by
      rw [fzc_sy3_conj_mono, hg1', hg2', fzc_sy3_mono_pow hcom, fzc_sy3_mono_pow hcom,
        fzc_sy3_mono_mul hcom]
      simp
    have hge2 : g * (x₁ ^ j * x₂ ^ i) * g⁻¹ = x₁ ^ (j + 2 * i) * x₂ ^ (2 * j + i) := by
      rw [fzc_sy3_conj_mono, hg1', hg2', fzc_sy3_mono_pow hcom, fzc_sy3_mono_pow hcom,
        fzc_sy3_mono_mul hcom]
      simp
    have hfix' : x₁ ^ (j + 2 * i) * x₂ ^ (2 * j + i) = x₁ ^ i * x₂ ^ j := by
      rw [← hge2, hfix]
    have hc2 := (fzc_sy3_coord_eq h₁ h₂ hinf).mp hfix'
    have hij4 : (i + j) % 4 = 0 := by omega
    rw [fzc_sy3_mono_pow hcom, hge, fzc_sy3_mono_inv hcom hx₁ hx₂]
    rw [fzc_sy3_mono_mul hcom, fzc_sy3_mono_mul hcom]
    rw [show (1 : G) = x₁ ^ 0 * x₂ ^ 0 by simp, fzc_sy3_coord_eq h₁ h₂ hinf]
    constructor <;> omega

theorem fzc_sy3_e0 {g s e : G} (hc : x₁ * x₂ = x₂ * x₁) (h₁ : orderOf x₁ = 4)
    (h₂ : orderOf x₂ = 4) (hinf : zpowers x₁ ⊓ zpowers x₂ = ⊥) (hs₁ : s * x₁ * s⁻¹ = x₂)
    (hs₂ : s * x₂ * s⁻¹ = x₁)
    (hg : (g * x₁ * g⁻¹ = x₁ ^ 3 ∧ g * x₂ * g⁻¹ = x₂ ^ 3) ∨
      (g * x₁ * g⁻¹ = x₁ * x₂ ^ 2 ∧ g * x₂ * g⁻¹ = x₁ ^ 2 * x₂))
    (he : e ∈ baseGrp x₁ x₂) (hz : g * e * g⁻¹ * e⁻¹ = (x₁ * x₂) ^ 2)
    (hse : s * e * s⁻¹ = e⁻¹) : e = x₁ * x₂ ^ 3 ∨ e = x₁ ^ 3 * x₂ := by
  have hx₁ : x₁ ^ 4 = 1 := fzc_sy3_pow4 h₁
  have hx₂ : x₂ ^ 4 = 1 := fzc_sy3_pow4 h₂
  have hcom : Commute x₁ x₂ := hc
  have hsq : (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := fzc_sy3_sq hcom
  obtain ⟨i, j, hi, hj, rfl⟩ := fzc_sy3_coord hc h₁ h₂ he
  have hse' : x₂ ^ i * x₁ ^ j = x₁ ^ (3 * i) * x₂ ^ (3 * j) := by
    rw [← fzc_sy3_s_conj_mono s hs₁ hs₂ i j, hse, fzc_sy3_mono_inv hcom hx₁ hx₂]
  have hsum : (i + j) % 4 = 0 := by
    have hswap : x₂ ^ i * x₁ ^ j = x₁ ^ j * x₂ ^ i := (hcom.pow_pow j i).eq.symm
    have heq : x₁ ^ j * x₂ ^ i = x₁ ^ (3 * i) * x₂ ^ (3 * j) := by
      rw [← hswap]
      exact hse'
    have h := (fzc_sy3_coord_eq h₁ h₂ hinf).mp heq
    omega
  rcases hg with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
  ·
    have hge : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = x₁ ^ (3 * i) * x₂ ^ (3 * j) := by
      rw [fzc_sy3_conj_mono, hg1, hg2, ← pow_mul, ← pow_mul]
    have hz' : x₁ ^ (3 * i + 3 * i) * x₂ ^ (3 * j + 3 * j) = x₁ ^ 2 * x₂ ^ 2 := by
      rw [← hsq, ← hz, hge, fzc_sy3_mono_inv hcom hx₁ hx₂, fzc_sy3_mono_mul hcom]
    have hc2 := (fzc_sy3_coord_eq h₁ h₂ hinf).mp hz'
    have hres : (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by omega
    rcases hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; simp
    · right; simp
  ·
    have hg1' : g * x₁ * g⁻¹ = x₁ ^ 1 * x₂ ^ 2 := by simpa using hg1
    have hg2' : g * x₂ * g⁻¹ = x₁ ^ 2 * x₂ ^ 1 := by simpa using hg2
    have hge : g * (x₁ ^ i * x₂ ^ j) * g⁻¹ = x₁ ^ (i + 2 * j) * x₂ ^ (2 * i + j) := by
      rw [fzc_sy3_conj_mono, hg1', hg2', fzc_sy3_mono_pow hcom, fzc_sy3_mono_pow hcom,
        fzc_sy3_mono_mul hcom]
      simp
    have hz' : x₁ ^ ((i + 2 * j) + 3 * i) * x₂ ^ ((2 * i + j) + 3 * j) = x₁ ^ 2 * x₂ ^ 2 := by
      rw [← hsq, ← hz, hge, fzc_sy3_mono_inv hcom hx₁ hx₂, fzc_sy3_mono_mul hcom]
    have hc2 := (fzc_sy3_coord_eq h₁ h₂ hinf).mp hz'
    have hres : (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) := by omega
    rcases hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; simp
    · right; simp

end CFSG.OddStandard.SmallF3.FritzII
