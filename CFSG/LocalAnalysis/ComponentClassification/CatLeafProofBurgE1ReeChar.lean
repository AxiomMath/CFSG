module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

@[expose] def zpowChar (K : Type*) [Field K] (m : ℤ) : Kˣ →* K :=
  (Units.coeHom K).comp (zpowGroupHom m)

theorem zpowChar_apply {K : Type*} [Field K] (m : ℤ) (s : Kˣ) :
    zpowChar K m s = ((s ^ m : Kˣ) : K) :=
  rfl

theorem dvd_sub_of_zpowChar_eq {K : Type*} [Field K] [Finite K] {m m' : ℤ}
    (h : zpowChar K m = zpowChar K m') : ((Nat.card K - 1 : ℕ) : ℤ) ∣ m - m' := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have h1 : γ ^ m = γ ^ m' := Units.ext (DFunLike.congr_fun h γ)
  rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hγ]
  exact orderOf_dvd_iff_zpow_eq_one.2 (by rw [zpow_sub, h1, mul_inv_cancel])

theorem exists_comp_eq_of_sum_eq {G L : Type*} [Group G] [Field L] {m : ℕ} (σ : L ≃+* L)
    (χ : Fin m → G →* L) (hχ : Function.Injective χ)
    (h : ∀ x, ∑ k, σ (χ k x) = ∑ k, χ k x) (k : Fin m) :
    ∃ l, σ.toMonoidHom.comp (χ k) = χ l := by
  classical
  by_contra hne'
  have hne : ∀ l, σ.toMonoidHom.comp (χ k) ≠ χ l := fun l hl => hne' ⟨l, hl⟩
  have hχ' : Function.Injective fun k => σ.toMonoidHom.comp (χ k) := fun k l hkl =>
    hχ (MonoidHom.ext fun x => σ.injective (DFunLike.congr_fun hkl x))
  set A := Finset.univ.image fun k => σ.toMonoidHom.comp (χ k) with hAdef
  set B := Finset.univ.image χ with hBdef
  have hA : σ.toMonoidHom.comp (χ k) ∈ A := Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hB : σ.toMonoidHom.comp (χ k) ∉ B := by
    rw [hBdef, Finset.mem_image]
    rintro ⟨l, -, hl⟩
    exact hne l hl.symm
  have hsum : ∑ ψ ∈ A ∪ B, ((if ψ ∈ A then (1 : L) else 0) - (if ψ ∈ B then 1 else 0)) •
      (ψ : G → L) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, ite_mul, one_mul,
      zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
      Finset.union_inter_cancel_right, Pi.zero_apply]
    rw [hAdef, hBdef, Finset.sum_image hχ'.injOn, Finset.sum_image hχ.injOn]
    exact sub_eq_zero.2 (h x)
  have h0 : (if σ.toMonoidHom.comp (χ k) ∈ A then (1 : L) else 0) -
      (if σ.toMonoidHom.comp (χ k) ∈ B then 1 else 0) = 0 :=
    linearIndependent_iff'.1 (linearIndependent_monoidHom G L) (A ∪ B) _ hsum _
      (Finset.mem_union_left _ hA)
  simp only [hA, hB, ↓reduceIte, sub_zero] at h0
  exact one_ne_zero h0

@[expose] def g2TorusExpM0 : Fin 12 → ℤ := ![2, -1, -2, -1, 1, 1, 1, 1, 0, -1, -1, 0]

@[expose] def g2TorusExpM1 : Fin 12 → ℤ := ![-3, 2, 3, 3, -1, -2, -3, 0, 1, 1, 0, -1]

@[expose] def g2TorusExp (θ : ℤ) (k : Fin 12) : ℤ := g2TorusExpM0 k + θ * g2TorusExpM1 k

theorem g2TorusExp_seven (θ : ℤ) : g2TorusExp θ 7 = 1 := by
  rw [g2TorusExp, show g2TorusExpM0 7 = 1 from rfl, show g2TorusExpM1 7 = 0 from rfl]
  ring

theorem g2TorusExp_eight (θ : ℤ) : g2TorusExp θ 8 = θ := by
  rw [g2TorusExp, show g2TorusExpM0 8 = 0 from rfl, show g2TorusExpM1 8 = 1 from rfl]
  ring

theorem g2TorusExp_facts : ∀ k : Fin 12,
    -2 ≤ g2TorusExpM0 k ∧ g2TorusExpM0 k ≤ 2 ∧ -3 ≤ g2TorusExpM1 k ∧ g2TorusExpM1 k ≤ 3 ∧
      (g2TorusExpM1 k ≠ 3 ∨ g2TorusExpM0 k ≤ -1) ∧ (g2TorusExpM1 k ≠ -3 ∨ 1 ≤ g2TorusExpM0 k) := by
  decide +kernel

theorem g2TorusExp_pair_facts : ∀ k l : Fin 12,
    (g2TorusExpM0 k - g2TorusExpM0 l = 0 → g2TorusExpM1 k - g2TorusExpM1 l = 0 → k = l) ∧
    ¬ (g2TorusExpM1 k - g2TorusExpM1 l = -1 ∧
      (g2TorusExpM0 k - g2TorusExpM0 l = 3 ∨ g2TorusExpM0 k - g2TorusExpM0 l = 4)) ∧
    ¬ (g2TorusExpM1 k - g2TorusExpM1 l = 1 ∧
      (g2TorusExpM0 k - g2TorusExpM0 l = -3 ∨ g2TorusExpM0 k - g2TorusExpM0 l = -4)) := by
  decide +kernel

theorem g2TorusExp_abs_le {θ : ℤ} (hθ : 3 ≤ θ) (k : Fin 12) :
    -(3 * θ - 1) ≤ g2TorusExp θ k ∧ g2TorusExp θ k ≤ 3 * θ - 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2TorusExp_facts k
  rw [g2TorusExp]
  generalize g2TorusExpM0 k = u at *
  generalize g2TorusExpM1 k = v at *
  interval_cases v <;> omega

theorem eq_of_dvd_g2TorusExp_sub {θ : ℤ} (hθ : 3 ≤ θ) {k l : Fin 12}
    (h : 3 * θ ^ 2 - 1 ∣ g2TorusExp θ k - g2TorusExp θ l) : k = l := by
  have hT : 3 * θ ≤ θ ^ 2 := by nlinarith
  obtain ⟨hk1, hk2⟩ := g2TorusExp_abs_le hθ k
  obtain ⟨hl1, hl2⟩ := g2TorusExp_abs_le hθ l
  have hz := Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
  obtain ⟨h0, h1, h2⟩ := g2TorusExp_pair_facts k l
  obtain ⟨a1, a2, -⟩ := g2TorusExp_facts k
  obtain ⟨b1, b2, -⟩ := g2TorusExp_facts l
  rw [g2TorusExp, g2TorusExp] at hz
  have hd : (g2TorusExpM0 k - g2TorusExpM0 l) + θ * (g2TorusExpM1 k - g2TorusExpM1 l) = 0 := by
    linear_combination hz
  have hb : -4 ≤ g2TorusExpM0 k - g2TorusExpM0 l ∧ g2TorusExpM0 k - g2TorusExpM0 l ≤ 4 := by omega
  generalize g2TorusExpM0 k - g2TorusExpM0 l = d0 at hd hb h0 h1 h2
  generalize g2TorusExpM1 k - g2TorusExpM1 l = d1 at hd h0 h1 h2
  rcases lt_trichotomy d1 0 with hn | hz' | hp
  · have e1 : d1 = -1 := by
      by_contra hne
      have hle : d1 ≤ -2 := by omega
      nlinarith [mul_nonneg (sub_nonneg.2 hθ) (by linarith : (0 : ℤ) ≤ -2 - d1)]
    subst e1
    exact absurd ⟨rfl, by omega⟩ h1
  · subst hz'
    exact h0 (by linarith) rfl
  · have e1 : d1 = 1 := by
      by_contra hne
      have hle : 2 ≤ d1 := by omega
      nlinarith [mul_nonneg (sub_nonneg.2 hθ) (by linarith : (0 : ℤ) ≤ d1 - 2)]
    subst e1
    exact absurd ⟨rfl, by omega⟩ h2

theorem not_dvd_sq_sub_g2TorusExp {θ : ℤ} (hθ : 3 ≤ θ) (l : Fin 12) :
    ¬ 3 * θ ^ 2 - 1 ∣ θ ^ 2 - g2TorusExp θ l := by
  intro h
  have hT : 3 * θ ≤ θ ^ 2 := by nlinarith
  obtain ⟨h1, h2⟩ := g2TorusExp_abs_le hθ l
  have hz := Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
  omega

theorem not_dvd_pow_sub_g2TorusExp {θ N : ℤ} (hθ : 3 ≤ θ)
    (hN : (3 ≤ N ∧ 3 * N ≤ θ) ∨ (3 * θ ≤ N ∧ N ≤ θ ^ 2)) (l : Fin 12) :
    ¬ 3 * θ ^ 2 - 1 ∣ N - g2TorusExp θ l := by
  intro h
  have hT : 3 * θ ≤ θ ^ 2 := by nlinarith
  obtain ⟨h1, h2⟩ := g2TorusExp_abs_le hθ l
  have hz := Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := g2TorusExp_facts l
  rw [g2TorusExp] at hz
  generalize g2TorusExpM0 l = u at *
  generalize g2TorusExpM1 l = v at *
  interval_cases v <;> omega

theorem pow_three_bounds_of_ne {a n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 2 * a) (hna : n ≠ a) :
    (3 ≤ (3 : ℤ) ^ n ∧ 3 * (3 : ℤ) ^ n ≤ 3 ^ a) ∨
      (3 * (3 : ℤ) ^ a ≤ 3 ^ n ∧ (3 : ℤ) ^ n ≤ ((3 : ℤ) ^ a) ^ 2) := by
  rcases lt_or_gt_of_ne hna with h | h
  · left
    refine ⟨?_, ?_⟩
    · calc (3 : ℤ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) h1
    · calc 3 * (3 : ℤ) ^ n = 3 ^ (n + 1) := by ring
        _ ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) (by omega)
  · right
    refine ⟨?_, ?_⟩
    · calc 3 * (3 : ℤ) ^ a = 3 ^ (a + 1) := by ring
        _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    · calc (3 : ℤ) ^ n ≤ 3 ^ (2 * a) := pow_le_pow_right₀ (by norm_num) h2
        _ = ((3 : ℤ) ^ a) ^ 2 := by ring

theorem g2TorusExp_frobenius_absurd {K : Type*} [Field K] [Finite K] {a n : ℕ}
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (hn : n < 2 * a + 1) (hn0 : n ≠ 0) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 3 ^ n)
    (h : ∀ s : Kˣ, ∑ k, σ (zpowChar K (g2TorusExp (3 ^ a) k) s) =
      ∑ k, zpowChar K (g2TorusExp (3 ^ a) k) s) : False := by
  have ha : 1 ≤ a := by omega
  have hθ : (3 : ℤ) ≤ 3 ^ a := by
    calc (3 : ℤ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) ha
  have hQ : ((Nat.card K - 1 : ℕ) : ℤ) = 3 * ((3 : ℤ) ^ a) ^ 2 - 1 := by
    have h1 : 1 ≤ 3 ^ (2 * a + 1) := Nat.one_le_pow _ _ (by norm_num)
    rw [hK]
    push_cast [Nat.cast_sub h1]
    ring
  have hχ : Function.Injective fun k => zpowChar K (g2TorusExp (3 ^ a) k) := fun k l hkl =>
    eq_of_dvd_g2TorusExp_sub hθ (by rw [← hQ]; exact dvd_sub_of_zpowChar_eq hkl)
  have hcomp : ∀ m : ℤ, σ.toMonoidHom.comp (zpowChar K m) = zpowChar K (3 ^ n * m) := by
    intro m
    refine MonoidHom.ext fun s => ?_
    show σ ((s ^ m : Kˣ) : K) = ((s ^ ((3 : ℤ) ^ n * m) : Kˣ) : K)
    rw [hσ, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    congr 2
    push_cast
    ring
  have key : ∀ k₀ : Fin 12, ∃ l,
      3 * ((3 : ℤ) ^ a) ^ 2 - 1 ∣ 3 ^ n * g2TorusExp (3 ^ a) k₀ - g2TorusExp (3 ^ a) l := by
    intro k₀
    obtain ⟨l, hl⟩ := exists_comp_eq_of_sum_eq σ _ hχ h k₀
    have hl' : zpowChar K (3 ^ n * g2TorusExp (3 ^ a) k₀) = zpowChar K (g2TorusExp (3 ^ a) l) := by
      rw [← hcomp]
      exact hl
    exact ⟨l, by rw [← hQ]; exact dvd_sub_of_zpowChar_eq hl'⟩
  by_cases hna : n = a
  · obtain ⟨l, hl⟩ := key 8
    rw [g2TorusExp_eight, hna, ← sq] at hl
    exact not_dvd_sq_sub_g2TorusExp hθ l hl
  · obtain ⟨l, hl⟩ := key 7
    rw [g2TorusExp_seven, mul_one] at hl
    exact not_dvd_pow_sub_g2TorusExp hθ (pow_three_bounds_of_ne (by omega) (by omega) hna) l hl

end CFSG.ComponentClassification.CatLeafProof
