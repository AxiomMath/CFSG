module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuMask
public import Certificates.Data.GMS78RuSModelData

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS

namespace RuSModel

variable {G : Type} [Group G]

@[expose] def secN (ℓ : ℕ → G) (c : ℕ) : ℕ → G
  | 0 => 1
  | n + 1 => secN ℓ c n * (if c.testBit n then ℓ n else 1)

theorem secN_zero_left (ℓ : ℕ → G) (n : ℕ) : secN ℓ 0 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [secN, ih]

theorem secN_two_pow (ℓ : ℕ → G) (k n : ℕ) : secN ℓ (2 ^ k) n = if k < n then ℓ k else 1 := by
  induction n with
  | zero => simp [secN]
  | succ n ih =>
    simp only [secN, ih, Nat.testBit_two_pow]
    by_cases h : k = n
    · subst h
      simp
    · have h1 : (k < n + 1) = (k < n) := propext (by omega)
      simp [h, h1]

theorem sBasis_getD_lt (j : ℕ) : sBasis.getD j 0 < 256 := by
  rcases Nat.lt_or_ge j 8 with hj | hj
  · interval_cases j <;> decide
  · rw [List.getD_eq_default _ _ (by simpa [sBasis] using hj)]
    norm_num

theorem sMaskN_lt (c n : ℕ) : sMaskN c n < 256 := by
  induction n with
  | zero => simp [sMaskN]
  | succ n ih =>
    simp only [sMaskN]
    have h : (if c.testBit n then sBasis.getD n 0 else 0) < 2 ^ 8 := by
      split_ifs
      · exact sBasis_getD_lt n
      · norm_num
    exact Nat.xor_lt_two_pow (by simpa using ih) h

theorem cOf_sMask_check : (List.range 256).all (fun c => cOf (sMask c) == c) = true := by
  decide +kernel

theorem cOf_sMask {c : ℕ} (hc : c < 256) : cOf (sMask c) = c := by
  have h := cOf_sMask_check
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h c hc

theorem sMask_cOf_check : (List.range 256).all (fun m => sMask (cOf m) == m) = true := by
  decide +kernel

theorem sMask_cOf {m : ℕ} (hm : m < 256) : sMask (cOf m) = m := by
  have h := sMask_cOf_check
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h m hm

theorem cOf_lt (m : ℕ) : cOf m < 256 :=
  RuSimCode.maskApply_lt (by decide) m

end RuSModel

open RuSModel

namespace Sec3.SzR.MaskCoords

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  (hM : MaskCoords L T R μ ν)
include hM

section Section

variable {a : Fin 8 → G} (ha : ∀ t, a t ∈ gmsA L T) (hνa : ∀ t, ν (a t) = t)
include ha hνa

theorem sec_xor (s t : Fin 8) : a (s ^^^ t) = a s * a t :=
  hM.eq_of_ν_eq (ha _) (mul_mem (ha s) (ha t)) (by rw [hM.ν_mul _ (ha s) _ (ha t), hνa, hνa, hνa])

theorem sec_zero : a 0 = 1 :=
  hM.eq_of_ν_eq (ha 0) (one_mem _) (by rw [hνa, hM.ν_one])

omit hνa in
theorem sec_comm {x : G} (hx : x ∈ R) (t : Fin 8) : a t * x = x * a t :=
  (hM.central x hx (a t) (ha t)).symm

theorem mul_eq_sec_mul {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y = a (bC (μ x) (μ y)) * (y * x) := by
  have h : x * y * x⁻¹ * y⁻¹ = a (bC (μ x) (μ y)) :=
    hM.eq_of_ν_eq (hM.comm_mem _ hx _ hy) (ha _) (by rw [hM.comm hx hy, hνa])
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = a (bC (μ x) (μ y)) * (y * x) := by rw [h]

end Section

section Products

variable {ℓ : ℕ → G} (hℓ : ∀ j, ℓ j ∈ R)
include hℓ

omit hM in
theorem secN_mem (c n : ℕ) : secN ℓ c n ∈ R := by
  induction n with
  | zero => exact one_mem _
  | succ n ih =>
    refine mul_mem ih ?_
    split_ifs
    · exact hℓ n
    · exact one_mem _

theorem μ_secN (hℓμ : ∀ j < 8, μ (ℓ j) = sBasis.getD j 0) (c : ℕ) {n : ℕ} (hn : n ≤ 8) :
    μ (secN ℓ c n) = sMaskN c n := by
  induction n with
  | zero => exact (hM.ker _ (one_mem _)).mpr (one_mem _)
  | succ n ih =>
    have hf : (if c.testBit n then ℓ n else 1) ∈ R := by
      split_ifs
      · exact hℓ n
      · exact one_mem _
    rw [secN, hM.mul _ (secN_mem hℓ c n) _ hf, ih (by omega), sMaskN]
    congr 1
    split_ifs
    · exact hℓμ n (by omega)
    · exact (hM.ker _ (one_mem _)).mpr (one_mem _)

variable {a : Fin 8 → G} (ha : ∀ t, a t ∈ gmsA L T) (hνa : ∀ t, ν (a t) = t)
include ha hνa

theorem secN_mul (hℓμ : ∀ j < 8, μ (ℓ j) = sBasis.getD j 0) (hℓ2 : ∀ j, ℓ j * ℓ j = 1)
    (c c' : ℕ) {n : ℕ} (hn : n ≤ 8) :
    secN ℓ c n * secN ℓ c' n = secN ℓ (c ^^^ c') n * a (gamN c c' n) := by
  induction n with
  | zero => simp [secN, gamN, hM.sec_zero ha hνa]
  | succ n ih =>
    have ih := ih (by omega)
    have hP' : secN ℓ c' n ∈ R := secN_mem hℓ c' n
    have hmove : ℓ n * secN ℓ c' n =
        secN ℓ c' n * ℓ n * a (bC (sBasis.getD n 0) (sMaskN c' n)) := by
      rw [hM.mul_eq_sec_mul ha hνa (hℓ n) hP', hℓμ n (by omega), hM.μ_secN hℓ hℓμ c' (by omega),
        hM.sec_comm ha (mul_mem hP' (hℓ n))]
    have hcomm : ∀ t, a t * ℓ n = ℓ n * a t := hM.sec_comm ha (hℓ n)
    simp only [secN, gamN, Nat.testBit_xor]
    rw [hM.sec_xor ha hνa]
    generalize secN ℓ c n = P at ih ⊢
    generalize secN ℓ c' n = P' at ih hmove ⊢
    generalize secN ℓ (c ^^^ c') n = Q at ih ⊢
    generalize bC (sBasis.getD n 0) (sMaskN c' n) = β at hmove ⊢
    cases c.testBit n <;> cases c'.testBit n <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true, Bool.not_false,
        Bool.not_true, mul_one, hM.sec_zero ha hνa]
    · exact ih
    · rw [← mul_assoc, ih, mul_assoc, hcomm, ← mul_assoc]
    · calc P * ℓ n * P' = P * (ℓ n * P') := by rw [mul_assoc]
        _ = P * P' * ℓ n * a β := by rw [hmove]; simp only [mul_assoc]
        _ = Q * a (gamN c c' n) * ℓ n * a β := by rw [ih]
        _ = Q * ℓ n * (a (gamN c c' n) * a β) := by
          rw [mul_assoc Q, hcomm]
          simp only [mul_assoc]
    · calc P * ℓ n * (P' * ℓ n) = P * (ℓ n * P') * ℓ n := by simp only [mul_assoc]
        _ = P * P' * (ℓ n * (a β * ℓ n)) := by rw [hmove]; simp only [mul_assoc]
        _ = Q * a (gamN c c' n) * (ℓ n * ℓ n * a β) := by
          rw [ih, hcomm β]
          simp only [mul_assoc]
        _ = Q * (a (gamN c c' n) * a β) := by rw [hℓ2 n, one_mul, mul_assoc]

theorem sec_mul (hℓμ : ∀ j < 8, μ (ℓ j) = sBasis.getD j 0) (hℓ2 : ∀ j, ℓ j * ℓ j = 1)
    (c c' : ℕ) : secN ℓ c 8 * secN ℓ c' 8 = secN ℓ (c ^^^ c') 8 * a (gam c c') :=
  hM.secN_mul hℓ ha hνa hℓμ hℓ2 c c' le_rfl

theorem conj_secN (hℓμ : ∀ j < 8, μ (ℓ j) = sBasis.getD j 0) (hℓ2 : ∀ j, ℓ j * ℓ j = 1)
    {D : G} {d : Fin 8} (hD : ∀ j < 8, D * ℓ j * D⁻¹ = ℓ (dMul d (fin8Of j)).val) (c : ℕ)
    {n : ℕ} (hn : n ≤ 8) :
    D * secN ℓ c n * D⁻¹ = secN ℓ (dPartN d c n).1 8 * a (dPartN d c n).2 := by
  induction n with
  | zero => simp [secN, dPartN, hM.sec_zero ha hνa]
  | succ n ih =>
    have ih := ih (by omega)
    rw [show secN ℓ c (n + 1) = secN ℓ c n * (if c.testBit n then ℓ n else 1) from rfl,
      show dPartN d c (n + 1) = if c.testBit n then
        ((dPartN d c n).1 ^^^ 2 ^ (dMul d (fin8Of n)).val,
          (dPartN d c n).2 ^^^ gam (dPartN d c n).1 (2 ^ (dMul d (fin8Of n)).val))
        else dPartN d c n from rfl]
    split_ifs with hc
    · have hk : (dMul d (fin8Of n)).val < 8 := (dMul d (fin8Of n)).isLt
      have hℓk : ℓ (dMul d (fin8Of n)).val = secN ℓ (2 ^ (dMul d (fin8Of n)).val) 8 := by
        rw [secN_two_pow, ite_eq_left_iff.mpr (fun h => absurd hk h)]
      calc D * (secN ℓ c n * ℓ n) * D⁻¹ = (D * secN ℓ c n * D⁻¹) * (D * ℓ n * D⁻¹) := by group
        _ = secN ℓ (dPartN d c n).1 8 * a (dPartN d c n).2 *
            secN ℓ (2 ^ (dMul d (fin8Of n)).val) 8 := by rw [ih, hD n (by omega), hℓk]
        _ = secN ℓ (dPartN d c n).1 8 * secN ℓ (2 ^ (dMul d (fin8Of n)).val) 8 *
            a (dPartN d c n).2 := by
          rw [mul_assoc, hM.sec_comm ha (secN_mem hℓ _ 8), ← mul_assoc]
        _ = secN ℓ ((dPartN d c n).1 ^^^ 2 ^ (dMul d (fin8Of n)).val) 8 *
            a ((dPartN d c n).2 ^^^ gam (dPartN d c n).1 (2 ^ (dMul d (fin8Of n)).val)) := by
          rw [hM.sec_mul hℓ ha hνa hℓμ hℓ2, hM.sec_xor ha hνa, mul_assoc,
            hM.sec_comm ha (hM.le (ha (dPartN d c n).2))]
    · rw [mul_one]
      exact ih

end Products

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
