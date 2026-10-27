module

import all CFSG.Fischer.F4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LargeExtraspecial.Asc611I

open CFSG.Fischer CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

structure IsSesq (S : (Fin m → K) → (Fin m → K) → K) : Prop where
  add_left : ∀ x x' y, S (x + x') y = S x y + S x' y
  add_right : ∀ x y y', S x (y + y') = S x y + S x y'
  smul_left : ∀ (c : K) x y, S (c • x) y = frob c * S x y
  smul_right : ∀ (c : K) x y, S x (c • y) = c * S x y

theorem eF4_eq_zero {x : F4} : eF4 x = 0 ↔ x = 0 := map_eq_zero_iff _ eF4.injective

theorem three_lambda {A B c : K} (h : ∀ l : K, l ≠ 0 → c + l * A + frob l * B = 0) :
    A = 0 ∧ B = 0 ∧ c = 0 := by
  obtain ⟨A', rfl⟩ := eF4.surjective A
  obtain ⟨B', rfl⟩ := eF4.surjective B
  obtain ⟨c', rfl⟩ := eF4.surjective c
  have key : ∀ l : F4, l ≠ 0 → c' + l * A' + l ^ 2 * B' = 0 := by
    intro l hl
    have := h (eF4 l) (by rwa [Ne, eF4_eq_zero])
    rwa [frob_eF4, ← map_mul, ← map_mul, ← map_add, ← map_add, eF4_eq_zero] at this
  have hdec : ∀ a b c : Fin 4,
      (∀ l : Fin 4, l ≠ 0 → (⟨c⟩ : F4) + ⟨l⟩ * ⟨a⟩ + (⟨l⟩ : F4) ^ 2 * ⟨b⟩ = ⟨0⟩) →
      a = 0 ∧ b = 0 ∧ c = 0 := by decide
  have h0 : ∀ x : F4, x.code = 0 → x = 0 := fun x hx => by cases x; subst hx; rfl
  obtain ⟨h1, h2, h3⟩ := hdec A'.code B'.code c'.code (fun l hl => key ⟨l⟩ (by
    intro h; apply hl; have := congrArg F4.code h; exact this))
  replace h1 := h0 _ h1
  replace h2 := h0 _ h2
  replace h3 := h0 _ h3
  exact ⟨by rw [h1, map_zero], by rw [h2, map_zero], by rw [h3, map_zero]⟩

namespace IsSesq

variable {S : (Fin m → K) → (Fin m → K) → K} (hS : IsSesq S)
include hS

theorem sub_right (x y y' : Fin m → K) : S x (y - y') = S x y - S x y' := by
  have := hS.add_right x (y - y') y'
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem expand (a b : Fin m → K) (l : K) :
    S (a + l • b) (a + l • b) =
      S a a + l * S a b + frob l * S b a + frob l * l * S b b := by
  rw [hS.add_left, hS.add_right, hS.add_right, hS.smul_left, hS.smul_left, hS.smul_right,
    hS.smul_right]
  ring

theorem expand_add (x z : Fin m → K) :
    S (x + z) (x + z) = S x x + S x z + S z x + S z z := by
  rw [hS.add_left, hS.add_right, hS.add_right]
  ring

theorem eq_zero_of_diag (h : ∀ a, S a a = 0) (a b : Fin m → K) : S a b = 0 := by
  have h1 := hS.expand_add a b
  have h2 := hS.expand a b ω
  rw [h, h, h, add_zero, zero_add] at h1
  simp only [h, mul_zero, add_zero, zero_add, frob_omega] at h2
  linear_combination -(1 + ω) * h1 + h2

theorem expand2 (α β : K) (q y : Fin m → K) :
    S (α • q + β • y) (α • q + β • y) = frob α * α * S q q + frob α * β * S q y +
      frob β * α * S y q + frob β * β * S y y := by
  rw [hS.add_left, hS.add_right, hS.add_right, hS.smul_left, hS.smul_left, hS.smul_left,
    hS.smul_left, hS.smul_right, hS.smul_right, hS.smul_right, hS.smul_right]
  ring

theorem cross_left (α β : K) (x q y : Fin m → K) :
    S x (α • q + β • y) = α * S x q + β * S x y := by
  rw [hS.add_right, hS.smul_right, hS.smul_right]

theorem cross_right (α β : K) (x q y : Fin m → K) :
    S (α • q + β • y) x = frob α * S q x + frob β * S y x := by
  rw [hS.add_left, hS.smul_left, hS.smul_left]

end IsSesq

section Herm

variable {H S : (Fin m → K) → (Fin m → K) → K} (hH : IsSesq H)
  (hHc : ∀ x y, H y x = frob (H x y))
include hH hHc

omit hH in
theorem herm_self_eq (x : Fin m → K) : H x x = 0 ∨ H x x = 1 :=
  (frob_eq_self_iff _).mp (hHc x x).symm

variable (hS : IsSesq S) (hS0 : ∀ a, H a a = 0 → S a a = 0)
include hS hS0

theorem orth_pair {a b : Fin m → K} (ha : H a a = 1) (hb : H b b = 1) (hab : H a b = 0) :
    S a b = 0 ∧ S b a = 0 ∧ S a a = S b b := by
  have hba : H b a = 0 := by rw [hHc, hab, map_zero]
  have key : ∀ l : K, l ≠ 0 → (S a a + S b b) + l * S a b + frob l * S b a = 0 := by
    intro l hl
    have hiso : H (a + l • b) (a + l • b) = 0 := by
      rw [hH.expand, ha, hb, hab, hba, frob_mul_self hl]
      simp only [mul_zero, add_zero, one_mul]
      exact add_self_K 1
    have := hS0 _ hiso
    rw [hS.expand, frob_mul_self hl, one_mul] at this
    linear_combination this
  obtain ⟨h1, h2, h3⟩ := three_lambda key
  exact ⟨h1, h2, by linear_combination h3 - S b b * two_eq_zero⟩

theorem cross_eq_zero {q y a : Fin m → K} (hq : H q q = 1) (hy : H y y = 1)
    (hqy : H q y = 0) (haq : H q a = 0) (hay : H y a = 0) : S a q = 0 ∧ S q a = 0 := by
  have hqa : H a q = 0 := by rw [hHc, haq, map_zero]
  rcases herm_self_eq hHc a with ha | ha
  · have hya : H a y = 0 := by rw [hHc, hay, map_zero]
    have hyq : H y q = 0 := by rw [hHc, hqy, map_zero]
    obtain ⟨hqy', hyq', -⟩ := orth_pair hH hHc hS hS0 hq hy hqy
    set b := a + y with hb
    have hbb : H b b = 1 := by
      rw [hb, hH.expand_add, ha, hay, hya, hy]; simp
    have hbq : H b q = 0 := by rw [hb, hH.add_left, hqa, hyq, add_zero]
    have hqb : H q b = 0 := by rw [hHc, hbq, map_zero]
    have key : ∀ l : K, l ≠ 0 → (S b b + S q q) + l * S b q + frob l * S q b = 0 := by
      intro l hl
      have hiso : H (b + l • q) (b + l • q) = 0 := by
        rw [hH.expand, hbb, hq, hbq, hqb, frob_mul_self hl]
        simp only [mul_zero, add_zero, one_mul]
        exact add_self_K 1
      have := hS0 _ hiso
      rw [hS.expand, frob_mul_self hl, one_mul] at this
      linear_combination this
    obtain ⟨h1, h2, -⟩ := three_lambda key
    constructor
    · have := hS.add_left a y q
      rw [← hb, h1, hyq'] at this
      linear_combination -this
    · have := hS.add_right q a y
      rw [← hb, h2, hqy'] at this
      linear_combination -this
  · obtain ⟨h1, h2, -⟩ := orth_pair hH hHc hS hS0 ha hq hqa
    exact ⟨h1, h2⟩

theorem eq_smul_of_isotropic {q y : Fin m → K} (hq : H q q = 1) (hy : H y y = 1)
    (hqy : H q y = 0) (a b : Fin m → K) : S a b = S q q * H a b := by
  set μ := S q q with hμ
  have hT : IsSesq (fun x z => S x z - μ * H x z) :=
    { add_left := fun x x' z => by simp only [hS.add_left, hH.add_left]; ring
      add_right := fun x z z' => by simp only [hS.add_right, hH.add_right]; ring
      smul_left := fun c x z => by simp only [hS.smul_left, hH.smul_left]; ring
      smul_right := fun c x z => by simp only [hS.smul_right, hH.smul_right]; ring }
  have hyq : H y q = 0 := by rw [hHc, hqy, map_zero]
  obtain ⟨hSqy, hSyq, hSqq⟩ := orth_pair hH hHc hS hS0 hq hy hqy
  have hdiag : ∀ x, S x x - μ * H x x = 0 := by
    intro x
    set α := H q x
    set β := H y x
    set x' := x - (α • q + β • y) with hx'
    have hxx : x = x' + (α • q + β • y) := by rw [hx', sub_add_cancel]
    have hqx' : H q x' = 0 := by
      rw [hx', hH.sub_right, hH.cross_left, hq, hqy]; ring
    have hyx' : H y x' = 0 := by
      rw [hx', hH.sub_right, hH.cross_left, hyq, hy]; ring
    obtain ⟨c1, c2⟩ := cross_eq_zero hH hHc hS hS0 hq hy hqy hqx' hyx'
    obtain ⟨c3, c4⟩ := cross_eq_zero hH hHc hS hS0 hy hq hyq hyx' hqx'
    have hHqx : H x' q = 0 := by rw [hHc, hqx', map_zero]
    have hHyx : H x' y = 0 := by rw [hHc, hyx', map_zero]
    have hS' : S x' x' = μ * H x' x' := by
      rcases herm_self_eq hHc x' with h0 | h1
      · rw [hS0 _ h0, h0, mul_zero]
      · rw [h1, mul_one, hμ, (orth_pair hH hHc hS hS0 h1 hq hHqx).2.2]
    rw [hxx, hS.expand_add, hH.expand_add, hS.cross_left, hS.cross_right, hS.expand2,
      hH.cross_left, hH.cross_right, hH.expand2, c1, c2, c3, c4, hSqy, hSyq, ← hSqq, hS',
      hHqx, hHyx, hqx', hyx', hq, hy, hqy, hyq]
    ring
  have := hT.eq_zero_of_diag hdiag a b
  linear_combination this

end Herm

theorem linear_eq_zero_of_isotropic {H : (Fin m → K) → (Fin m → K) → K} (hH : IsSesq H)
    (hHc : ∀ x y, H y x = frob (H x y)) {f : (Fin m → K) → K}
    (hfa : ∀ x z, f (x + z) = f x + f z) (hfs : ∀ (c : K) x, f (c • x) = c * f x)
    (h0 : ∀ a, H a a = 0 → f a = 0) {q y : Fin m → K} (hq : H q q = 1) (hy : H y y = 1)
    (hqy : H q y = 0) (x : Fin m → K) : f x = 0 := by
  have hyq : H y q = 0 := by rw [hHc, hqy, map_zero]
  have key : ∀ l : K, l ≠ 0 → f q + l * f y + frob l * 0 = 0 := by
    intro l hl
    have hiso : H (q + l • y) (q + l • y) = 0 := by
      rw [hH.expand, hq, hy, hqy, hyq, frob_mul_self hl]
      simp only [mul_zero, add_zero, one_mul]
      exact add_self_K 1
    rw [mul_zero, add_zero, ← hfs, ← hfa]
    exact h0 _ hiso
  obtain ⟨hfy, -, hfq⟩ := three_lambda key
  set α := H q x
  set β := H y x
  set x' := x - (α • q + β • y) with hx'
  have hxx : x = x' + (α • q + β • y) := by rw [hx', sub_add_cancel]
  have hqx' : H q x' = 0 := by rw [hx', hH.sub_right, hH.cross_left, hq, hqy]; ring
  have hfx' : f x' = 0 := by
    rcases herm_self_eq hHc x' with h0' | h1
    · exact h0 _ h0'
    · have hHqx : H x' q = 0 := by rw [hHc, hqx', map_zero]
      have key' : ∀ l : K, l ≠ 0 → f x' + l * f q + frob l * 0 = 0 := by
        intro l hl
        have hiso : H (x' + l • q) (x' + l • q) = 0 := by
          rw [hH.expand, h1, hq, hHqx, hqx', frob_mul_self hl]
          simp only [mul_zero, add_zero, one_mul]
          exact add_self_K 1
        rw [mul_zero, add_zero, ← hfs, ← hfa]
        exact h0 _ hiso
      exact (three_lambda key').2.2
  rw [hxx, hfa, hfa, hfs, hfs, hfx', hfq, hfy, mul_zero, mul_zero, add_zero, add_zero]

end CFSG.LargeExtraspecial.Asc611I
