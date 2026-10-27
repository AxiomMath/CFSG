module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Singer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix

theorem two_pow_mod_fifteen (v : ℕ) : 2 ^ v % 15 = 1 ∨ 2 ^ v % 15 = 2 ∨ 2 ^ v % 15 = 4 ∨
    2 ^ v % 15 = 8 := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h | h | h <;> simp [h]

section

variable {G : Type*} [Group G] [Finite G] {L A : Subgroup G}

theorem exists_singer_coord (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hsq : ∀ x ∈ A, x ^ 2 = 1) (hcard : Nat.card A = 16)
    (hsurj : ∀ f : G → G, (∀ a ∈ A, f a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
      (∀ a ∈ A, ∀ b ∈ A, f a = f b → a = b) → ∃ n ∈ L, ∀ a ∈ A, n * a * n⁻¹ = f a) :
    ∃ (k : G) (c : G → (Fin 4 → ZMod 2)) (j : ℕ), k ∈ L ∧ (∀ x ∈ A, k * x * k⁻¹ ∈ A) ∧
      Odd (orderOf k) ∧ (∀ x ∈ A, k * x * k⁻¹ = x → x = 1) ∧
      (j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 8) ∧ (∀ a ∈ A, ∀ b ∈ A, c (a * b) = c a + c b) ∧
      (∀ a ∈ A, ∀ b ∈ A, c a = c b → a = b) ∧ (∀ u, ∃ a ∈ A, c a = u) ∧
      (∀ a ∈ A, c (k * a * k⁻¹) = (singerMat ^ j) *ᵥ c a) := by
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hV : ∀ x : Additive ↥A, 2 • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ : ∃ a : ↥A, Additive.ofMul a = x := ⟨Additive.toMul x, rfl⟩
    rw [← ofMul_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hsq a a.2)
    rw [this]
    rfl
  let _ : Module (ZMod 2) (Additive ↥A) := AddCommGroup.zmodModule hV
  have _ : Module.Finite (ZMod 2) (Additive ↥A) := Module.Finite.of_finite
  have h4 : Module.finrank (ZMod 2) (Additive ↥A) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥A)
    have hc : Nat.card (Additive ↥A) = 16 := hcard
    rw [hc, Nat.card_zmod] at h
    have h' : 2 ^ Module.finrank (ZMod 2) (Additive ↥A) = 2 ^ 4 := h.symm.trans (by norm_num)
    exact Nat.pow_right_injective (le_refl 2) h'
  let e : Additive ↥A ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h4, Module.finrank_fin_fun])
  let actA : ℕ → ↥A → ↥A := fun j a =>
    Additive.toMul (e.symm ((singerMat ^ j).mulVec (e (Additive.ofMul a))))
  have hactA_vec : ∀ j a, e (Additive.ofMul (actA j a)) = (singerMat ^ j).mulVec
      (e (Additive.ofMul a)) := fun j a => by simp [actA]
  have hactA_succ : ∀ j a, actA (j + 1) a = actA 1 (actA j a) := fun j a => by
    simp only [actA, pow_succ']
    rw [← mulVec_mulVec]
    simp
  have hactA_zero : ∀ a, actA 0 a = a := fun a => by simp [actA]
  have hactA_mul : ∀ j a b, actA j (a * b) = actA j a * actA j b := fun j a b => by
    apply (Additive.ofMul : ↥A ≃ Additive ↥A).injective
    apply e.injective
    simp only [hactA_vec, ofMul_mul, map_add, mulVec_add]
  have hactA_inj : ∀ a b, actA 1 a = actA 1 b → a = b := fun a b h => by
    have := congrArg (fun x => e (Additive.ofMul x)) h
    simp only [hactA_vec, pow_one] at this
    exact (Additive.ofMul : ↥A ≃ Additive ↥A).injective (e.injective
      (singerMat_mulVec_injective this))
  let f : G → G := fun y => if h : y ∈ A then ((actA 1 ⟨y, h⟩ : ↥A) : G) else 1
  have hf : ∀ a : ↥A, f a = ((actA 1 a : ↥A) : G) := fun a => by simp [f]
  obtain ⟨n, hnL, hn⟩ := hsurj f (fun y hy => by simp only [f, hy, dite_true]; exact (actA 1 _).2)
    (fun x hx y hy => by
      simp only [f, hx, hy, mul_mem hx hy, dite_true]
      exact congrArg Subtype.val (hactA_mul 1 ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx y hy hxy => by
      simp only [f, hx, hy, dite_true] at hxy
      exact congrArg Subtype.val (hactA_inj _ _ (Subtype.ext hxy)))
  have hnj : ∀ (j : ℕ) (a : ↥A), n ^ j * (a : G) * (n ^ j)⁻¹ = ((actA j a : ↥A) : G) := by
    intro j
    induction j with
    | zero => intro a; simp [hactA_zero]
    | succ j ih =>
      intro a
      have h1 : n ^ (j + 1) * (a : G) * (n ^ (j + 1))⁻¹ =
          n * (n ^ j * (a : G) * (n ^ j)⁻¹) * n⁻¹ := by group
      rw [h1, ih a, hn _ (actA j a).2, hactA_succ]
      have := hf (actA j a)
      simpa using this
  have ho : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨v, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd ho
  let c : G → (Fin 4 → ZMod 2) := fun y =>
    if h : y ∈ A then e (Additive.ofMul (⟨y, h⟩ : ↥A)) else 0
  have hc : ∀ a : ↥A, c a = e (Additive.ofMul a) := fun a => by simp [c]
  have hmod : singerMat ^ (2 ^ v) = singerMat ^ (2 ^ v % 15) := by
    conv_lhs => rw [← Nat.mod_add_div (2 ^ v) 15]
    rw [pow_add, pow_mul, singerMat_pow_fifteen, one_pow, mul_one]
  refine ⟨n ^ (2 ^ v), c, 2 ^ v % 15, pow_mem hnL _, fun x hx => ?_, ?_, fun x hx hfix => ?_,
    two_pow_mod_fifteen v, ?_, ?_, ?_, ?_⟩
  · have := hnj (2 ^ v) ⟨x, hx⟩
    rw [show (n ^ 2 ^ v) * x * (n ^ 2 ^ v)⁻¹ = n ^ 2 ^ v * ((⟨x, hx⟩ : ↥A) : G) *
      (n ^ 2 ^ v)⁻¹ from rfl, this]
    exact (actA _ _).2
  · have hd : 2 ^ v ∣ orderOf n := ⟨m, hom⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero v two_ne_zero) hd, hom, Nat.mul_div_cancel_left _
      (pow_pos two_pos v)]
    exact hm
  · have h1 := hnj (2 ^ v) ⟨x, hx⟩
    have h2 : actA (2 ^ v) ⟨x, hx⟩ = ⟨x, hx⟩ := Subtype.ext (by rw [← h1]; exact hfix)
    have h3 := hactA_vec (2 ^ v) ⟨x, hx⟩
    rw [h2] at h3
    have h15 : ¬ 15 ∣ 2 ^ v := fun h => by
      have : 3 ∣ 2 ^ v := Dvd.dvd.trans (by norm_num) h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
      omega
    have h0 := singerMat_pow_fix (2 ^ v) h15 _ h3.symm
    have : Additive.ofMul (⟨x, hx⟩ : ↥A) = 0 := e.injective (by rw [h0, map_zero])
    have h5 : (⟨x, hx⟩ : ↥A) = 1 := by simpa using this
    exact congrArg Subtype.val h5
  · intro a ha b hb
    have e1 : c (a * b) = e (Additive.ofMul (⟨a * b, mul_mem ha hb⟩ : ↥A)) :=
      hc ⟨a * b, mul_mem ha hb⟩
    have e2 : c a = e (Additive.ofMul (⟨a, ha⟩ : ↥A)) := hc ⟨a, ha⟩
    have e3 : c b = e (Additive.ofMul (⟨b, hb⟩ : ↥A)) := hc ⟨b, hb⟩
    rw [e1, e2, e3, ← map_add, ← ofMul_mul]
    rfl
  · intro a ha b hb hab
    have e2 : c a = e (Additive.ofMul (⟨a, ha⟩ : ↥A)) := hc ⟨a, ha⟩
    have e3 : c b = e (Additive.ofMul (⟨b, hb⟩ : ↥A)) := hc ⟨b, hb⟩
    rw [e2, e3] at hab
    have h := (Additive.ofMul : ↥A ≃ Additive ↥A).injective (e.injective hab)
    exact congrArg Subtype.val h
  · intro u
    obtain ⟨x, hx⟩ := e.surjective u
    refine ⟨((Additive.toMul x : ↥A) : G), (Additive.toMul x).2, ?_⟩
    rw [hc (Additive.toMul x)]
    simpa using hx
  · intro a ha
    have h1 := hnj (2 ^ v) ⟨a, ha⟩
    have e1 : c (n ^ 2 ^ v * a * (n ^ 2 ^ v)⁻¹) = e (Additive.ofMul (actA (2 ^ v) ⟨a, ha⟩)) := by
      rw [show (n ^ 2 ^ v) * a * (n ^ 2 ^ v)⁻¹ = n ^ 2 ^ v * ((⟨a, ha⟩ : ↥A) : G) *
        (n ^ 2 ^ v)⁻¹ from rfl, h1]
      exact hc (actA (2 ^ v) ⟨a, ha⟩)
    rw [e1, hactA_vec, hmod, hc ⟨a, ha⟩]

end

end CFSG.EvenSporadicStandard.ThStd
