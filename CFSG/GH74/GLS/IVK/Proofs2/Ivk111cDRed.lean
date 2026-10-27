module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDefs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

@[expose] def redLabel (q A : ℕ) : ℕ := if A < q then A else (A - 1) % (q - 1) + 1

theorem redLabel_of_lt {q A : ℕ} (h : A < q) : redLabel q A = A := by
  simp [redLabel, h]

theorem redLabel_lt {q : ℕ} (hq : 2 ≤ q) (A : ℕ) : redLabel q A < q := by
  unfold redLabel
  split_ifs with h
  · exact h
  · have : (A - 1) % (q - 1) < q - 1 := Nat.mod_lt _ (by omega)
    omega

namespace Mix11cRed

theorem redLabel_zero {q : ℕ} (hq : 1 ≤ q) : redLabel q 0 = 0 := redLabel_of_lt hq

theorem one_le_redLabel {q A : ℕ} (hA : 1 ≤ A) : 1 ≤ redLabel q A := by
  unfold redLabel
  split_ifs with h
  · exact hA
  · omega

theorem redLabel_modEq {q : ℕ} (hq : 2 ≤ q) (A : ℕ) : redLabel q A ≡ A [MOD q - 1] := by
  unfold redLabel
  split_ifs with h
  · exact Nat.ModEq.refl _
  · have hA : 1 ≤ A := by omega
    have h1 : (A - 1) % (q - 1) ≡ A - 1 [MOD q - 1] := Nat.mod_modEq _ _
    have h2 := h1.add_right 1
    rwa [Nat.sub_add_cancel hA] at h2

theorem eq_of_modEq_of_mem {q x y : ℕ} (hx1 : 1 ≤ x) (hxq : x < q) (hy1 : 1 ≤ y) (hyq : y < q)
    (h : x ≡ y [MOD q - 1]) : x = y := by
  have h2 : x - 1 + 1 ≡ y - 1 + 1 [MOD q - 1] := by
    rwa [Nat.sub_add_cancel hx1, Nat.sub_add_cancel hy1]
  have h' : x - 1 ≡ y - 1 [MOD q - 1] := Nat.ModEq.add_right_cancel' 1 h2
  have := h'.eq_of_lt_of_lt (by omega) (by omega)
  omega

theorem rot_zero_eq (p n : ℕ) : rot p n 0 = 0 := by simp [rot]

theorem one_le_rot {p n : ℕ} (hp : 1 < p) {A : ℕ} (hA : 1 ≤ A) : 1 ≤ rot p n A := by
  unfold rot
  have hM : 0 < p ^ (n - 1) := pow_pos (by omega) _
  by_cases hlt : A < p ^ (n - 1)
  · rw [Nat.mod_eq_of_lt hlt]
    have : 1 ≤ A * p := Nat.mul_pos (by omega) (by omega)
    exact le_trans this (Nat.le_add_right _ _)
  · have := Nat.div_pos (not_lt.1 hlt) hM
    exact le_trans this (Nat.le_add_left _ _)

theorem rot_lt_of_lt {p n : ℕ} (hp : 1 < p) (hn : 0 < n) {A : ℕ} (hA : A < p ^ n) :
    rot p n A < p ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpm : 0 < p ^ m := pow_pos (by omega) m
  have h1 : A % p ^ m < p ^ m := Nat.mod_lt _ hpm
  have h2 : A / p ^ m < p := by
    rw [Nat.div_lt_iff_lt_mul hpm]
    calc A < p ^ (m + 1) := hA
      _ = p * p ^ m := by ring
  have h3 : rot p (m + 1) A = (A % p ^ m) * p + A / p ^ m := by simp [rot]
  rw [h3]
  calc (A % p ^ m) * p + A / p ^ m < (A % p ^ m) * p + p := by omega
    _ = (A % p ^ m + 1) * p := by ring
    _ ≤ p ^ m * p := Nat.mul_le_mul_right _ h1
    _ = p ^ (m + 1) := by ring

theorem rot_modEq {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (A : ℕ) :
    rot p n A ≡ p * A [MOD p ^ n - 1] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpm : 0 < p ^ m := pow_pos (by omega) m
  have h3 : rot p (m + 1) A = (A % p ^ m) * p + A / p ^ m := by simp [rot]
  have hN : p ^ (m + 1) - 1 + 1 = p ^ (m + 1) := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
  have hNM : (p ^ (m + 1) - 1) + 1 = p * p ^ m := by rw [hN]; ring
  have hA : A = p ^ m * (A / p ^ m) + A % p ^ m := (Nat.div_add_mod A (p ^ m)).symm
  have key : p * A = (A / p ^ m + p * (A % p ^ m)) + (p ^ (m + 1) - 1) * (A / p ^ m) := by
    have e1 : p * A = p * p ^ m * (A / p ^ m) + p * (A % p ^ m) := by
      conv_lhs => rw [hA]
      ring
    rw [e1, ← hNM]
    ring
  rw [h3, key]
  have e2 : (A % p ^ m) * p + A / p ^ m = A / p ^ m + p * (A % p ^ m) := by ring
  rw [e2]
  exact (Nat.add_mul_mod_self_left _ _ _).symm

theorem redLabel_rot {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (A : ℕ) :
    redLabel (p ^ n) (rot p n A) = rot p n (redLabel (p ^ n) A) := by
  have hq : 2 ≤ p ^ n := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · rw [rot_zero_eq, redLabel_zero (by omega), rot_zero_eq]
  · have hA1 : 1 ≤ A := hA
    have hr1 : 1 ≤ redLabel (p ^ n) A := one_le_redLabel hA1
    have hrq : redLabel (p ^ n) A < p ^ n := redLabel_lt hq A
    have hx1 : 1 ≤ redLabel (p ^ n) (rot p n A) := one_le_redLabel (one_le_rot hp hA1)
    have hxq : redLabel (p ^ n) (rot p n A) < p ^ n := redLabel_lt hq _
    have hy1 : 1 ≤ rot p n (redLabel (p ^ n) A) := one_le_rot hp hr1
    have hyq : rot p n (redLabel (p ^ n) A) < p ^ n := rot_lt_of_lt hp hn hrq
    refine eq_of_modEq_of_mem hx1 hxq hy1 hyq ?_
    calc redLabel (p ^ n) (rot p n A) ≡ rot p n A [MOD p ^ n - 1] := redLabel_modEq hq _
      _ ≡ p * A [MOD p ^ n - 1] := rot_modEq hp hn A
      _ ≡ p * redLabel (p ^ n) A [MOD p ^ n - 1] := ((redLabel_modEq hq A).mul_left p).symm
      _ ≡ rot p n (redLabel (p ^ n) A) [MOD p ^ n - 1] := (rot_modEq hp hn _).symm

end Mix11cRed

theorem redLabel_iterate_rot {p n : ℕ} (hp : 1 < p) (hn : 0 < n) (s A : ℕ) :
    redLabel (p ^ n) ((rot p n)^[s] A) = (rot p n)^[s] (redLabel (p ^ n) A) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Mix11cRed.redLabel_rot hp hn, ih]

namespace Mix11cRed

theorem pow_eq_pow_redLabel {F : Type} [Field F] [Finite F] {q : ℕ} (hq : Nat.card F = q) (x : F)
    (A : ℕ) : x ^ A = x ^ redLabel q A := by
  have hq2 : 2 ≤ q := by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  by_cases hA : A < q
  · rw [redLabel_of_lt hA]
  · have hAq : q ≤ A := not_lt.1 hA
    have hred : redLabel q A = (A - 1) % (q - 1) + 1 := by
      simp [redLabel, hA]
    rw [hred]
    have hdecomp : A = (q - 1) * ((A - 1) / (q - 1)) + ((A - 1) % (q - 1) + 1) := by
      have := Nat.div_add_mod (A - 1) (q - 1)
      omega
    by_cases hx : x = 0
    · subst hx
      rw [zero_pow (by omega), zero_pow (by omega)]
    · have := Fintype.ofFinite F
      have hfc : Fintype.card F = q := by rw [← hq, Nat.card_eq_fintype_card]
      have hxq : x ^ (q - 1) = 1 := by
        have h1 := FiniteField.pow_card_sub_one_eq_one x hx
        rwa [hfc] at h1
      calc x ^ A = x ^ ((q - 1) * ((A - 1) / (q - 1)) + ((A - 1) % (q - 1) + 1)) := by
            rw [← hdecomp]
        _ = (x ^ (q - 1)) ^ ((A - 1) / (q - 1)) * x ^ ((A - 1) % (q - 1) + 1) := by
            rw [pow_add, pow_mul]
        _ = x ^ ((A - 1) % (q - 1) + 1) := by rw [hxq, one_pow, one_mul]

theorem steinbergSub_redLabel {F : Type} [Field F] [Finite F] {q : ℕ} (hq : Nat.card F = q)
    (A : ℕ) : steinbergSub F F A = steinbergSub F F (redLabel q A) := by
  have hmono : monoFun F F A 0 = monoFun F F (redLabel q A) 0 := by
    funext v
    simp only [monoFun, pow_zero, mul_one]
    exact pow_eq_pow_redLabel hq _ A
  unfold steinbergSub
  rw [hmono]

end Mix11cRed

section Constituent

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F]
  {W : Type} [AddCommGroup W] [Module (ZMod p) W]

omit [Finite F] in
theorem Mix11cRed.hasConstituent_of_steinbergSub_eq {σ : Representation (ZMod p) (SLm F) W}
    {A B : ℕ} (hsub : steinbergSub F F A = steinbergSub F F B) (h : HasConstituent p F σ A) :
    HasConstituent p F σ B := by
  obtain ⟨f, hf⟩ := h
  let e : ↥(steinbergSub F F B) ≃ₗ[F] ↥(steinbergSub F F A) := LinearEquiv.ofEq _ _ hsub.symm
  let ι : Representation.IntertwiningMap (steinbergRep F F B) (steinbergRep F F A) :=
    e.toLinearMap.intertwiningMap_of_isIntertwiningMap (steinbergRep F F B) (steinbergRep F F A)
      (fun g v => Subtype.ext rfl)
  let φ := Representation.IntertwiningMap.equivLinearMapAsModule (steinbergRep F F B)
    (steinbergRep F F A) ι
  have hφ : Function.Surjective φ := e.surjective
  refine ⟨f.comp φ, fun h0 => hf ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hφ x
  exact LinearMap.congr_fun h0 y

theorem hasConstituent_redLabel {n : ℕ} (hF : Nat.card F = p ^ n)
    (σ : Representation (ZMod p) (SLm F) W) {A : ℕ} (h : HasConstituent p F σ A) :
    HasConstituent p F σ (redLabel (p ^ n) A) :=
  Mix11cRed.hasConstituent_of_steinbergSub_eq (Mix11cRed.steinbergSub_redLabel hF A) h

end Constituent

end CFSG.GH74.GLS.Stage4.Rest
