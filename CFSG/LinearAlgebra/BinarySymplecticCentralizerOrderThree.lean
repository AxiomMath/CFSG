module

public import CFSG.Certificates.InvariantQuadraticCentralizerAction
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LinearAlgebra

open Polynomial Module CFSG.Certificates

section Poly

variable {A : Type*} [Ring A] [Algebra (ZMod 2) A]

theorem golay_factor_mul_factor_poly :
    ((X ^ 11 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X + 1 : (ZMod 2)[X]) *
      (X ^ 11 + X ^ 10 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1)) =
      ∑ i ∈ Finset.range 23, X ^ i := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring_nf
  reduce_mod_char

theorem golay_factor_bezout_poly :
    ((X ^ 7 + X ^ 3 + X : (ZMod 2)[X]) * (X ^ 11 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X + 1) +
      (X ^ 7 + X ^ 6 + X + 1) * (X ^ 11 + X ^ 10 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1)) = 1 := by
  ring_nf
  reduce_mod_char

theorem golay_factor_mul_factor (t : A) :
    (t ^ 11 + t ^ 9 + t ^ 7 + t ^ 6 + t ^ 5 + t + 1) *
      (t ^ 11 + t ^ 10 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 2 + 1) = ∑ i ∈ Finset.range 23, t ^ i := by
  simpa using congrArg (aeval t) golay_factor_mul_factor_poly

theorem golay_factor_bezout (t : A) :
    (t ^ 7 + t ^ 3 + t) * (t ^ 11 + t ^ 9 + t ^ 7 + t ^ 6 + t ^ 5 + t + 1) +
      (t ^ 7 + t ^ 6 + t + 1) * (t ^ 11 + t ^ 10 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 2 + 1) = 1 := by
  simpa using congrArg (aeval t) golay_factor_bezout_poly

end Poly

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem binary_add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def invariantRestrictEnd (W : Submodule (ZMod 2) V) (T : Module.End (ZMod 2) V)
    (hW : ∀ w ∈ W, T w ∈ W) : Function.End W :=
  fun w => ⟨T w, hW w w.2⟩

theorem coe_invariantRestrictEnd_pow (W : Submodule (ZMod 2) V) (T : Module.End (ZMod 2) V)
    (hW : ∀ w ∈ W, T w ∈ W) (n : ℕ) (w : W) :
    (((invariantRestrictEnd W T hW) ^ n) w : V) = (T ^ n) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change (((invariantRestrictEnd W T hW ^ n) (invariantRestrictEnd W T hW w) : W) : V) = _
    rw [ih, pow_succ, Module.End.mul_apply]
    rfl

theorem card_modEq_one_of_fixedPointFree [Finite V] (W : Submodule (ZMod 2) V)
    (T : Module.End (ZMod 2) V) (hW : ∀ w ∈ W, T w ∈ W) (p : ℕ) [Fact p.Prime]
    (hp : ∀ w ∈ W, (T ^ p) w = w) (hfix : ∀ w ∈ W, T w = w → w = 0) :
    Nat.card W ≡ 1 [MOD p] := by
  classical
  have : Fintype W := Fintype.ofFinite W
  set f := invariantRestrictEnd W T hW
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext w
    exact Subtype.ext ((coe_invariantRestrictEnd_pow W T hW p w).trans (hp w w.2))
  have hcard := Equiv.Perm.card_fixedPoints_modEq (f := f) hf
  have hfp : Function.fixedPoints f = {0} := by
    ext w
    change (f : W → W) w = w ↔ w = 0
    constructor
    · intro h
      exact Subtype.ext (hfix w w.2 (congrArg Subtype.val h))
    · rintro rfl
      exact Subtype.ext (map_zero T)
  have h1 : Nat.card (({0} : Set W)) = 1 := by simp
  simp only [Fintype.card_eq_nat_card] at hcard
  rw [hfp, h1] at hcard
  exact hcard

theorem finrank_eq_zero_or_twentytwo [FiniteDimensional (ZMod 2) V] (W : Submodule (ZMod 2) V)
    (hW44 : finrank (ZMod 2) W < 44) (T A : Module.End (ZMod 2) V) (hTW : ∀ w ∈ W, T w ∈ W)
    (hAW : ∀ w ∈ W, A w ∈ W) (hT : ∀ w ∈ W, (T ^ 23) w = w) (hA : ∀ w ∈ W, (A ^ 3) w = w)
    (hTfix : ∀ w ∈ W, T w = w → w = 0) (hAfix : ∀ w ∈ W, A w = w → w = 0) :
    finrank (ZMod 2) W = 0 ∨ finrank (ZMod 2) W = 22 := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card W = 2 ^ finrank (ZMod 2) W := by
    have : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have h23 := card_modEq_one_of_fixedPointFree W T hTW 23 hT hTfix
  have h3 := card_modEq_one_of_fixedPointFree W A hAW 3 hA hAfix
  rw [hcard] at h23 h3
  have key : ∀ d < 44, 2 ^ d % 23 = 1 → 2 ^ d % 3 = 1 → d = 0 ∨ d = 22 := by decide
  exact key _ hW44 h23 h3

theorem binary_order_twentythree_commuting_fixed_point_free_order_three
    [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V < 44)
    (b : LinearMap.BilinForm (ZMod 2) V) (hb : b.Nondegenerate) (T A : Module.End (ZMod 2) V)
    (hT : T ^ 23 = 1) (hTb : ∀ x y, b (T x) (T y) = b x y) (hA : A ^ 3 = 1)
    (hAfix : ∀ v, A v = v → v = 0) (hAT : A * T = T * A) : T = 1 := by
  classical
  set F₁ : Module.End (ZMod 2) V := T ^ 11 + T ^ 9 + T ^ 7 + T ^ 6 + T ^ 5 + T + 1 with hF₁
  set F₂ : Module.End (ZMod 2) V := T ^ 11 + T ^ 10 + T ^ 6 + T ^ 5 + T ^ 4 + T ^ 2 + 1 with hF₂
  have hprod : F₁ * F₂ = ∑ i ∈ Finset.range 23, T ^ i := golay_factor_mul_factor T
  have hbez : (T ^ 7 + T ^ 3 + T) * F₁ + (T ^ 7 + T ^ 6 + T + 1) * F₂ = 1 :=
    golay_factor_bezout T
  have hTpow : ∀ n x y, b ((T ^ n) x) ((T ^ n) y) = b x y := by
    intro n
    induction n with
    | zero => intro x y; rfl
    | succ n ih =>
      intro x y
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hTb]
  have hshift : ∀ i j, i ≤ j → ∀ x y, b ((T ^ i) x) ((T ^ j) y) = b x ((T ^ (j - i)) y) := by
    intro i j hij x y
    rw [show j = i + (j - i) by omega, pow_add, Module.End.mul_apply, hTpow,
      Nat.add_sub_cancel_left]
  have hrec : ∀ u v, b (F₁ u) ((T ^ 11) v) = b u (F₂ v) := by
    intro u v
    have e : ∀ i, i ≤ 11 → b ((T ^ i) u) ((T ^ 11) v) = b u ((T ^ (11 - i)) v) :=
      fun i hi => hshift i 11 hi u v
    have e1 : b (T u) ((T ^ 11) v) = b u ((T ^ 10) v) := by simpa using e 1 (by norm_num)
    simp only [hF₁, hF₂, LinearMap.add_apply, map_add, Module.End.one_apply]
    rw [e 11 le_rfl, e 9 (by norm_num), e 7 (by norm_num), e 6 (by norm_num),
      e 5 (by norm_num), e1]
    simp only [Nat.reduceSub, pow_zero, Module.End.one_apply]
    abel
  have hcommT : ∀ n, A * T ^ n = T ^ n * A := fun n => (Commute.pow_right hAT n).eq
  have hAF : ∀ F : Module.End (ZMod 2) V, A * F = F * A → ∀ w ∈ LinearMap.ker F,
      A w ∈ LinearMap.ker F := by
    intro F hF w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [← Module.End.mul_apply, ← hF, Module.End.mul_apply, hw, map_zero]
  have hAF₁ : A * F₁ = F₁ * A := by
    simp only [hF₁, mul_add, add_mul, hcommT, mul_one, one_mul]
    rw [show A * T = T * A from hAT]
  have hAF₂ : A * F₂ = F₂ * A := by
    simp only [hF₂, mul_add, add_mul, hcommT, mul_one, one_mul]
  have hTF₁ : T * F₁ = F₁ * T := by
    simp only [hF₁, mul_add, add_mul, ← pow_succ, ← pow_succ', mul_one, one_mul]
  have hTF₂ : T * F₂ = F₂ * T := by
    simp only [hF₂, mul_add, add_mul, ← pow_succ, ← pow_succ', mul_one, one_mul]
  have hTn : ∀ v, T v = v → ∀ n, (T ^ n) v = v := by
    intro v hv n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, ih]
  have h7 : ∀ v : V, v + v + v + v + v + v + v = v := by
    intro v
    simp only [binary_add_self, zero_add]
  have hF₁fix : ∀ v, T v = v → F₁ v = v := by
    intro v hv
    simp only [hF₁, LinearMap.add_apply, hTn v hv, hv, Module.End.one_apply]
    exact h7 v
  have hF₂fix : ∀ v, T v = v → F₂ v = v := by
    intro v hv
    simp only [hF₂, LinearMap.add_apply, hTn v hv, Module.End.one_apply]
    exact h7 v
  have hdim : ∀ F : Module.End (ZMod 2) V, A * F = F * A → T * F = F * T →
      (∀ v, T v = v → F v = v) →
      finrank (ZMod 2) (LinearMap.ker F) = 0 ∨ finrank (ZMod 2) (LinearMap.ker F) = 22 := by
    intro F hAF' hTF' hFfix
    refine finrank_eq_zero_or_twentytwo (LinearMap.ker F)
      ((Submodule.finrank_le _).trans_lt hV) T A ?_ (hAF F hAF') (fun w _ => by rw [hT]; rfl)
      (fun w _ => by rw [hA]; rfl) ?_ (fun w _ hw => hAfix w hw)
    · intro w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [← Module.End.mul_apply, ← hTF', Module.End.mul_apply, hw, map_zero]
    · intro w hw hTw
      rw [LinearMap.mem_ker] at hw
      rw [← hFfix w hTw, hw]
  have hd₁ := hdim F₁ hAF₁ hTF₁ hF₁fix
  have hd₂ := hdim F₂ hAF₂ hTF₂ hF₂fix
  have hinf : LinearMap.ker F₁ ⊓ LinearMap.ker F₂ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hw
    rw [Submodule.mem_bot]
    have h := congrArg (fun F : Module.End (ZMod 2) V => F w) hbez
    simp only [LinearMap.add_apply, Module.End.mul_apply, hw.1, hw.2, map_zero, add_zero,
      Module.End.one_apply] at h
    exact h.symm
  have hsum : finrank (ZMod 2) (LinearMap.ker F₁) + finrank (ZMod 2) (LinearMap.ker F₂) < 44 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker F₁) (LinearMap.ker F₂)
    rw [hinf, finrank_bot, add_zero] at h
    rw [← h]
    exact (Submodule.finrank_le _).trans_lt hV
  have hTinj : Function.Injective ⇑(T ^ 11) := by
    intro x y hxy
    have h := congrArg (fun w => (T ^ 12) w) hxy
    simp only [← Module.End.mul_apply, ← pow_add, show 12 + 11 = 23 from rfl, hT,
      Module.End.one_apply] at h
    exact h
  have hker : LinearMap.ker F₁ = ⊥ ∧ LinearMap.ker F₂ = ⊥ := by
    rcases hd₁ with h₁ | h₁
    · have hk₁ : LinearMap.ker F₁ = ⊥ := Submodule.finrank_eq_zero.1 h₁
      refine ⟨hk₁, ?_⟩
      have hsurj : Function.Surjective F₁ :=
        LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 hk₁)
      rw [eq_bot_iff]
      intro v hv
      rw [LinearMap.mem_ker] at hv
      rw [Submodule.mem_bot]
      have h0 : (T ^ 11) v = 0 := hb.2 _ fun w => by
        obtain ⟨u, rfl⟩ := hsurj w
        rw [hrec, hv, map_zero]
      exact hTinj (h0.trans (map_zero _).symm)
    · rcases hd₂ with h₂ | h₂
      · have hk₂ : LinearMap.ker F₂ = ⊥ := Submodule.finrank_eq_zero.1 h₂
        refine ⟨?_, hk₂⟩
        have hsurj : Function.Surjective F₂ :=
          LinearMap.injective_iff_surjective.1 (LinearMap.ker_eq_bot.1 hk₂)
        rw [eq_bot_iff]
        intro u hu
        rw [LinearMap.mem_ker] at hu
        rw [Submodule.mem_bot]
        exact hb.1 _ fun w => by
          obtain ⟨v, rfl⟩ := hsurj w
          rw [← hrec, hu, map_zero, LinearMap.zero_apply]
      · omega
  have hΦinj : Function.Injective ⇑(∑ i ∈ Finset.range 23, T ^ i) := by
    rw [← hprod, Module.End.coe_mul]
    exact (LinearMap.ker_eq_bot.1 hker.1).comp (LinearMap.ker_eq_bot.1 hker.2)
  have hgeom : (∑ i ∈ Finset.range 23, T ^ i) * (T - 1) = 0 := by
    rw [geom_sum_mul, hT, sub_self]
  refine LinearMap.ext fun v => ?_
  have h := congrArg (fun F : Module.End (ZMod 2) V => F v) hgeom
  simp only [Module.End.mul_apply, LinearMap.zero_apply] at h
  have h' : (T - 1) v = 0 := hΦinj (h.trans (map_zero _).symm)
  rw [LinearMap.sub_apply, sub_eq_zero] at h'
  exact h'

theorem binary_symplectic_centralizer_order_three_exclusion [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 22 ∨ finrank (ZMod 2) V = 24)
    (b : LinearMap.BilinForm (ZMod 2) V) (hb : b.Nondegenerate) (_hbalt : b.IsAlt)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (hKb : K ≤ bilinIsometryGroup b)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ k ∈ K, ∀ w ∈ W, (k : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h23 : 23 ∣ Nat.card K)
    (h3 : ∀ a ∈ Subgroup.centralizer (K : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)),
      a ^ 3 = 1) :
    Subgroup.centralizer (K : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) ⊓
      bilinIsometryGroup b = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro a ⟨haC, -⟩
  rw [Subgroup.mem_bot]
  by_contra ha1
  have hcomm : ∀ k ∈ K, (k : Module.End (ZMod 2) V) * a = a * k := fun k hk => by
    rw [← Units.val_mul, ← Units.val_mul, Subgroup.mem_centralizer_iff.1 haC k hk]
  have hfix : ∀ v, (a : Module.End (ZMod 2) V) v = v → v = 0 := by
    have hW := hirr (LinearMap.ker ((a : Module.End (ZMod 2) V) - 1)) fun k hk w hw => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
      rw [← Module.End.mul_apply, ← hcomm k hk, Module.End.mul_apply, hw]
    rcases hW with h | h
    · intro v hv
      have hv' : v ∈ LinearMap.ker ((a : Module.End (ZMod 2) V) - 1) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hv, sub_self]
      rw [h] at hv'
      exact hv'
    · exfalso
      refine ha1 (Units.ext (LinearMap.ext fun v => ?_))
      have hv : v ∈ LinearMap.ker ((a : Module.End (ZMod 2) V) - 1) := by rw [h]; trivial
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      exact hv
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[ZMod 2] V))
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    Finite.of_injective _ Units.val_injective
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 23 h23
  have hk23 : ((k : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) ^ 23 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, ← hk, pow_orderOf_eq_one]
    rfl
  have hkb : ∀ x y, b (((k : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) x) (((k : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      Module.End (ZMod 2) V) y) = b x y := hKb k.2
  have ha3 : (a : Module.End (ZMod 2) V) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h3 a haC]
    rfl
  have hT1 := binary_order_twentythree_commuting_fixed_point_free_order_three
    (by omega) b hb _ _ hk23 hkb ha3 hfix (hcomm k k.2).symm
  have hk1 : k = 1 := Subtype.ext (Units.ext hT1)
  rw [hk1, orderOf_one] at hk
  exact absurd hk (by norm_num)

end CFSG.LinearAlgebra
