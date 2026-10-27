module

public import CFSG.Fischer.F4
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped commutatorElement

open CFSG.Fischer

namespace CFSG.GroupTheory.HeisenbergF4

@[ext]
structure H27 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
deriving DecidableEq, Fintype

namespace H27

@[expose] def mul (x y : H27) : H27 :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩

@[expose] def inv (x : H27) : H27 :=
  ⟨-x.a, -x.b, -x.c + x.a * x.b⟩

instance : Mul H27 := ⟨mul⟩
instance : Inv H27 := ⟨inv⟩
instance : One H27 := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem mul_a (x y : H27) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : H27) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : H27) : (x * y).c = x.c + y.c + x.a * y.b := rfl

@[simp] theorem inv_a (x : H27) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : H27) : x⁻¹.b = -x.b := rfl
@[simp] theorem inv_c (x : H27) : x⁻¹.c = -x.c + x.a * x.b := rfl

@[simp] theorem one_a : (1 : H27).a = 0 := rfl
@[simp] theorem one_b : (1 : H27).b = 0 := rfl
@[simp] theorem one_c : (1 : H27).c = 0 := rfl

@[expose] def c0 : H27 := ⟨0, 0, 1⟩

@[simp] theorem c0_a : c0.a = 0 := rfl
@[simp] theorem c0_b : c0.b = 0 := rfl
@[simp] theorem c0_c : c0.c = 1 := rfl

instance : Group H27 :=
  Group.ofLeftAxioms
    (fun x y z => by
      ext <;> simp only [mul_a, mul_b, mul_c] <;> ring)
    (fun x => by
      ext <;> simp only [mul_a, mul_b, mul_c, one_a, one_b, one_c] <;> ring)
    (fun x => by
      ext
      · change (x⁻¹ * x).a = (1 : H27).a
        rw [mul_a, inv_a, one_a]
        abel
      · change (x⁻¹ * x).b = (1 : H27).b
        rw [mul_b, inv_b, one_b]
        abel
      · change (x⁻¹ * x).c = (1 : H27).c
        rw [mul_c, inv_c, inv_a, one_c]
        have h : (-x.a) * x.b = -(x.a * x.b) := neg_mul x.a x.b
        rw [h]
        abel)

def toProd : H27 ≃ ZMod 3 × ZMod 3 × ZMod 3 where
  toFun x := (x.a, x.b, x.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

theorem card : Fintype.card H27 = 27 := by
  rw [Fintype.card_congr toProd]
  decide

theorem exponent_three : ∀ x : H27, x ^ 3 = 1 := by decide

theorem noncommutative : ∃ x y : H27, x * y ≠ y * x := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ?_⟩
  decide

def centerSubgroup : Subgroup H27 where
  carrier := {x | x.a = 0 ∧ x.b = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    simp [hx1, hx2, hy1, hy2]
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    constructor <;> (simp [hx1, hx2]; exact neg_zero)

theorem mem_centerSubgroup_iff (x : H27) :
    x ∈ centerSubgroup ↔ x.a = 0 ∧ x.b = 0 := Iff.rfl

theorem center_eq : Subgroup.center H27 = centerSubgroup := by
  ext x
  rw [Subgroup.mem_center_iff, mem_centerSubgroup_iff]
  constructor
  · intro h
    have h1 : x.c = x.c + x.a := by
      simpa [mul_a, mul_b, mul_c] using congrArg H27.c (h ⟨0, 1, 0⟩)
    have h2 : x.c + x.b = x.c := by
      simpa [mul_a, mul_b, mul_c] using congrArg H27.c (h ⟨1, 0, 0⟩)
    constructor
    · linear_combination -h1
    · linear_combination h2
  · rintro ⟨hx1, hx2⟩ g
    ext <;> simp [mul_a, mul_b, mul_c, hx1, hx2, add_comm]

theorem commutator_mem_center (x y : H27) : ⁅x, y⁆ ∈ centerSubgroup := by
  rw [mem_centerSubgroup_iff]
  constructor
  · rw [commutatorElement_def]
    simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
    abel
  · rw [commutatorElement_def]
    simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
    abel

theorem exists_conj_eq_mul (x : H27) (hx : x ∉ centerSubgroup) :
    ∃ y : H27, y * x * y⁻¹ = c0 * x := by
  by_cases ha : x.a = 0
  · have hb : x.b ≠ 0 := by
      intro hb
      exact hx (mem_centerSubgroup_iff x |>.mpr ⟨ha, hb⟩)
    refine ⟨⟨x.b⁻¹, 0, 0⟩, ?_⟩
    ext
    · simp only [mul_a, inv_a, inv_b, inv_c]
      rw [ha]
      abel
    · simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
      abel
    · simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c, c0_a, c0_b, c0_c, ha,
        zero_mul, mul_zero, zero_add, add_zero]
      have h1 : x.b⁻¹ * x.b = 1 := inv_mul_cancel₀ hb
      have h2 : x.b⁻¹ * (-0) = 0 := by
        have h : (-0 : ZMod 3) = 0 := neg_zero
        rw [h, mul_zero]
      rw [h1, h2]
      abel
  · refine ⟨⟨0, -(x.a⁻¹), 0⟩, ?_⟩
    ext
    · simp only [mul_a, inv_a, inv_b, inv_c]
      abel
    · simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c]
      abel
    · simp only [mul_a, mul_b, mul_c, inv_a, inv_b, inv_c, c0_a, c0_b, c0_c,
        zero_mul, mul_zero, zero_add, add_zero]
      have h1 : x.a * (-(-(x.a⁻¹))) = 1 := by
        have h : -(-(x.a⁻¹)) = x.a⁻¹ := neg_neg (x.a⁻¹)
        rw [h, mul_inv_cancel₀ ha]
      change x.c + -0 + x.a * (-(-(x.a⁻¹))) = 1 + x.c
      rw [h1]
      abel

theorem commutator_le_center : commutator H27 ≤ centerSubgroup := by
  rw [commutator, Subgroup.commutator_le]
  intro x _ y _
  exact commutator_mem_center x y

theorem center_le_commutator : centerSubgroup ≤ commutator H27 := by
  intro x hx
  rw [mem_centerSubgroup_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hc0 : (⟨0, 0, (1 : ZMod 3)⟩ : H27) ∈ commutator H27 := by
    rw [commutator]
    have hcomm : ⁅(⟨1, 0, 0⟩ : H27), (⟨0, 1, 0⟩ : H27)⁆ = ⟨0, 0, (1 : ZMod 3)⟩ := by
      decide
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hpow : ∀ n : ℕ, (⟨0, 0, (1 : ZMod 3)⟩ : H27) ^ n = ⟨0, 0, (n : ZMod 3)⟩ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, ih]
      ext <;> simp [mul_a, mul_b, mul_c] <;> ring
  have hx_eq : x = ⟨0, 0, (x.c.val : ZMod 3)⟩ := by
    ext <;> simp [hx1, hx2, ZMod.natCast_zmod_val]
  rw [hx_eq, ← hpow x.c.val]
  exact Subgroup.pow_mem _ hc0 _

theorem commutator_eq_center : commutator H27 = centerSubgroup :=
  le_antisymm commutator_le_center center_le_commutator

def centerEquiv : centerSubgroup ≃ ZMod 3 where
  toFun x := x.1.c
  invFun z := ⟨⟨0, 0, z⟩, by simp [centerSubgroup]⟩
  left_inv x := by
    rcases x with ⟨⟨a, b, c⟩, hx⟩
    rw [mem_centerSubgroup_iff] at hx
    change a = 0 ∧ b = 0 at hx
    ext <;> simp [hx.1, hx.2]
  right_inv z := rfl

theorem card_center : Nat.card centerSubgroup = 3 := by
  rw [Nat.card_congr centerEquiv, Nat.card_eq_fintype_card, ZMod.card]

theorem c0_mem_centerSubgroup : c0 ∈ centerSubgroup := by
  rw [mem_centerSubgroup_iff]
  exact ⟨rfl, rfl⟩

theorem orderOf_c0 : orderOf c0 = 3 :=
  orderOf_eq_prime (exponent_three c0) (by decide)

theorem c0_mem_center : c0 ∈ Subgroup.center H27 := by
  rw [center_eq]
  exact c0_mem_centerSubgroup

theorem centerSubgroup_eq_zpowers_c0 : centerSubgroup = Subgroup.zpowers c0 := by
  have hle : Subgroup.zpowers c0 ≤ centerSubgroup :=
    Subgroup.zpowers_le.mpr c0_mem_centerSubgroup
  have hcard : Nat.card (Subgroup.zpowers c0) = 3 := by
    rw [Nat.card_zpowers, orderOf_c0]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_center])).symm

theorem center_eq_zpowers_c0 : Subgroup.center H27 = Subgroup.zpowers c0 := by
  rw [center_eq, centerSubgroup_eq_zpowers_c0]

theorem card_commutator : Nat.card (commutator H27) = 3 := by
  rw [commutator_eq_center, card_center]

theorem nat_card : Nat.card H27 = 27 := by
  rw [Nat.card_eq_fintype_card, card]

end H27



variable {W : Type*} [AddCommGroup W] [Module F4 W] [FiniteDimensional F4 W]

abbrev fixedSpace (T : W →ₗ[F4] W) : Submodule F4 W := LinearMap.ker (T - 1)

theorem fixedSpace_finrank_eq_one
    (ρ : H27 →* (W ≃ₗ[F4] W))
    {ω : F4} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hρc : ((ρ H27.c0 : W ≃ₗ[F4] W) : W →ₗ[F4] W) = ω • (1 : W →ₗ[F4] W))
    (hW : Module.finrank F4 W = 3)
    (x : H27) (hx : x ∉ Subgroup.center H27) :
    Module.finrank F4 (fixedSpace ((ρ x : W ≃ₗ[F4] W) : W →ₗ[F4] W)) = 1 := by
  classical
  let T : W →ₗ[F4] W := ρ x
  let P : W →ₗ[F4] W := 1 + T + T ^ 2
  have hx' : x ∉ H27.centerSubgroup := by
    simpa [H27.center_eq] using hx
  obtain ⟨y, hy⟩ := H27.exists_conj_eq_mul x hx'
  have hT3 : T ^ 3 = 1 := by
    have h : (ρ x : W ≃ₗ[F4] W) ^ 3 = 1 := by
      calc (ρ x) ^ 3 = ρ (x ^ 3) := (map_pow ρ x 3).symm
        _ = ρ 1 := by rw [H27.exponent_three x]
        _ = 1 := map_one ρ
    change ((ρ x : W ≃ₗ[F4] W) : W →ₗ[F4] W) ^ 3 = 1
    rw [show ((ρ x : W ≃ₗ[F4] W) : W →ₗ[F4] W) ^ 3 =
        (((ρ x : W ≃ₗ[F4] W) ^ 3 : W ≃ₗ[F4] W) : W →ₗ[F4] W) from rfl, h]
    rfl
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    have hωeq : ω = 1 := by
      calc ω = ω * ω ^ 2 := by rw [h, mul_one]
        _ = ω ^ 3 := by ring
        _ = 1 := hω3
    exact hω1 hωeq
  have hconj : (ρ y).conj T = ω • T := by
    have hgroup : (ρ y) * (ρ x) * (ρ y)⁻¹ = (ρ H27.c0) * (ρ x) := by
      calc (ρ y) * (ρ x) * (ρ y)⁻¹ = ρ (y * x * y⁻¹) := by simp [map_mul]
        _ = ρ (H27.c0 * x) := by rw [hy]
        _ = ρ H27.c0 * ρ x := map_mul _ _ _
    have hlin := congrArg (fun e : W ≃ₗ[F4] W => (e : W →ₗ[F4] W)) hgroup
    have hconj_map : (ρ y).conj T =
        (((ρ y) * (ρ x) * (ρ y)⁻¹ : W ≃ₗ[F4] W) : W →ₗ[F4] W) := by
      ext w
      simp [LinearEquiv.conj_apply, T]
    calc (ρ y).conj T = (((ρ y) * (ρ x) * (ρ y)⁻¹ : W ≃ₗ[F4] W) : W →ₗ[F4] W) := hconj_map
      _ = (((ρ H27.c0) * (ρ x) : W ≃ₗ[F4] W) : W →ₗ[F4] W) := hlin
      _ = ω • T := by
          simp [hρc, T, smul_mul_assoc]
  have htraceT : LinearMap.trace F4 W T = 0 := by
    have htr : LinearMap.trace F4 W T = ω * LinearMap.trace F4 W T := by
      calc LinearMap.trace F4 W T = LinearMap.trace F4 W ((ρ y).conj T) :=
            (LinearMap.trace_conj' T (ρ y)).symm
        _ = LinearMap.trace F4 W (ω • T) := by rw [hconj]
        _ = ω * LinearMap.trace F4 W T := by simp
    have hcoef : (1 : F4) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
    have hzero : (1 - ω) * LinearMap.trace F4 W T = 0 := by
      rw [sub_mul, one_mul]
      nth_rewrite 1 [htr]
      exact sub_self _
    exact (mul_eq_zero.mp hzero).resolve_left hcoef
  have hconj2 : (ρ y).conj (T ^ 2) = ω ^ 2 • T ^ 2 := by
    have hmap : (ρ y).conj (T ^ 2) = ((ρ y).conj T) ^ 2 := by
      change (LinearEquiv.conjRingEquiv (ρ y)) (T ^ 2) =
        ((LinearEquiv.conjRingEquiv (ρ y)) T) ^ 2
      rw [map_pow]
    calc (ρ y).conj (T ^ 2) = ((ρ y).conj T) ^ 2 := hmap
      _ = (ω • T) ^ 2 := by rw [hconj]
      _ = (ω * ω) • (T * T) := by rw [pow_two, smul_mul_smul_comm]
      _ = ω ^ 2 • T ^ 2 := by rw [pow_two, pow_two]
  have htraceT2 : LinearMap.trace F4 W (T ^ 2) = 0 := by
    have htr : LinearMap.trace F4 W (T ^ 2) = ω ^ 2 * LinearMap.trace F4 W (T ^ 2) := by
      calc LinearMap.trace F4 W (T ^ 2) = LinearMap.trace F4 W ((ρ y).conj (T ^ 2)) :=
            (LinearMap.trace_conj' (T ^ 2) (ρ y)).symm
        _ = LinearMap.trace F4 W (ω ^ 2 • T ^ 2) := by rw [hconj2]
        _ = ω ^ 2 * LinearMap.trace F4 W (T ^ 2) := by simp
    have hcoef : (1 : F4) - ω ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hω2)
    have hzero : (1 - ω ^ 2) * LinearMap.trace F4 W (T ^ 2) = 0 := by
      rw [sub_mul, one_mul]
      nth_rewrite 1 [htr]
      exact sub_self _
    exact (mul_eq_zero.mp hzero).resolve_left hcoef
  have hTP : T * P = P := by
    unfold P
    rw [mul_add, mul_add, mul_one, ← pow_two, ← pow_succ' T 2, hT3]
    abel
  have hPT : P * T = P := by
    unfold P
    rw [add_mul, add_mul, one_mul, ← pow_two, ← pow_succ T 2, hT3]
    abel
  have hT2P : T ^ 2 * P = P := by
    rw [pow_two, mul_assoc, hTP, hTP]
  have hPP : P * P = P := by
    unfold P
    rw [add_mul, add_mul, one_mul, hTP, hT2P]
    have hPP0 : P + P = 0 := by
      rw [← two_smul F4 P, F4.two_eq_zero, zero_smul]
    rw [hPP0, zero_add]
  have hproj : LinearMap.IsProj (LinearMap.range P) P :=
    (LinearMap.isProj_range_iff_isIdempotentElem P).mpr hPP
  have hrange : LinearMap.range P = fixedSpace T := by
    apply le_antisymm
    · rintro w ⟨v, rfl⟩
      have hsub : (T - 1) * P = 0 := by
        rw [sub_mul, hTP, one_mul, sub_self]
      simpa [Module.End.mul_apply] using congrArg (fun f : W →ₗ[F4] W => f v) hsub
    · intro w hw
      have hTw : T w = w := by
        simpa [Module.End.one_apply] using sub_eq_zero.mp hw
      have hT2w : (T ^ 2) w = w := by
        rw [pow_two, Module.End.mul_apply, hTw, hTw]
      refine ⟨w, ?_⟩
      change w + T w + (T ^ 2) w = w
      rw [hTw, hT2w]
      have hww : w + w = 0 := by
        rw [← two_smul F4 w, F4.two_eq_zero, zero_smul]
      rw [hww]
      abel
  have h3 : (3 : F4) = 1 := by
    have h2 : (2 : F4) = 0 := F4.two_eq_zero
    calc (3 : F4) = (2 : F4) + 1 := by norm_num
      _ = 0 + 1 := by rw [h2]
      _ = 1 := zero_add 1
  have htraceP : LinearMap.trace F4 W P = 1 := by
    simp [P, htraceT, htraceT2, hW, h3]
  have htraceP' : LinearMap.trace F4 W P = (Module.finrank F4 (LinearMap.range P) : F4) :=
    hproj.trace
  have hcast : (Module.finrank F4 (LinearMap.range P) : F4) = 1 := by
    rw [← htraceP']
    exact htraceP
  have hle : Module.finrank F4 (LinearMap.range P) ≤ 3 := by
    have h := Submodule.finrank_le (LinearMap.range P)
    rwa [hW] at h
  have hρc_ne : ((ρ H27.c0 : W ≃ₗ[F4] W) : W →ₗ[F4] W) ≠ 1 := by
    intro h
    have htr := congrArg (LinearMap.trace F4 W) h
    rw [hρc] at htr
    simp [hW, h3] at htr
    exact hω1 htr
  have hne3 : Module.finrank F4 (LinearMap.range P) ≠ 3 := by
    intro hn
    have htop : LinearMap.range P = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hn, hW])
    have hP1 : P = 1 := by
      ext w
      have hw : w ∈ LinearMap.range P := by rw [htop]; trivial
      exact (hproj.mem_iff_map_id).mp hw
    have hT1 : T = 1 := by
      have := hTP
      rwa [hP1, mul_one] at this
    have hconj1 : (ρ y).conj T = ω • T := hconj
    rw [hT1] at hconj1
    have hconj_one : (ρ y).conj (1 : W →ₗ[F4] W) = 1 := by
      ext w
      simp [LinearEquiv.conj_apply]
    have hω1eq : (ω • (1 : W →ₗ[F4] W)) = 1 := by
      rw [← hconj1, hconj_one]
    have hρc1 : ((ρ H27.c0 : W ≃ₗ[F4] W) : W →ₗ[F4] W) = 1 := by
      rw [hρc]
      exact hω1eq
    exact hρc_ne hρc1
  have hn : Module.finrank F4 (LinearMap.range P) = 1 := by
    have h0 : (0 : F4) ≠ 1 := zero_ne_one
    have h2 : (2 : F4) ≠ 1 := by
      rw [F4.two_eq_zero]
      exact zero_ne_one
    interval_cases Module.finrank F4 (LinearMap.range P) <;> simp_all
  have hn' : Module.finrank F4
      (fixedSpace ((ρ x : W ≃ₗ[F4] W) : W →ₗ[F4] W)) = 1 := by
    change Module.finrank F4 (fixedSpace T) = 1
    rw [← hrange]
    exact hn
  simpa [fixedSpace] using hn' 


section F2

local instance : Algebra (ZMod 2) F4 := ZMod.algebra F4 2
local instance : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) F4)
local instance : IsScalarTower (ZMod 2) F4 W where
  smul_assoc r s w := by
    change (algebraMap (ZMod 2) F4 r * s) • w = algebraMap (ZMod 2) F4 r • (s • w)
    rw [mul_smul]

theorem finrank_f2_eq_two : Module.finrank (ZMod 2) F4 = 2 := by
  have hcard : 2 ^ Module.finrank (ZMod 2) F4 = 4 := by
    simpa [F4.card] using FiniteField.pow_finrank_eq_card 2 F4
  have hcard' : 2 ^ Module.finrank (ZMod 2) F4 = 2 ^ 2 := by
    simpa using hcard
  exact Nat.pow_right_injective (by norm_num) hcard'

theorem finrank_f2_eq_six (hW : Module.finrank F4 W = 3) :
    Module.finrank (ZMod 2) W = 6 := by
  have htower := Module.finrank_mul_finrank (ZMod 2) F4 W
  rw [finrank_f2_eq_two, hW] at htower
  simpa using htower.symm

theorem fixedSpace_finrank_f2_eq_two
    (ρ : H27 →* (W ≃ₗ[F4] W))
    {ω : F4} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hρc : ((ρ H27.c0 : W ≃ₗ[F4] W) : W →ₗ[F4] W) = ω • (1 : W →ₗ[F4] W))
    (hW : Module.finrank F4 W = 3)
    (x : H27) (hx : x ∉ Subgroup.center H27) :
    Module.finrank (ZMod 2) (fixedSpace ((ρ x : W ≃ₗ[F4] W) : W →ₗ[F4] W)) = 2 := by
  have hdim := fixedSpace_finrank_eq_one ρ hω3 hω1 hρc hW x hx
  have htower := Module.finrank_mul_finrank (ZMod 2) F4
    (fixedSpace ((ρ x : W ≃ₗ[F4] W) : W →ₗ[F4] W))
  rw [finrank_f2_eq_two, hdim] at htower
  simpa using htower.symm

end F2

end CFSG.GroupTheory.HeisenbergF4
