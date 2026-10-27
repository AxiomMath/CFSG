module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem sub_eq_add_zmod2 (u v : V) : u - v = u + v := by
  rw [sub_eq_iff_eq_add, add_assoc, add_self_zmod2, add_zero]

theorem finite_linearEquiv [FiniteDimensional (ZMod 2) V] : Finite (V ≃ₗ[ZMod 2] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) fun g h hgh =>
    LinearEquiv.ext fun v => congrFun hgh v

section Comm

variable (Y : Subgroup (V ≃ₗ[ZMod 2] V))

@[expose] def commSub (W : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  span (ZMod 2) {x | ∃ y ∈ Y, ∃ w ∈ W, y w - w = x}

@[expose] def iterComm (W : Submodule (ZMod 2) V) (k : ℕ) : Submodule (ZMod 2) V :=
  (commSub Y)^[k] W

@[expose] def IsInv (W : Submodule (ZMod 2) V) : Prop :=
  ∀ y ∈ Y, ∀ w ∈ W, y w ∈ W

@[expose] def IsUnip (A B : Submodule (ZMod 2) V) : Prop :=
  ∃ k, iterComm Y B k ≤ A

variable {Y}

theorem sub_mem_commSub {W : Submodule (ZMod 2) V} {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ Y) {w : V}
    (hw : w ∈ W) : y w - w ∈ commSub Y W :=
  subset_span ⟨y, hy, w, hw, rfl⟩

theorem commSub_le_iff {W A : Submodule (ZMod 2) V} :
    commSub Y W ≤ A ↔ ∀ y ∈ Y, ∀ w ∈ W, y w - w ∈ A := by
  rw [commSub, span_le]
  constructor
  · intro h y hy w hw
    exact h ⟨y, hy, w, hw, rfl⟩
  · rintro h _ ⟨y, hy, w, hw, rfl⟩
    exact h y hy w hw

theorem commSub_mono {W W' : Submodule (ZMod 2) V} (h : W ≤ W') : commSub Y W ≤ commSub Y W' :=
  commSub_le_iff.mpr fun _ hy _ hw => sub_mem_commSub hy (h hw)

theorem commSub_mono_left {Y' : Subgroup (V ≃ₗ[ZMod 2] V)} (h : Y ≤ Y')
    (W : Submodule (ZMod 2) V) : commSub Y W ≤ commSub Y' W :=
  commSub_le_iff.mpr fun _ hy _ hw => sub_mem_commSub (h hy) hw

@[simp] theorem commSub_bot : commSub Y (⊥ : Submodule (ZMod 2) V) = ⊥ :=
  eq_bot_iff.mpr (commSub_le_iff.mpr fun y _ w hw => by
    rw [mem_bot] at hw
    rw [hw, map_zero, sub_zero]
    exact zero_mem _)

theorem commSub_sup_le (W W' : Submodule (ZMod 2) V) :
    commSub Y (W ⊔ W') ≤ commSub Y W ⊔ commSub Y W' := by
  refine commSub_le_iff.mpr fun y hy v hv => ?_
  obtain ⟨w, hw, w', hw', rfl⟩ := mem_sup.mp hv
  have h : y (w + w') - (w + w') = (y w - w) + (y w' - w') := by rw [map_add]; abel
  rw [h]
  exact add_mem (mem_sup_left (sub_mem_commSub hy hw)) (mem_sup_right (sub_mem_commSub hy hw'))

theorem commSub_le_of_isInv {W : Submodule (ZMod 2) V} (hW : IsInv Y W) : commSub Y W ≤ W :=
  commSub_le_iff.mpr fun y hy w hw => sub_mem (hW y hy w hw) hw

theorem apply_mem_commSub {X : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V}
    {y : V ≃ₗ[ZMod 2] V} (hyX : ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hyW : ∀ w ∈ W, y w ∈ W) {v : V}
    (hv : v ∈ commSub X W) : y v ∈ commSub X W := by
  induction hv using span_induction with
  | mem _ hx =>
    obtain ⟨x, hxX, w, hw, rfl⟩ := hx
    have h : y (x w - w) = (y * x * y⁻¹) (y w) - y w := by simp
    rw [h]
    exact sub_mem_commSub (hyX x hxX) (hyW w hw)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact smul_mem _ c ha

theorem isInv_commSub {W : Submodule (ZMod 2) V} (hW : IsInv Y W) : IsInv Y (commSub Y W) :=
  fun y hy _ hv => apply_mem_commSub (fun _ hx => Y.mul_mem (Y.mul_mem hy hx) (Y.inv_mem hy))
    (hW y hy) hv

theorem isInv_bot : IsInv Y (⊥ : Submodule (ZMod 2) V) := fun y _ w hw => by
  rw [mem_bot] at hw ⊢
  rw [hw, map_zero]

theorem isInv_top : IsInv Y (⊤ : Submodule (ZMod 2) V) := fun _ _ _ _ => mem_top

theorem IsInv.inf {W W' : Submodule (ZMod 2) V} (hW : IsInv Y W) (hW' : IsInv Y W') :
    IsInv Y (W ⊓ W') := fun y hy _ hv => ⟨hW y hy _ hv.1, hW' y hy _ hv.2⟩

theorem IsInv.sup {W W' : Submodule (ZMod 2) V} (hW : IsInv Y W) (hW' : IsInv Y W') :
    IsInv Y (W ⊔ W') := fun y hy v hv => by
  obtain ⟨w, hw, w', hw', rfl⟩ := mem_sup.mp hv
  rw [map_add]
  exact add_mem (mem_sup_left (hW y hy w hw)) (mem_sup_right (hW' y hy w' hw'))

theorem IsInv.inv_apply_mem {W : Submodule (ZMod 2) V} (hW : IsInv Y W) {y : V ≃ₗ[ZMod 2] V}
    (hy : y ∈ Y) {w : V} (hw : w ∈ W) : y⁻¹ w ∈ W :=
  hW _ (Y.inv_mem hy) w hw

@[simp] theorem iterComm_zero (W : Submodule (ZMod 2) V) : iterComm Y W 0 = W := rfl

theorem iterComm_succ (W : Submodule (ZMod 2) V) (k : ℕ) :
    iterComm Y W (k + 1) = iterComm Y (commSub Y W) k :=
  Function.iterate_succ_apply _ _ _

theorem iterComm_succ' (W : Submodule (ZMod 2) V) (k : ℕ) :
    iterComm Y W (k + 1) = commSub Y (iterComm Y W k) :=
  Function.iterate_succ_apply' _ _ _

theorem iterComm_one (W : Submodule (ZMod 2) V) : iterComm Y W 1 = commSub Y W := rfl

theorem iterComm_add (W : Submodule (ZMod 2) V) (k l : ℕ) :
    iterComm Y W (k + l) = iterComm Y (iterComm Y W k) l := by
  rw [iterComm, iterComm, iterComm, add_comm, Function.iterate_add_apply]

theorem iterComm_mono {W W' : Submodule (ZMod 2) V} (h : W ≤ W') (k : ℕ) :
    iterComm Y W k ≤ iterComm Y W' k := by
  induction k with
  | zero => exact h
  | succ k ih => rw [iterComm_succ', iterComm_succ']; exact commSub_mono ih

theorem isInv_iterComm {W : Submodule (ZMod 2) V} (hW : IsInv Y W) (k : ℕ) :
    IsInv Y (iterComm Y W k) := by
  induction k with
  | zero => exact hW
  | succ k ih => rw [iterComm_succ']; exact isInv_commSub ih

theorem iterComm_le_of_isInv {W : Submodule (ZMod 2) V} (hW : IsInv Y W) (k : ℕ) :
    iterComm Y W k ≤ W := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [iterComm_succ']; exact (commSub_le_of_isInv (isInv_iterComm hW k)).trans ih

theorem iterComm_antitone {W : Submodule (ZMod 2) V} (hW : IsInv Y W) {k l : ℕ} (h : k ≤ l) :
    iterComm Y W l ≤ iterComm Y W k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [iterComm_add]
  exact iterComm_le_of_isInv (isInv_iterComm hW k) j

theorem iterComm_sup_le (W W' : Submodule (ZMod 2) V) (k : ℕ) :
    iterComm Y (W ⊔ W') k ≤ iterComm Y W k ⊔ iterComm Y W' k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterComm_succ', iterComm_succ', iterComm_succ']
    exact (commSub_mono ih).trans (commSub_sup_le _ _)

@[simp] theorem iterComm_bot (k : ℕ) : iterComm Y (⊥ : Submodule (ZMod 2) V) k = ⊥ :=
  le_bot_iff.mp (iterComm_le_of_isInv isInv_bot k)

theorem isUnip_self (A : Submodule (ZMod 2) V) : IsUnip Y A A := ⟨0, le_rfl⟩

theorem isUnip_of_commSub_le {A B : Submodule (ZMod 2) V} (h : commSub Y B ≤ A) :
    IsUnip Y A B :=
  ⟨1, h⟩

theorem IsUnip.mono {A A' B B' : Submodule (ZMod 2) V} (h : IsUnip Y A B) (hA : A ≤ A')
    (hB : B' ≤ B) : IsUnip Y A' B' :=
  let ⟨k, hk⟩ := h
  ⟨k, (iterComm_mono hB k).trans (hk.trans hA)⟩

theorem IsUnip.trans {A B C : Submodule (ZMod 2) V} (hAB : IsUnip Y A B) (hBC : IsUnip Y B C) :
    IsUnip Y A C := by
  obtain ⟨k, hk⟩ := hBC
  obtain ⟨l, hl⟩ := hAB
  exact ⟨k + l, by rw [iterComm_add]; exact (iterComm_mono hk l).trans hl⟩

theorem IsUnip.iterComm_le {A B : Submodule (ZMod 2) V} (hA : IsInv Y A) {k : ℕ}
    (hk : iterComm Y B k ≤ A) {m : ℕ} (hm : k ≤ m) : iterComm Y B m ≤ A := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [iterComm_add]
  exact (iterComm_mono hk j).trans (iterComm_le_of_isInv hA j)

theorem iterComm_mono_left {Y' : Subgroup (V ≃ₗ[ZMod 2] V)} (h : Y ≤ Y')
    (W : Submodule (ZMod 2) V) (k : ℕ) : iterComm Y W k ≤ iterComm Y' W k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterComm_succ', iterComm_succ']
    exact (commSub_mono_left h _).trans (commSub_mono ih)

theorem IsUnip.mono_left {Y' : Subgroup (V ≃ₗ[ZMod 2] V)} {A B : Submodule (ZMod 2) V}
    (h : IsUnip Y' A B) (hY : Y ≤ Y') : IsUnip Y A B :=
  let ⟨k, hk⟩ := h
  ⟨k, (iterComm_mono_left hY B k).trans hk⟩

theorem apply_mem_iterComm {X : Subgroup (V ≃ₗ[ZMod 2] V)} {W : Submodule (ZMod 2) V}
    {y : V ≃ₗ[ZMod 2] V} (hyX : ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hyW : ∀ w ∈ W, y w ∈ W) (k : ℕ) :
    ∀ v ∈ iterComm X W k, y v ∈ iterComm X W k := by
  induction k with
  | zero => exact hyW
  | succ k ih =>
    rw [iterComm_succ']
    exact fun v hv => apply_mem_commSub hyX ih hv

@[expose] def secCent (A B : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | (∀ b ∈ B, g b ∈ B) ∧ (∀ b ∈ B, g⁻¹ b ∈ B) ∧ ∀ b ∈ B, g b - b ∈ A}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
    · rw [LinearEquiv.mul_apply]; exact hg1 _ (hh1 b hb)
    · rw [mul_inv_rev, LinearEquiv.mul_apply]; exact hh2 _ (hg2 b hb)
    · have h : (g * h) b - b = (g (h b) - h b) + (h b - b) := by
        rw [LinearEquiv.mul_apply]; abel
      rw [h]
      exact add_mem (hg3 _ (hh1 b hb)) (hh3 b hb)
  one_mem' := ⟨fun _ hb => hb, fun _ hb => by simpa using hb, fun _ _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    refine ⟨hg2, fun b hb => by rw [inv_inv]; exact hg1 b hb, fun b hb => ?_⟩
    have h := hg3 _ (hg2 b hb)
    have h' : g (g⁻¹ b) = b := by simp
    rw [h'] at h
    have h'' : g⁻¹ b - b = -(b - g⁻¹ b) := by abel
    rw [h'']
    exact neg_mem h

theorem mem_secCent_of_isInv {A B : Submodule (ZMod 2) V} (hB : IsInv Y B)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ Y) (h : ∀ b ∈ B, g b - b ∈ A) : g ∈ secCent A B :=
  ⟨hB g hg, fun _ hb => hB.inv_apply_mem hg hb, h⟩

theorem commSub_le_of_le_secCent {K : Subgroup (V ≃ₗ[ZMod 2] V)} {A B : Submodule (ZMod 2) V}
    (hK : K ≤ secCent A B) : commSub K B ≤ A :=
  commSub_le_iff.mpr fun _ hk b hb => (hK hk).2.2 b hb

theorem conj_mem_secCent {A B : Submodule (ZMod 2) V} (hA : IsInv Y A) (hB : IsInv Y B)
    {y k : V ≃ₗ[ZMod 2] V} (hy : y ∈ Y) (hk : k ∈ secCent A B) : y * k * y⁻¹ ∈ secCent A B := by
  obtain ⟨hk1, hk2, hk3⟩ := hk
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩
  · simp only [LinearEquiv.mul_apply]
    exact hB y hy _ (hk1 _ (hB.inv_apply_mem hy hb))
  · simp only [mul_inv_rev, inv_inv, LinearEquiv.mul_apply]
    exact hB y hy _ (hk2 _ (hB.inv_apply_mem hy hb))
  · have h : (y * k * y⁻¹) b - b = y (k (y⁻¹ b) - y⁻¹ b) := by
      simp [LinearEquiv.mul_apply, map_sub]
    rw [h]
    exact hA y hy _ (hk3 _ (hB.inv_apply_mem hy hb))

theorem iterComm_eq_of_succ_eq {W : Submodule (ZMod 2) V} {n : ℕ}
    (hn : iterComm Y W (n + 1) = iterComm Y W n) {m : ℕ} (hm : n ≤ m) :
    iterComm Y W m = iterComm Y W n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [iterComm_succ', ih, ← iterComm_succ', hn]

variable (Y) in
@[expose] noncomputable def stab (W : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  iterComm Y W (finrank (ZMod 2) V)

theorem isUnip_stab (W : Submodule (ZMod 2) V) : IsUnip Y (stab Y W) W := ⟨_, le_rfl⟩

theorem isInv_stab {W : Submodule (ZMod 2) V} (hW : IsInv Y W) : IsInv Y (stab Y W) :=
  isInv_iterComm hW _

variable [FiniteDimensional (ZMod 2) V]

theorem exists_iterComm_succ_eq {W : Submodule (ZMod 2) V} (hW : IsInv Y W) :
    ∃ n ≤ finrank (ZMod 2) W, iterComm Y W (n + 1) = iterComm Y W n := by
  by_contra hne
  push Not at hne
  have key : ∀ k ≤ finrank (ZMod 2) W + 1,
      finrank (ZMod 2) (iterComm Y W k) + k ≤ finrank (ZMod 2) W := by
    intro k
    induction k with
    | zero => intro _; rw [iterComm_zero, add_zero]
    | succ k ih =>
      intro hk
      have hlt : iterComm Y W (k + 1) < iterComm Y W k :=
        lt_of_le_of_ne (iterComm_antitone hW (Nat.le_succ k)) (hne k (by omega))
      have h1 := Submodule.finrank_lt_finrank_of_lt hlt
      have h2 := ih (by omega)
      omega
  have := key _ le_rfl
  omega

theorem iterComm_eq_stab {W : Submodule (ZMod 2) V} (hW : IsInv Y W) {m : ℕ}
    (hm : finrank (ZMod 2) V ≤ m) : iterComm Y W m = stab Y W := by
  obtain ⟨n, hn, hsucc⟩ := exists_iterComm_succ_eq hW
  have hnV : n ≤ finrank (ZMod 2) V := hn.trans (Submodule.finrank_le W)
  rw [stab, iterComm_eq_of_succ_eq hsucc (hnV.trans hm), iterComm_eq_of_succ_eq hsucc hnV]

theorem commSub_stab {W : Submodule (ZMod 2) V} (hW : IsInv Y W) :
    commSub Y (stab Y W) = stab Y W := by
  rw [stab, ← iterComm_succ', iterComm_eq_stab hW (Nat.le_succ _), stab]

theorem iterComm_stab {W : Submodule (ZMod 2) V} (hW : IsInv Y W) (k : ℕ) :
    iterComm Y (stab Y W) k = stab Y W := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterComm_succ', ih, commSub_stab hW]

theorem IsUnip.stab_le {A W : Submodule (ZMod 2) V} (hA : IsInv Y A) (hW : IsInv Y W)
    (h : IsUnip Y A W) : stab Y W ≤ A := by
  obtain ⟨k, hk⟩ := h
  rw [← iterComm_eq_stab hW (le_max_right k (finrank (ZMod 2) V))]
  exact IsUnip.iterComm_le hA hk (le_max_left _ _)

theorem isUnip_bot_stab_iff {W : Submodule (ZMod 2) V} (hW : IsInv Y W) :
    IsUnip Y ⊥ (stab Y W) ↔ stab Y W = ⊥ := by
  constructor
  · rintro ⟨k, hk⟩
    rw [iterComm_stab hW] at hk
    exact le_bot_iff.mp hk
  · intro h
    rw [h]
    exact isUnip_self ⊥

end Comm

section Pow

variable {Y : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem pow_two_pow_sub_mem {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ Y) (j : ℕ) :
    ∀ {B : Submodule (ZMod 2) V} {v : V}, v ∈ B → (y ^ 2 ^ j) v - v ∈ iterComm Y B (2 ^ j) := by
  induction j with
  | zero =>
    intro B v hv
    rw [pow_zero, pow_one, iterComm_one]
    exact sub_mem_commSub hy hv
  | succ j ih =>
    intro B v hv
    have h2 := ih (ih hv)
    have hz : (y ^ 2 ^ (j + 1)) v - v =
        (y ^ 2 ^ j) ((y ^ 2 ^ j) v - v) - ((y ^ 2 ^ j) v - v) := by
      rw [pow_succ, pow_mul, sq, LinearEquiv.mul_apply, map_sub, sub_eq_add_zmod2, sub_eq_add_zmod2,
        sub_eq_add_zmod2, sub_eq_add_zmod2, add_assoc, ← add_assoc ((y ^ 2 ^ j) v), add_self_zmod2,
        zero_add]
    rw [hz, pow_succ, mul_two, iterComm_add]
    exact h2

theorem exists_pow_sub_mem {A B : Submodule (ZMod 2) V} (hA : IsInv Y A) (h : IsUnip Y A B)
    {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ Y) : ∃ j : ℕ, ∀ v ∈ B, (y ^ 2 ^ j) v - v ∈ A := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun v hv => IsUnip.iterComm_le hA hk Nat.lt_two_pow_self.le
    (pow_two_pow_sub_mem hy k hv)⟩

theorem isPGroup_of_isUnip {K : Subgroup (V ≃ₗ[ZMod 2] V)} (h : IsUnip K ⊥ ⊤) :
    IsPGroup 2 K := by
  rintro ⟨g, hg⟩
  obtain ⟨j, hj⟩ := exists_pow_sub_mem isInv_bot h hg
  refine ⟨j, Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
  have hv := hj v mem_top
  rw [mem_bot, sub_eq_zero] at hv
  simpa using hv

theorem exists_fixed_of_pow [FiniteDimensional (ZMod 2) V] {W : Submodule (ZMod 2) V}
    (hW : IsInv Y W) (hne : W ≠ ⊥) (h2 : ∀ y ∈ Y, ∃ j : ℕ, ∀ w ∈ W, (y ^ 2 ^ j) w = w) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ y ∈ Y, y w = w := by
  classical
  let _ : MulAction Y W :=
    { smul := fun y w => ⟨(y : V ≃ₗ[ZMod 2] V) w, hW y y.2 w w.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl }
  set σ := MulAction.toPermHom Y W
  have hP : IsPGroup 2 σ.range := by
    rintro ⟨_, ⟨y, rfl⟩⟩
    obtain ⟨j, hj⟩ := h2 y y.2
    refine ⟨j, Subtype.ext (Equiv.ext fun w => Subtype.ext ?_)⟩
    rw [Subgroup.coe_pow, ← map_pow]
    change ((y ^ 2 ^ j : Y) : V ≃ₗ[ZMod 2] V) w = w
    rw [Subgroup.coe_pow]
    exact hj w w.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hdvd : 2 ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (by rwa [Ne, Submodule.finrank_eq_zero])
  have h0 : (0 : W) ∈ MulAction.fixedPoints σ.range W := by
    rintro ⟨_, ⟨y, rfl⟩⟩
    exact Subtype.ext (map_zero (y : V ≃ₗ[ZMod 2] V))
  obtain ⟨w, hw, hw0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hdvd h0
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h.symm), fun y hy => ?_⟩
  exact congrArg Subtype.val (hw ⟨σ ⟨y, hy⟩, ⟨y, hy⟩, rfl⟩)

end Pow

section Form

variable {Y : Subgroup (V ≃ₗ[ZMod 2] V)} {f : LinearMap.BilinForm (ZMod 2) V}

theorem apply_apply_eq (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) {y : V ≃ₗ[ZMod 2] V}
    (hy : y ∈ Y) (u v : V) : f (y u) (y v) = f u v :=
  TauCeti.BilinForm.mem_isometryGroup_iff.mp (hY hy) u v

theorem apply_sub_eq (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) {y : V ≃ₗ[ZMod 2] V}
    (hy : y ∈ Y) (u v : V) : f (y u - u) v = f u (y⁻¹ v - v) := by
  have h := apply_apply_eq hY hy u (y⁻¹ v)
  have h' : f (y u) v = f u (y⁻¹ v) := by simpa using h
  rw [sub_eq_add_zmod2, sub_eq_add_zmod2, map_add, LinearMap.add_apply, map_add, h']

theorem isInv_orth (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) {W : Submodule (ZMod 2) V}
    (hW : IsInv Y W) : IsInv Y (f.orthogonal W) := by
  intro y hy v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro w hw
  have h := apply_apply_eq hY hy (y⁻¹ w) v
  have h' : f w (y v) = f (y⁻¹ w) v := by simpa using h
  rw [h']
  exact hv _ (hW.inv_apply_mem hy hw)

theorem commSub_orth_iff (hY : Y ≤ TauCeti.BilinForm.isometryGroup f)
    {A B : Submodule (ZMod 2) V} :
    (∀ a ∈ commSub Y A, ∀ b ∈ B, f a b = 0) ↔ (∀ a ∈ A, ∀ b ∈ commSub Y B, f a b = 0) := by
  constructor
  · intro h a ha b hb
    have hle : commSub Y B ≤ LinearMap.ker (f a) := commSub_le_iff.mpr fun y hy w hw => by
      rw [LinearMap.mem_ker]
      have h1 := apply_sub_eq hY (Y.inv_mem hy) a w
      rw [inv_inv] at h1
      rw [← h1]
      exact h _ (sub_mem_commSub (Y.inv_mem hy) ha) w hw
    exact hle hb
  · intro h a ha b hb
    have hle : commSub Y A ≤ LinearMap.ker (f.flip b) := commSub_le_iff.mpr fun y hy w hw => by
      rw [LinearMap.mem_ker]
      change f (y w - w) b = 0
      rw [apply_sub_eq hY hy]
      exact h w hw _ (sub_mem_commSub (Y.inv_mem hy) hb)
    exact hle ha

theorem iterComm_orth_iff (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) (k : ℕ)
    {A B : Submodule (ZMod 2) V} :
    (∀ a ∈ iterComm Y A k, ∀ b ∈ B, f a b = 0) ↔ (∀ a ∈ A, ∀ b ∈ iterComm Y B k, f a b = 0) := by
  induction k generalizing B with
  | zero => rfl
  | succ k ih =>
    rw [show iterComm Y A (k + 1) = commSub Y (iterComm Y A k) from iterComm_succ' A k,
      commSub_orth_iff hY, ih, ← iterComm_succ]

variable [FiniteDimensional (ZMod 2) V]

theorem iterComm_orth_le_iff (hf : f.Nondegenerate) (hr : f.IsRefl)
    (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) (k : ℕ) {A B : Submodule (ZMod 2) V} :
    iterComm Y (f.orthogonal A) k ≤ f.orthogonal B ↔ iterComm Y B k ≤ A := by
  have key : (iterComm Y (f.orthogonal A) k ≤ f.orthogonal B) ↔
      ∀ b ∈ B, ∀ x ∈ iterComm Y (f.orthogonal A) k, f b x = 0 := by
    constructor
    · intro h b hb x hx
      exact LinearMap.BilinForm.mem_orthogonal_iff.mp (h hx) b hb
    · intro h x hx
      exact LinearMap.BilinForm.mem_orthogonal_iff.mpr fun b hb => h b hb x hx
  rw [key, ← iterComm_orth_iff hY k]
  conv_rhs => rw [← LinearMap.BilinForm.orthogonal_orthogonal hf hr A]
  constructor
  · intro h a ha
    exact LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => hr _ _ (h a ha x hx)
  · intro h a ha x hx
    exact hr _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp (h ha) x hx)

theorem isUnip_orth_iff (hf : f.Nondegenerate) (hr : f.IsRefl)
    (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) {A B : Submodule (ZMod 2) V} :
    IsUnip Y (f.orthogonal B) (f.orthogonal A) ↔ IsUnip Y A B :=
  exists_congr fun k => iterComm_orth_le_iff hf hr hY k

theorem isUnip_orth_top_iff (hf : f.Nondegenerate) (hr : f.IsRefl)
    (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) {W : Submodule (ZMod 2) V} :
    IsUnip Y (f.orthogonal W) ⊤ ↔ IsUnip Y ⊥ W := by
  rw [← isUnip_orth_iff hf hr hY (A := ⊥), LinearMap.BilinForm.orthogonal_bot]

end Form

end CFSG.LargeExtraspecial.DW
