module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

abbrev Z3 := Fin 3 → ZMod 3

@[expose] def dot (φ x : Z3) : ZMod 3 := ∑ i, φ i * x i

@[expose] def Rset : Finset Z3 :=
  {![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 2, 0], ![1, 0, 1], ![1, 0, 2], ![0, 1, 1],
    ![0, 1, 2], ![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]}

theorem count_R : ∀ x : Z3, (Rset.filter (fun φ => dot φ x = 0)).card =
    if x = 0 then 13 else 4 := by
  decide

theorem card_N : ∀ φ ∈ Rset, (Finset.univ.filter (fun x : Z3 => dot φ x = 0)).card = 9 := by
  decide

theorem dot_add (φ x y : Z3) : dot φ (x + y) = dot φ x + dot φ y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem exists_ab : ∀ φ ∈ Rset, ∃ a b : Z3, dot φ a = 0 ∧ dot φ b = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
    a + b ≠ 0 ∧ a + b + b ≠ 0 := by
  decide

section

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def act (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) : Module.End K V :=
  ρ (Multiplicative.ofAdd x)

theorem act_add (ρ : Multiplicative Z3 →* Module.End K V) (x y : Z3) :
    act ρ (x + y) = act ρ x * act ρ y := by
  simp [act, ofAdd_add]

theorem act_zero (ρ : Multiplicative Z3 →* Module.End K V) : act ρ 0 = 1 := by
  simp [act]

theorem two_nsmul_eq_zero' [CharP K 2] (v : V) : (2 : ℕ) • v = 0 := by
  have h : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [two_nsmul, ← two_smul K, h, zero_smul]

theorem odd_nsmul_eq [CharP K 2] (n : ℕ) (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_comm, add_smul, mul_comm, mul_smul, two_nsmul_eq_zero' (K := K), smul_zero, add_zero,
    one_smul]

@[expose] noncomputable def eN (ρ : Multiplicative Z3 →* Module.End K V) (φ : Z3) :
    Module.End K V :=
  ∑ x ∈ Finset.univ.filter (fun x : Z3 => dot φ x = 0), act ρ x

theorem act_eN (ρ : Multiplicative Z3 →* Module.End K V) {φ y : Z3} (hy : dot φ y = 0) (v : V) :
    act ρ y (eN ρ φ v) = eN ρ φ v := by
  unfold eN
  simp only [LinearMap.sum_apply]
  rw [map_sum]
  refine Finset.sum_equiv (Equiv.addLeft y) ?_ ?_
  · intro x
    simp [dot_add, hy]
  · intro x _
    simp [act_add]

@[expose] def fixOf (ρ : Multiplicative Z3 →* Module.End K V) (S : Set Z3) : Submodule K V where
  carrier := {v | ∀ x ∈ S, act ρ x v = v}
  add_mem' := fun {u v} hu hv x hx => by rw [map_add, hu x hx, hv x hx]
  zero_mem' := fun x _ => map_zero _
  smul_mem' := fun c v hv x hx => by rw [map_smul, hv x hx]

theorem mem_fixOf {ρ : Multiplicative Z3 →* Module.End K V} {S : Set Z3} {v : V} :
    v ∈ fixOf ρ S ↔ ∀ x ∈ S, act ρ x v = v := Iff.rfl

theorem eN_mem_fixOf (ρ : Multiplicative Z3 →* Module.End K V) (φ : Z3) (v : V) :
    eN ρ φ v ∈ fixOf ρ {x | dot φ x = 0} := fun _ hy => act_eN ρ hy v

theorem eN_of_mem [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) {φ : Z3}
    (hφ : φ ∈ Rset) {v : V} (hv : v ∈ fixOf ρ {x | dot φ x = 0}) : eN ρ φ v = v := by
  unfold eN
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => v) (fun x hx => hv x (by simpa using hx)),
    Finset.sum_const, card_N φ hφ]
  exact odd_nsmul_eq (K := K) 9 (by decide) v

theorem sum_eN [CharP K 2] (ρ : Multiplicative Z3 →* Module.End K V) (v : V) :
    ∑ φ ∈ Rset, eN ρ φ v = v := by
  unfold eN
  simp only [LinearMap.sum_apply]
  have h1 : ∀ φ : Z3, ∑ x ∈ Finset.univ.filter (fun x : Z3 => dot φ x = 0), act ρ x v =
      ∑ x : Z3, if dot φ x = 0 then act ρ x v else 0 := fun φ => by
    rw [Finset.sum_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x : Z3, ∑ φ ∈ Rset, (if dot φ x = 0 then act ρ x v else 0) =
      (if x = 0 then 13 else 4) • act ρ x v := fun x => by
    rw [← count_R x, ← Finset.sum_filter, Finset.sum_const]
  simp only [h2]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Z3))]
  have h3 : ∑ x ∈ Finset.univ.erase (0 : Z3), (if x = 0 then 13 else 4) • act ρ x v = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hx0 := Finset.ne_of_mem_erase hx
    simp only [hx0, ↓reduceIte]
    rw [show (4 : ℕ) = 2 * 2 by rfl, mul_smul, two_nsmul_eq_zero' (K := K)]
  rw [h3, add_zero]
  simp only [↓reduceIte, act_zero]
  exact odd_nsmul_eq (K := K) 13 (by decide) v

theorem eq_of_add_eq_zero' [CharP K 2] {x y : V} (h : x + y = 0) : x = y := by
  have h2 : y + y = 0 := by rw [← two_nsmul]; exact two_nsmul_eq_zero' (K := K) y
  exact (eq_neg_of_add_eq_zero_left h).trans (neg_eq_of_add_eq_zero_right h2)

theorem exists_fixed_ab [CharP K 2] (a b : Module.End K V) (hab : a * b = b * a)
    (ha3 : a * a * a = 1) (hb3 : b * b * b = 1)
    (X : Submodule K V) (hXa : ∀ v ∈ X, a v ∈ X) (hXb : ∀ v ∈ X, b v ∈ X)
    (hnfa : ∀ v ∈ X, a v = v → v = 0) (hnfb : ∀ v ∈ X, b v = v → v = 0)
    {v : V} (hv : v ∈ X) (hv0 : v ≠ 0) :
    ∃ w ∈ X, w ≠ 0 ∧ ((a * b) w = w ∨ (a * b * b) w = w) := by
  have ca : ∀ w, a (a (a w)) = w := fun w => by
    have := congrArg (fun f : Module.End K V => f w) ha3
    simpa using this
  have cb : ∀ w, b (b (b w)) = w := fun w => by
    have := congrArg (fun f : Module.End K V => f w) hb3
    simpa using this
  have cab : ∀ w, a (b w) = b (a w) := fun w => by
    have := congrArg (fun f : Module.End K V => f w) hab
    simpa using this
  have ea : ∀ w ∈ X, w + a w + a (a w) = 0 := fun w hw => by
    refine hnfa _ (X.add_mem (X.add_mem hw (hXa w hw)) (hXa _ (hXa w hw))) ?_
    rw [map_add, map_add, ca]
    abel
  have eb : ∀ w ∈ X, w + b w + b (b w) = 0 := fun w hw => by
    refine hnfb _ (X.add_mem (X.add_mem hw (hXb w hw)) (hXb _ (hXb w hw))) ?_
    rw [map_add, map_add, cb]
    abel
  have hbb : b v + b (b v) = v := by
    have := eb v hv
    have h2 : v + (b v + b (b v)) = 0 := by rw [← this]; abel
    exact (eq_of_add_eq_zero' (K := K) h2).symm
  set w1 := a v + b (b v) with hw1
  have hw1X : w1 ∈ X := X.add_mem (hXa v hv) (hXb _ (hXb v hv))
  by_cases h0 : w1 = 0
  · refine ⟨v, hv, hv0, Or.inl ?_⟩
    have h1 : a v = b (b v) := eq_of_add_eq_zero' (K := K) h0
    show a (b v) = v
    rw [cab, h1, cb]
  · refine ⟨w1, hw1X, h0, Or.inr ?_⟩
    have e2 : a (b (b v)) + a (b v) = a v := by rw [← map_add, add_comm, hbb]
    have hsum : a w1 + b w1 = 0 := by
      calc a w1 + b w1 = a (a v) + (a (b (b v)) + a (b v)) + v := by
            simp only [hw1, map_add, ← cab v, cb]
            abel
        _ = v + a v + a (a v) := by rw [e2]; abel
        _ = 0 := ea v hv
    have h1 : a w1 = b w1 := eq_of_add_eq_zero' (K := K) hsum
    show a (b (b w1)) = w1
    rw [cab, cab, h1, cb]


theorem act_comm (ρ : Multiplicative Z3 →* Module.End K V) (x y : Z3) :
    act ρ x * act ρ y = act ρ y * act ρ x := by
  rw [← act_add, ← act_add, add_comm]

theorem act_eN_comm (ρ : Multiplicative Z3 →* Module.End K V) (φ y : Z3) (v : V) :
    eN ρ φ (act ρ y v) = act ρ y (eN ρ φ v) := by
  unfold eN
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, act_comm]

theorem act_three (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) :
    act ρ x * act ρ x * act ρ x = 1 := by
  rw [← act_add, ← act_add, ← act_zero ρ]
  congr 1
  funext i
  simp
  generalize x i = t
  revert t
  decide

@[expose] def GoodElt (ρ : Multiplicative Z3 →* Module.End K V) (x : Z3) : Prop :=
  x ≠ 0 ∧ 4 ≤ finrank K (fixOf ρ {x}) ∧ ∃ y : Z3, ∃ u ∈ fixOf ρ {x}, act ρ y u ≠ u

theorem fixOf_N_le [CharP K 2] [FiniteDimensional K V] (ρ : Multiplicative Z3 →* Module.End K V)
    (hfaith : ∀ x, act ρ x = 1 → x = 0)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp1 : ∀ x : Z3, x ≠ 0 → Even (finrank K (fixOf ρ {x})))
    {φ : Z3} (hφ : φ ∈ Rset) :
    fixOf ρ {x | dot φ x = 0} ≤ ⨆ x ∈ {x | GoodElt ρ x}, fixOf ρ {x} := by
  set N : Set Z3 := {x | dot φ x = 0} with hN
  set F := fixOf ρ N with hF
  by_cases hF0 : F = ⊥
  · rw [hF0]; exact bot_le
  obtain ⟨a, b, ha, hb, ha0, hb0, hab0, hab0'⟩ := exists_ab φ hφ
  let X : Submodule K V := LinearMap.ker (eN ρ φ)
  have hXmem : ∀ w, w ∈ X ↔ eN ρ φ w = 0 := fun w => LinearMap.mem_ker
  have hXinv : ∀ y, dot φ y = 0 → ∀ w ∈ X, act ρ y w ∈ X := fun y _ w hw => by
    rw [hXmem, act_eN_comm, (hXmem w).1 hw, map_zero]
  have hFX : ∀ w ∈ X, w ∈ F → w = 0 := fun w hw hwF => by
    rw [← eN_of_mem ρ hφ hwF]; exact (hXmem w).1 hw
  obtain ⟨w₁, hw₁X, hw₁0⟩ : ∃ w₁ ∈ X, w₁ ≠ 0 := by
    have : act ρ a ≠ 1 := fun h => ha0 (hfaith a h)
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, act ρ a v₀ ≠ v₀ := by
      by_contra hcon
      push Not at hcon
      exact this (LinearMap.ext fun v => by simpa using hcon v)
    refine ⟨v₀ - eN ρ φ v₀, ?_, fun h0 => hv₀ ?_⟩
    · rw [hXmem, map_sub, eN_of_mem ρ hφ (eN_mem_fixOf ρ φ v₀), sub_self]
    · have h1 : v₀ = eN ρ φ v₀ := sub_eq_zero.1 h0
      have := eN_mem_fixOf ρ φ v₀
      rw [← h1] at this
      exact this a ha
  obtain ⟨x₀, hx₀N, hx₀0, w, hwX, hw0, hwx⟩ : ∃ x₀ : Z3, dot φ x₀ = 0 ∧ x₀ ≠ 0 ∧
      ∃ w ∈ X, w ≠ 0 ∧ act ρ x₀ w = w := by
    by_cases hxa : ∃ w ∈ X, w ≠ 0 ∧ act ρ a w = w
    · obtain ⟨w, hw, hw0, hwa⟩ := hxa
      exact ⟨a, ha, ha0, w, hw, hw0, hwa⟩
    by_cases hxb : ∃ w ∈ X, w ≠ 0 ∧ act ρ b w = w
    · obtain ⟨w, hw, hw0, hwb⟩ := hxb
      exact ⟨b, hb, hb0, w, hw, hw0, hwb⟩
    push Not at hxa hxb
    obtain ⟨w, hw, hw0, hw'⟩ := exists_fixed_ab (K := K) (act ρ a) (act ρ b) (act_comm ρ a b)
      (act_three ρ a) (act_three ρ b) X (hXinv a ha) (hXinv b hb)
      (fun v hv hva => by_contra fun hv0 => hxa v hv hv0 hva)
      (fun v hv hvb => by_contra fun hv0 => hxb v hv hv0 hvb) hw₁X hw₁0
    rcases hw' with h | h
    · refine ⟨a + b, by rw [dot_add, ha, hb, add_zero], hab0, w, hw, hw0, ?_⟩
      rw [act_add]; exact h
    · refine ⟨a + b + b, by rw [dot_add, dot_add, ha, hb, add_zero, add_zero], hab0', w, hw, hw0,
        ?_⟩
      rw [act_add, act_add]; exact h
  have hx₀N' : x₀ ∈ N := hx₀N
  have hFle : F ≤ fixOf ρ {x₀} := fun v hv x hx => by
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hv x₀ hx₀N'
  have hspan : (K ∙ w) ≤ fixOf ρ {x₀} := by
    rw [Submodule.span_le]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hwx
  have hdisj : F ⊓ (K ∙ w) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvF, hvw⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvw
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      have : w ∈ F := by
        have := F.smul_mem c⁻¹ hvF
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      exact hw0 (hFX w hwX this)
  have hF2 : 2 ≤ finrank K F := by
    have hpos : 0 < finrank K F :=
      Nat.pos_of_ne_zero fun h => hF0 (Submodule.finrank_eq_zero.1 h)
    obtain ⟨k, hk⟩ : ∃ k, finrank K F = k + k := hpN φ hφ
    omega
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq F (K ∙ w)
  rw [hdisj, finrank_bot, finrank_span_singleton hw0] at hsup
  have hle : finrank K (F ⊔ (K ∙ w) : Submodule K V) ≤ finrank K (fixOf ρ {x₀}) :=
    Submodule.finrank_mono (sup_le hFle hspan)
  have h4 : 4 ≤ finrank K (fixOf ρ {x₀}) := by
    obtain ⟨k, hk⟩ := hp1 x₀ hx₀0
    omega
  have hgood : GoodElt ρ x₀ := by
    refine ⟨hx₀0, h4, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hw0
    refine hFX w hwX fun y _ => ?_
    exact hcon y w (fun x hx => by rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hwx)
  exact hFle.trans (le_iSup₂_of_le x₀ hgood le_rfl)

theorem cover [CharP K 2] [FiniteDimensional K V] (ρ : Multiplicative Z3 →* Module.End K V)
    (hfaith : ∀ x, act ρ x = 1 → x = 0)
    (hpN : ∀ φ ∈ Rset, Even (finrank K (fixOf ρ {x | dot φ x = 0})))
    (hp1 : ∀ x : Z3, x ≠ 0 → Even (finrank K (fixOf ρ {x}))) :
    (⊤ : Submodule K V) ≤ ⨆ x ∈ {x | GoodElt ρ x}, fixOf ρ {x} := by
  intro v _
  rw [← sum_eN (K := K) ρ v]
  exact Submodule.sum_mem _ fun φ hφ =>
    fixOf_N_le ρ hfaith hpN hp1 hφ (eN_mem_fixOf ρ φ v)

end

end CFSG.HardMathSupport.Timmesfeld.CrossChar
