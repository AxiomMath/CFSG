module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Defs

variable {X : Type} [Group X] (V : Type) [Group V] [MulDistribMulAction X V]

@[expose] def fixSub (Y : Subgroup X) : Subgroup V where
  carrier := {v | ∀ y ∈ Y, y • v = v}
  mul_mem' := fun {a b} ha hb y hy => by simp [smul_mul', ha y hy, hb y hy]
  one_mem' := fun y _ => smul_one y
  inv_mem' := fun {a} ha y hy => by simp [smul_inv', ha y hy]

@[expose] def commSub (Y : Subgroup X) : Subgroup V :=
  Subgroup.closure {u : V | ∃ y ∈ Y, ∃ v : V, u = (y • v) * v⁻¹}

@[expose] noncomputable def shapeN : ℕ := Nat.log 2 (Nat.card V)

@[expose] noncomputable def shapeK (Y : Subgroup X) : ℕ := Nat.log 2 (Nat.card (fixSub V Y))

variable {V}

theorem mem_fixSub {Y : Subgroup X} {v : V} : v ∈ fixSub V Y ↔ ∀ y ∈ Y, y • v = v := Iff.rfl

theorem smul_mul_inv_mem_commSub {Y : Subgroup X} {y : X} (hy : y ∈ Y) (v : V) :
    (y • v) * v⁻¹ ∈ commSub V Y :=
  Subgroup.subset_closure ⟨y, hy, v, rfl⟩

theorem smul_mem_commSub {Y : Subgroup X} {x : X} (hx : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) {u : V}
    (hu : u ∈ commSub V Y) : x • u ∈ commSub V Y := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨y, hy, v, rfl⟩ := hu
    have h := smul_mul_inv_mem_commSub (V := V) (hx y hy) (x • v)
    simpa [smul_mul', smul_inv', smul_smul, mul_assoc] using h
  | one => simp [smul_one, one_mem]
  | mul a b _ _ ha hb => rw [smul_mul']; exact mul_mem ha hb
  | inv a _ ha => rw [smul_inv']; exact inv_mem ha

theorem smul_mem_commSub_of_mem {Y : Subgroup X} {y : X} (hy : y ∈ Y) {u : V}
    (hu : u ∈ commSub V Y) : y • u ∈ commSub V Y :=
  smul_mem_commSub (fun _ hy' => Y.mul_mem (Y.mul_mem hy hy') (Y.inv_mem hy)) hu

end Defs

section Comm

variable {X : Type} [Group X] (V : Type) [CommGroup V] [MulDistribMulAction X V]

@[expose] def avg (Y : Subgroup X) [Fintype Y] : V →* V where
  toFun v := ∏ y : Y, (y : X) • v
  map_one' := by simp [smul_one]
  map_mul' a b := by simp [smul_mul', Finset.prod_mul_distrib]

variable {V}

theorem avg_apply (Y : Subgroup X) [Fintype Y] (v : V) : avg V Y v = ∏ y : Y, (y : X) • v := rfl

theorem avg_mem_fixSub (Y : Subgroup X) [Fintype Y] (v : V) : avg V Y v ∈ fixSub V Y := by
  intro z hz
  rw [avg_apply]
  have : (z • ∏ y : Y, (y : X) • v) = ∏ y : Y, z • ((y : X) • v) :=
    map_prod (MulDistribMulAction.toMonoidHom V z) _ _
  rw [this]
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft (⟨z, hz⟩ : Y)) _ _ (fun y => rfl)

theorem avg_smul (Y : Subgroup X) [Fintype Y] {z : X} (hz : z ∈ Y) (v : V) :
    avg V Y (z • v) = avg V Y v := by
  rw [avg_apply, avg_apply]
  simp_rw [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight (⟨z, hz⟩ : Y)) _ _ (fun y => rfl)

omit [MulDistribMulAction X V] in
theorem prod_const_eq_self (Y : Subgroup X) [Fintype Y] (hV : ∀ v : V, v * v = 1)
    (hodd : Odd (Fintype.card Y)) (c : V) : ∏ _y : Y, c = c := by
  rw [Finset.prod_const, Finset.card_univ]
  obtain ⟨m, hm⟩ := hodd
  have : c ^ 2 = 1 := by rw [sq]; exact hV c
  rw [hm, pow_succ, pow_mul, this]; simp

theorem avg_of_mem_fixSub (Y : Subgroup X) [Fintype Y] (hV : ∀ v : V, v * v = 1)
    (hodd : Odd (Fintype.card Y)) {c : V} (hc : c ∈ fixSub V Y) : avg V Y c = c := by
  rw [avg_apply]
  have : ∀ y : Y, (y : X) • c = c := fun y => hc y y.2
  simp_rw [this]
  exact prod_const_eq_self Y hV hodd c

theorem avg_eq_one_of_mem_commSub (Y : Subgroup X) [Fintype Y] {u : V} (hu : u ∈ commSub V Y) :
    avg V Y u = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨y, hy, v, rfl⟩ := hu
    rw [map_mul, map_inv, avg_smul Y hy, mul_inv_cancel]
  | one => exact map_one _
  | mul a b _ _ ha hb => rw [map_mul, ha, hb, mul_one]
  | inv a _ ha => rw [map_inv, ha, inv_one]

theorem mul_avg_inv_mem_commSub (Y : Subgroup X) [Fintype Y] (hV : ∀ v : V, v * v = 1)
    (hodd : Odd (Fintype.card Y)) (v : V) : v * (avg V Y v)⁻¹ ∈ commSub V Y := by
  have h1 := prod_const_eq_self Y hV hodd v
  have h2 : v * (avg V Y v)⁻¹ = (∏ _y : Y, v) * (∏ y : Y, (y : X) • v)⁻¹ := by
    rw [h1]; rfl
  rw [h2, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Subgroup.prod_mem _ fun y _ => ?_
  have := inv_mem (smul_mul_inv_mem_commSub y.2 v)
  simpa using this

theorem commSub_inf_fixSub (Y : Subgroup X) [Fintype Y] (hV : ∀ v : V, v * v = 1)
    (hodd : Odd (Fintype.card Y)) : commSub V Y ⊓ fixSub V Y = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨h1, h2⟩
  have := avg_eq_one_of_mem_commSub Y h1
  rw [avg_of_mem_fixSub Y hV hodd h2] at this
  exact this

end Comm

section GO

variable {X : Type} [Group X] (V : Type) [Group V] [MulDistribMulAction X V]

structure GOPair (Y : Subgroup X) : Prop where
  exp_two : ∀ v : V, v * v = 1
  faithful : ∀ x : X, (∀ v : V, x • v = v) → x = 1
  isCyclic : IsCyclic Y
  odd_card : Odd (Nat.card Y)
  ne_bot : Y ≠ ⊥
  transitive : ∀ v ∈ commSub V Y, v ≠ 1 → ∀ w ∈ commSub V Y, w ≠ 1 → ∃ y ∈ Y, y • v = w
  fixSub_ne_bot : fixSub V Y ≠ ⊥
  inter_trivial : ∀ x₁ x₂ : X, x₁ • fixSub V Y ≠ x₂ • fixSub V Y →
    x₁ • fixSub V Y ⊓ x₂ • fixSub V Y = ⊥
  normal_in_stab : ∀ x : X, x • fixSub V Y = fixSub V Y → ∀ y ∈ Y, x * y * x⁻¹ ∈ Y

variable {V}

namespace GOPair

variable {Y : Subgroup X}

theorem mul_comm' (hGO : GOPair V Y) (a b : V) : a * b = b * a := by
  have h1 : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hGO.exp_two v)
  calc a * b = (a * b)⁻¹ := (h1 _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h1]

abbrev commGroup (hGO : GOPair V Y) : CommGroup V :=
  { ‹Group V› with mul_comm := hGO.mul_comm' }

theorem exists_decomp [Finite X] (hGO : GOPair V Y) (v : V) :
    ∃ c ∈ fixSub V Y, v * c⁻¹ ∈ commSub V Y := by
  classical
  let _ : CommGroup V := hGO.commGroup
  let _ : Fintype Y := Fintype.ofFinite Y
  have hodd : Odd (Fintype.card Y) := by
    rw [← Nat.card_eq_fintype_card]; exact hGO.odd_card
  exact ⟨avg V Y v, avg_mem_fixSub Y v, mul_avg_inv_mem_commSub Y hGO.exp_two hodd v⟩

theorem commSub_inf_fixSub' [Finite X] (hGO : GOPair V Y) :
    commSub V Y ⊓ fixSub V Y = ⊥ := by
  classical
  let _ : CommGroup V := hGO.commGroup
  let _ : Fintype Y := Fintype.ofFinite Y
  have hodd : Odd (Fintype.card Y) := by
    rw [← Nat.card_eq_fintype_card]; exact hGO.odd_card
  exact commSub_inf_fixSub Y hGO.exp_two hodd

theorem eq_one_of_mul_eq_one [Finite X] (hGO : GOPair V Y) {p c : V} (hp : p ∈ commSub V Y)
    (hc : c ∈ fixSub V Y) (h : p * c = 1) : p = 1 ∧ c = 1 := by
  have hpc : p = c⁻¹ := eq_inv_of_mul_eq_one_left h
  have hcinv : c⁻¹ ∈ fixSub V Y := Subgroup.inv_mem _ hc
  have : p ∈ commSub V Y ⊓ fixSub V Y := ⟨hp, by rw [hpc]; exact hcinv⟩
  rw [hGO.commSub_inf_fixSub'] at this
  have hp1 : p = 1 := this
  refine ⟨hp1, ?_⟩
  rw [hp1, one_mul] at h
  exact h

theorem decomp_unique [Finite X] (hGO : GOPair V Y) {p p' c c' : V} (hp : p ∈ commSub V Y)
    (hp' : p' ∈ commSub V Y) (hc : c ∈ fixSub V Y) (hc' : c' ∈ fixSub V Y) (h : p * c = p' * c') :
    p = p' ∧ c = c' := by
  let _ : CommGroup V := hGO.commGroup
  have h1 : (p * p'⁻¹) * (c * c'⁻¹) = 1 := by
    calc (p * p'⁻¹) * (c * c'⁻¹) = (p * c) * (p' * c')⁻¹ := by rw [mul_inv_rev]; ac_rfl
      _ = 1 := by rw [h, mul_inv_cancel]
  have := hGO.eq_one_of_mul_eq_one (mul_mem hp (inv_mem hp')) (mul_mem hc (inv_mem hc')) h1
  exact ⟨mul_inv_eq_one.1 this.1, mul_inv_eq_one.1 this.2⟩

theorem smul_commSub_of_stab (hGO : GOPair V Y) {x : X} (hx : x • fixSub V Y = fixSub V Y)
    {u : V} (hu : u ∈ commSub V Y) : x • u ∈ commSub V Y :=
  smul_mem_commSub (hGO.normal_in_stab x hx) hu

theorem smul_commSub_le (hGO : GOPair V Y) {x : X} (hx : x • fixSub V Y = fixSub V Y) :
    x • commSub V Y ≤ commSub V Y := by
  intro m hm
  obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
  exact hGO.smul_commSub_of_stab hx hs

theorem smul_commSub_eq (hGO : GOPair V Y) {x : X} (hx : x • fixSub V Y = fixSub V Y) :
    x • commSub V Y = commSub V Y := by
  have hx' : x⁻¹ • fixSub V Y = fixSub V Y := by
    rw [inv_smul_eq_iff]; exact hx.symm
  refine le_antisymm (hGO.smul_commSub_le hx) ?_
  have h2 := hGO.smul_commSub_le hx'
  have := (Subgroup.pointwise_smul_subset_iff (a := x⁻¹)).1 h2
  rwa [inv_inv] at this

theorem comm_Y (hGO : GOPair V Y) {a b : X} (ha : a ∈ Y) (hb : b ∈ Y) : a * b = b * a := by
  have := hGO.isCyclic
  have := (IsCyclic.commGroup (α := Y)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem eq_of_smul_eq [Finite X] (hGO : GOPair V Y) {y₁ y₂ : X} (h₁ : y₁ ∈ Y) (h₂ : y₂ ∈ Y)
    {v : V} (hv : v ∈ commSub V Y) (hv1 : v ≠ 1) (h : y₁ • v = y₂ • v) : y₁ = y₂ := by
  set g := y₁⁻¹ * y₂ with hg
  have hgY : g ∈ Y := Y.mul_mem (Y.inv_mem h₁) h₂
  have hgv : g • v = v := by rw [hg, mul_smul, ← h, inv_smul_smul]
  have hfix : ∀ w ∈ commSub V Y, g • w = w := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, smul_one]
    obtain ⟨z, hz, hzv⟩ := hGO.transitive v hv hv1 w hw hw1
    rw [← hzv, smul_smul, hGO.comm_Y hgY hz, ← smul_smul, hgv]
  have htriv : ∀ u : V, g • u = u := by
    intro u
    obtain ⟨c, hc, hp⟩ := hGO.exists_decomp u
    have hu : u = (u * c⁻¹) * c := by simp
    rw [hu, smul_mul', hfix _ hp, hc g hgY]
  have := hGO.faithful g htriv
  rw [hg, inv_mul_eq_one] at this
  exact this

theorem mem_fixSub_of_smul_eq [Finite X] (hGO : GOPair V Y) {y : X} (hy : y ∈ Y) (hy1 : y ≠ 1)
    {v : V} (h : y • v = v) : v ∈ fixSub V Y := by
  obtain ⟨c, hc, hp⟩ := hGO.exists_decomp v
  have hpfix : y • (v * c⁻¹) = v * c⁻¹ := by rw [smul_mul', smul_inv', h, hc y hy]
  have hp1 : v * c⁻¹ = 1 := by
    by_contra hne
    exact hy1 (hGO.eq_of_smul_eq hy Y.one_mem hp hne (by rw [one_smul]; exact hpfix))
  have : v = c := by simpa [mul_inv_eq_one] using hp1
  rwa [this]

theorem commSub_ne_bot [Finite X] (hGO : GOPair V Y) : commSub V Y ≠ ⊥ := by
  intro hbot
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra h
    exact hGO.ne_bot ((Subgroup.eq_bot_iff_forall _).2 fun y hy => by_contra fun h' => h ⟨y, hy, h'⟩)
  have : ∀ v : V, y • v = v := by
    intro v
    obtain ⟨c, hc, hp⟩ := hGO.exists_decomp v
    have hp1 : v * c⁻¹ = 1 := by rw [hbot] at hp; exact hp
    have hv : v = c := by simpa [mul_inv_eq_one] using hp1
    rw [hv]; exact hc y hy
  exact hy1 (hGO.faithful y this)

theorem card_Y_add_one [Finite X] [Finite V] (hGO : GOPair V Y) :
    Nat.card Y + 1 = Nat.card (commSub V Y) := by
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ commSub V Y, v ≠ 1 := by
    by_contra h
    exact hGO.commSub_ne_bot ((Subgroup.eq_bot_iff_forall _).2 fun v hv =>
      by_contra fun h' => h ⟨v, hv, h'⟩)
  have hcard : (Y : Set X).ncard = (((commSub V Y : Subgroup V) : Set V) \ {1}).ncard := by
    refine Set.ncard_congr (fun y _ => y • v₀) ?_ ?_ ?_
    · intro y hy
      refine ⟨smul_mem_commSub_of_mem hy hv₀, ?_⟩
      intro h
      apply hv₀1
      have : y • v₀ = y • (1 : V) := by rw [smul_one]; exact h
      exact (MulAction.injective y) this
    · intro a b ha hb hab
      exact hGO.eq_of_smul_eq ha hb hv₀ hv₀1 hab
    · intro w hw
      obtain ⟨hw1, hw2⟩ := hw
      obtain ⟨y, hy, hyv⟩ := hGO.transitive v₀ hv₀ hv₀1 w hw1 (by simpa using hw2)
      exact ⟨y, hy, hyv⟩
  have h1 : (((commSub V Y : Subgroup V) : Set V) \ {1}).ncard + 1 =
      ((commSub V Y : Subgroup V) : Set V).ncard :=
    Set.ncard_sdiff_singleton_add_one (Subgroup.one_mem _) (Set.toFinite _)
  rw [← hcard] at h1
  have e1 : Nat.card Y = (Y : Set X).ncard := Nat.card_coe_set_eq (Y : Set X)
  have e2 : Nat.card (commSub V Y) = ((commSub V Y : Subgroup V) : Set V).ncard :=
    Nat.card_coe_set_eq _
  rw [e1, e2, h1]

theorem isPGroup_two (hGO : GOPair V Y) : IsPGroup 2 V :=
  fun v => ⟨1, by rw [pow_one, sq]; exact hGO.exp_two v⟩

theorem exists_card_pow [Finite V] (hGO : GOPair V Y) (W : Subgroup V) :
    ∃ m : ℕ, Nat.card W = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (hGO.isPGroup_two.to_subgroup W).exists_card_eq

theorem card_mul [Finite X] [Finite V] (hGO : GOPair V Y) :
    Nat.card (commSub V Y) * Nat.card (fixSub V Y) = Nat.card V := by
  have hd : Disjoint (commSub V Y) (fixSub V Y) := by
    rw [disjoint_iff]; exact hGO.commSub_inf_fixSub'
  have hmul : ((commSub V Y : Subgroup V) : Set V) * (fixSub V Y : Set V) = Set.univ := by
    ext v
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    obtain ⟨c, hc, hp⟩ := hGO.exists_decomp v
    exact ⟨v * c⁻¹, hp, c, hc, by simp⟩
  exact (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd hmul).card_mul_card

theorem card_V [Finite V] (hGO : GOPair V Y) : Nat.card V = 2 ^ shapeN V := by
  obtain ⟨n, hn⟩ := hGO.exists_card_pow (⊤ : Subgroup V)
  have h : Nat.card V = 2 ^ n := by rwa [Subgroup.card_top] at hn
  rw [shapeN, h, Nat.log_pow (by norm_num)]

theorem card_fixSub [Finite V] (hGO : GOPair V Y) : Nat.card (fixSub V Y) = 2 ^ shapeK V Y := by
  obtain ⟨n, hn⟩ := hGO.exists_card_pow (fixSub V Y)
  rw [shapeK, hn, Nat.log_pow (by norm_num)]

theorem card_commSub [Finite X] [Finite V] (hGO : GOPair V Y) :
    Nat.card (commSub V Y) = 2 ^ (shapeN V - shapeK V Y) := by
  obtain ⟨a, ha⟩ := hGO.exists_card_pow (commSub V Y)
  have h := hGO.card_mul
  rw [ha, hGO.card_fixSub, hGO.card_V, ← pow_add] at h
  have := Nat.pow_right_injective (le_refl 2) h
  rw [ha]
  congr 1
  omega

end GOPair

end GO

end CFSG.GH74.Uniqueness.SU.SU2
