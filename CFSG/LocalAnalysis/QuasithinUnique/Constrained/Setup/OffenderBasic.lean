module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open Module

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : Type*} [Group A]

@[expose] def fixSub (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) : Submodule k V where
  carrier := {v | ∀ b ∈ B, ρ b v = v}
  zero_mem' := fun b _ => map_zero _
  add_mem' := fun {x y} hx hy b hb => by rw [map_add, hx b hb, hy b hb]
  smul_mem' := fun c v hv b hb => by rw [map_smul, hv b hb]

theorem mem_fixSub {ρ : A →* (V ≃ₗ[k] V)} {B : Subgroup A} {v : V} :
    v ∈ fixSub ρ B ↔ ∀ b ∈ B, ρ b v = v := Iff.rfl

@[expose] noncomputable def weight (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) : ℕ :=
  Nat.card B * Nat.card (fixSub ρ B)

@[expose] def centSub (ρ : A →* (V ≃ₗ[k] V)) (U : Submodule k V) : Subgroup A where
  carrier := {a | ∀ u ∈ U, ρ a u = u}
  one_mem' := fun u _ => by simp
  mul_mem' := fun {a b} ha hb u hu => by rw [map_mul, LinearEquiv.mul_apply, hb u hu, ha u hu]
  inv_mem' := fun {a} ha u hu => by
    have := ha u hu
    rw [map_inv]
    exact (LinearEquiv.symm_apply_eq _).mpr this.symm

theorem mem_centSub {ρ : A →* (V ≃ₗ[k] V)} {U : Submodule k V} {a : A} :
    a ∈ centSub ρ U ↔ ∀ u ∈ U, ρ a u = u := Iff.rfl

@[expose] def commSub (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) (U : Submodule k V) :
    Submodule k V :=
  Submodule.span k {w | ∃ b ∈ B, ∃ u ∈ U, w = ρ b u - u}

@[expose] def QuadAct (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) : Prop :=
  ∀ b ∈ B, ∀ c ∈ B, ∀ v : V, ρ c (ρ b v - v) = ρ b v - v

@[expose] def IsInvariant (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) (U : Submodule k V) : Prop :=
  ∀ b ∈ B, ∀ u ∈ U, ρ b u ∈ U

theorem ρ_inv_apply (ρ : A →* (V ≃ₗ[k] V)) (a : A) (x : V) : ρ a⁻¹ (ρ a x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem ρ_apply_inv (ρ : A →* (V ≃ₗ[k] V)) (a : A) (x : V) : ρ a (ρ a⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem ρ_mul_apply (ρ : A →* (V ≃ₗ[k] V)) (a b : A) (x : V) : ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]; rfl

theorem fixSub_anti (ρ : A →* (V ≃ₗ[k] V)) {B C : Subgroup A} (h : B ≤ C) :
    fixSub ρ C ≤ fixSub ρ B := fun _ hv b hb => hv b (h hb)

theorem fixSub_bot (ρ : A →* (V ≃ₗ[k] V)) : fixSub ρ ⊥ = ⊤ := by
  ext v
  simp [mem_fixSub]

theorem weight_bot (ρ : A →* (V ≃ₗ[k] V)) : weight ρ ⊥ = Nat.card V := by
  rw [weight, fixSub_bot, Subgroup.card_bot, one_mul]
  exact Nat.card_congr (Submodule.topEquiv (R := k) (M := V)).toEquiv

theorem weight_pos [Finite A] [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) :
    0 < weight ρ B :=
  Nat.mul_pos Nat.card_pos Nat.card_pos

theorem map_mem_fixSub_iff (ρ : A →* (V ≃ₗ[k] V)) {B : Subgroup A} {a : A} (ha : a ∈ B) (x : V) :
    ρ a x ∈ fixSub ρ B ↔ x ∈ fixSub ρ B := by
  constructor
  · intro h
    have h1 := h a⁻¹ (B.inv_mem ha)
    rw [ρ_inv_apply] at h1
    rw [h1]; exact h
  · intro h
    rw [h a ha]; exact h

theorem natCard_sup_mul_natCard_inf [Finite V] (X Y : Submodule k V) :
    Nat.card ↥(X ⊔ Y) * Nat.card ↥(X ⊓ Y) = Nat.card ↥X * Nat.card ↥Y := by
  have : Module.Finite k V := Module.Finite.of_finite
  have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [Module.natCard_eq_pow_finrank (K := k) (V := ↥(X ⊔ Y)),
    Module.natCard_eq_pow_finrank (K := k) (V := ↥(X ⊓ Y)),
    Module.natCard_eq_pow_finrank (K := k) (V := ↥X),
    Module.natCard_eq_pow_finrank (K := k) (V := ↥Y), ← pow_add, ← pow_add, h]

theorem natCard_dvd_of_le [Finite V] {X Z : Submodule k V} (h : X ≤ Z) :
    Nat.card ↥X ∣ Nat.card ↥Z := by
  have : Module.Finite k V := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := k) (V := ↥X),
    Module.natCard_eq_pow_finrank (K := k) (V := ↥Z)]
  exact pow_dvd_pow _ (Submodule.finrank_mono h)

theorem submodule_eq_of_le_of_card_ge [Finite V] {X Z : Submodule k V} (h : X ≤ Z)
    (hc : Nat.card ↥Z ≤ Nat.card ↥X) : X = Z := by
  have := AddSubgroup.eq_of_le_of_card_ge (H := X.toAddSubgroup) (K := Z.toAddSubgroup)
    (Submodule.toAddSubgroup_mono h) hc
  exact Submodule.toAddSubgroup_injective this

theorem isElementaryAbelian_subgroup {p : ℕ} [hA : CFSG.IsElementaryAbelian p A]
    (B : Subgroup A) : CFSG.IsElementaryAbelian p B where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hA.exponent_dvd_p (x : A)
    simpa using this

theorem exists_maxWeight_minimalSubgroup [Finite A] [Nontrivial A] (ρ : A →* (V ≃ₗ[k] V))
    (h : Nat.card V ≤ weight ρ ⊤) :
    ∃ B : Subgroup A, B ≠ ⊥ ∧ weight ρ ⊤ ≤ weight ρ B ∧
      (∀ D, D ≤ B → weight ρ D ≤ weight ρ B) ∧
      (∀ D, ⊥ < D → D < B → weight ρ D < weight ρ B) ∧
      ∀ p : ℕ, CFSG.IsElementaryAbelian p A → CFSG.IsElementaryAbelian p B := by
  classical
  obtain ⟨M, hM⟩ := Finite.exists_max (weight ρ)
  have hex : ∃ B : Subgroup A, B ≠ ⊥ ∧ weight ρ B = weight ρ M := by
    by_cases hMbot : M = ⊥
    · refine ⟨⊤, top_ne_bot, le_antisymm (hM _) ?_⟩
      rw [hMbot, weight_bot]
      exact h
    · exact ⟨M, hMbot, rfl⟩
  obtain ⟨B, ⟨hBbot, hBw⟩, hBmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup A))
    {B : Subgroup A | B ≠ ⊥ ∧ weight ρ B = weight ρ M} hex
  refine ⟨B, hBbot, hBw ▸ hM _, fun D _ => hBw ▸ hM D, fun D hDbot hDB => ?_, fun p hp => ?_⟩
  · refine lt_of_le_of_ne (hBw ▸ hM D) fun heq => hBmin D ⟨(bot_lt_iff_ne_bot.1 hDbot), ?_⟩ hDB
    rw [heq, hBw]
  · have := hp
    exact isElementaryAbelian_subgroup B

@[expose] def orbitDiff (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) (v : V) : Submodule k V :=
  Submodule.span k {w | ∃ b ∈ B, w = ρ b v - v}

theorem comm_aux (ρ : A →* (V ≃ₗ[k] V)) {a c : A} (hac : a * c = c * a) (v : V) :
    ρ a (ρ c v - v) - (ρ c v - v) = ρ c (ρ a v - v) - (ρ a v - v) := by
  have h : ρ a (ρ c v) = ρ c (ρ a v) := by
    rw [← ρ_mul_apply, hac, ρ_mul_apply]
  rw [map_sub, map_sub, h]
  abel

theorem diff_eq (ρ : A →* (V ≃ₗ[k] V)) (a a' : A) (v : V) :
    (ρ a' v - v) - (ρ a v - v) = ρ a (ρ (a⁻¹ * a') v - v) := by
  rw [map_sub, ρ_mul_apply, ρ_apply_inv ρ]
  abel

theorem mem_centSub_orbitDiff_iff (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (v : V) {c : A} (hc : c ∈ B) :
    c ∈ centSub ρ (orbitDiff ρ B v) ↔ ρ c v - v ∈ fixSub ρ B := by
  constructor
  · intro h a ha
    have h1 : ρ c (ρ a v - v) = ρ a v - v := h _ (Submodule.subset_span ⟨a, ha, rfl⟩)
    have := comm_aux ρ (hcomm a ha c hc) v
    rw [h1, sub_self, sub_eq_zero] at this
    exact this
  · intro h u hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, rfl⟩ := hw
      have := comm_aux ρ (hcomm a ha c hc) v
      rw [h a ha, sub_self] at this
      exact sub_eq_zero.1 this.symm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul r x _ hx => rw [map_smul, hx]

theorem two_pow_prime_pow {p : ℕ} [Fact p.Prime] [CharP k p] (m : ℕ) : (2 : k) ^ p ^ m = 2 := by
  have : ExpChar k p := ExpChar.prime (Fact.out)
  rw [← one_add_one_eq_two, add_pow_char_pow, one_pow]

theorem map_pow_of_eq_two_smul_add (ρ : A →* (V ≃ₗ[k] V)) (a : A) (v y : V) (hy : ρ a y = y)
    (h : ρ a v = (2 : k) • v + y) (n : ℕ) :
    ρ (a ^ n) v = (2 : k) ^ n • v + ((2 : k) ^ n - 1) • y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ρ_mul_apply, ih, map_add, map_smul, map_smul, h, hy]
    module

theorem count_core [Finite A] [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (B B' : Subgroup A) (hB'B : B' ≤ B)
    (δ : A → V) (hfix : ∀ a ∈ B, δ a ∈ fixSub ρ B')
    (hcos : ∀ a ∈ B, ∀ a' ∈ B, (δ a' - δ a ∈ fixSub ρ B ↔ a⁻¹ * a' ∈ B'))
    (hmax : weight ρ B' ≤ weight ρ B) :
    weight ρ B' = weight ρ B ∧ ∀ x ∈ fixSub ρ B', ∃ a ∈ B, x - δ a ∈ fixSub ρ B := by
  have hYX : fixSub ρ B ≤ fixSub ρ B' := fixSub_anti ρ hB'B
  set S : Submodule k (fixSub ρ B') := (fixSub ρ B).comap (fixSub ρ B').subtype with hS
  have hfinQ : Finite (fixSub ρ B' ⧸ S) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := S)) (Submodule.Quotient.mk_surjective S)
  let f : (B ⧸ B'.subgroupOf B) → (fixSub ρ B' ⧸ S) :=
    Quotient.lift (s := QuotientGroup.leftRel (B'.subgroupOf B))
      (fun a : B => Submodule.Quotient.mk (⟨δ a, hfix a a.2⟩ : fixSub ρ B')) (by
        intro a a' h
        have h1 := QuotientGroup.leftRel_apply.mp h
        rw [Subgroup.mem_subgroupOf] at h1
        rw [Submodule.Quotient.eq, hS, Submodule.mem_comap]
        have := (fixSub ρ B).neg_mem ((hcos a a.2 a' a'.2).2 h1)
        rw [neg_sub] at this
        simpa using this)
  have finj : Function.Injective f := by
    intro q q'
    induction q using QuotientGroup.induction_on with | _ a =>
    induction q' using QuotientGroup.induction_on with | _ a' =>
    intro h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h' : Submodule.Quotient.mk (⟨δ a, hfix a a.2⟩ : fixSub ρ B') =
        Submodule.Quotient.mk (⟨δ a', hfix a' a'.2⟩ : fixSub ρ B') := h
    rw [Submodule.Quotient.eq, hS, Submodule.mem_comap] at h'
    refine (hcos a a.2 a' a'.2).1 ?_
    have h'' : δ a - δ a' ∈ fixSub ρ B := by simpa using h'
    have := (fixSub ρ B).neg_mem h''
    rwa [neg_sub] at this
  have hcardB := Subgroup.card_eq_card_quotient_mul_card_subgroup (B'.subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'B).toEquiv] at hcardB
  have hcardX := Submodule.card_eq_card_quotient_mul_card S
  rw [Nat.card_congr (Submodule.comapSubtypeEquivOfLe hYX).toEquiv] at hcardX
  have hle : Nat.card (B ⧸ B'.subgroupOf B) ≤ Nat.card (fixSub ρ B' ⧸ S) :=
    Nat.card_le_card_of_injective f finj
  unfold weight at hmax ⊢
  have hpos1 : 0 < Nat.card B' := Nat.card_pos
  have hpos2 : 0 < Nat.card (fixSub ρ B) := Nat.card_pos
  have hge : Nat.card (fixSub ρ B' ⧸ S) ≤ Nat.card (B ⧸ B'.subgroupOf B) := by
    rw [hcardB, hcardX] at hmax
    have h3 : (Nat.card B' * Nat.card (fixSub ρ B)) * Nat.card (fixSub ρ B' ⧸ S) ≤
        (Nat.card B' * Nat.card (fixSub ρ B)) * Nat.card (B ⧸ B'.subgroupOf B) := by
      calc _ = Nat.card B' * (Nat.card (fixSub ρ B) * Nat.card (fixSub ρ B' ⧸ S)) := by ring
        _ ≤ Nat.card (B ⧸ B'.subgroupOf B) * Nat.card B' * Nat.card (fixSub ρ B) := hmax
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left h3 (Nat.mul_pos hpos1 hpos2)
  have heq : Nat.card (B ⧸ B'.subgroupOf B) = Nat.card (fixSub ρ B' ⧸ S) := le_antisymm hle hge
  have fbij : Function.Bijective f := finj.bijective_of_nat_card_le hge
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hcardB, hcardX, ← heq]; ring
  · obtain ⟨q, hq⟩ := fbij.2 (Submodule.Quotient.mk (⟨x, hx⟩ : fixSub ρ B'))
    induction q using QuotientGroup.induction_on with | _ a =>
    have h' : Submodule.Quotient.mk (⟨δ a, hfix a a.2⟩ : fixSub ρ B') =
        Submodule.Quotient.mk (⟨x, hx⟩ : fixSub ρ B') := hq
    rw [Submodule.Quotient.eq, hS, Submodule.mem_comap] at h'
    refine ⟨a, a.2, ?_⟩
    have h'' : δ a - x ∈ fixSub ρ B := by simpa using h'
    have := (fixSub ρ B).neg_mem h''
    rwa [neg_sub] at this

variable {p : ℕ} [Fact p.Prime] [CharP k p]

theorem orbitDiff_centralizer [Finite A] [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A)
    (hB : B ≠ ⊥) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hp : ∀ x ∈ B, ∃ n : ℕ, x ^ (p ^ n) = 1)
    (hmax : ∀ D : Subgroup A, D ≤ B → weight ρ D ≤ weight ρ B) (v : V) :
    B ⊓ centSub ρ (orbitDiff ρ B v) ≠ ⊥ ∧
      weight ρ (B ⊓ centSub ρ (orbitDiff ρ B v)) = weight ρ B ∧
      (∀ a ∈ B, ρ a v - v ∈ fixSub ρ (B ⊓ centSub ρ (orbitDiff ρ B v))) ∧
      (∀ a ∈ B, ∀ a' ∈ B, ((ρ a' v - v) - (ρ a v - v) ∈ fixSub ρ B ↔
          a⁻¹ * a' ∈ B ⊓ centSub ρ (orbitDiff ρ B v))) ∧
      (∀ x ∈ fixSub ρ (B ⊓ centSub ρ (orbitDiff ρ B v)),
          ∃ a ∈ B, x - (ρ a v - v) ∈ fixSub ρ B) := by
  set W := orbitDiff ρ B v with hW
  set B' := B ⊓ centSub ρ W with hB'
  have hB'B : B' ≤ B := inf_le_left
  have hfix : ∀ a ∈ B, ρ a v - v ∈ fixSub ρ B' := by
    intro a ha b hb
    exact hb.2 _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  have hmem : ∀ c ∈ B, c ∈ B' ↔ ρ c v - v ∈ fixSub ρ B := fun c hc =>
    ⟨fun h => (mem_centSub_orbitDiff_iff ρ B hcomm v hc).1 h.2,
      fun h => ⟨hc, (mem_centSub_orbitDiff_iff ρ B hcomm v hc).2 h⟩⟩
  have hcos : ∀ a ∈ B, ∀ a' ∈ B, ((ρ a' v - v) - (ρ a v - v) ∈ fixSub ρ B ↔ a⁻¹ * a' ∈ B') := by
    intro a ha a' ha'
    rw [diff_eq ρ a a' v, map_mem_fixSub_iff ρ ha]
    exact (hmem _ (B.mul_mem (B.inv_mem ha) ha')).symm
  obtain ⟨hweq, hsurj⟩ := count_core ρ B B' hB'B (fun a => ρ a v - v) hfix hcos (hmax B' hB'B)
  refine ⟨?_, hweq, hfix, hcos, hsurj⟩
  intro hbot
  have hXtop : fixSub ρ B' = ⊤ := by rw [hbot, fixSub_bot]
  obtain ⟨a, ha, hya⟩ := hsurj v (by rw [hXtop]; trivial)
  set y := ρ a v - (2 : k) • v with hy
  have hyY : y ∈ fixSub ρ B := by
    have : y = -(v - (ρ a v - v)) := by rw [hy]; module
    rw [this]; exact (fixSub ρ B).neg_mem hya
  have hay : ρ a y = y := hyY a ha
  have hav : ρ a v = (2 : k) • v + y := by rw [hy]; module
  obtain ⟨n, hn⟩ := hp a ha
  have key := map_pow_of_eq_two_smul_add ρ a v y hay hav (p ^ n)
  rw [hn, map_one, two_pow_prime_pow] at key
  have key' : v = (2 : k) • v + ((2 : k) - 1) • y := key
  have hvy : v = -y := by
    have h0 : v + y = (2 : k) • v + ((2 : k) - 1) • y - v := by module
    rw [← key', sub_self] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hvfix : v ∈ fixSub ρ B := by rw [hvy]; exact (fixSub ρ B).neg_mem hyY
  have hBle : B ≤ B' := fun c hc =>
    (hmem c hc).2 (by rw [hvfix c hc, sub_self]; exact zero_mem _)
  exact hB (le_bot_iff.1 (hbot ▸ hBle))

theorem orbitDifference_centralizer [Finite A] [Finite V] [Nontrivial A]
    (ρ : A →* (V ≃ₗ[k] V)) (hab : ∀ x y : A, x * y = y * x) (hp : IsPGroup p A)
    (hmax : ∀ D : Subgroup A, weight ρ D ≤ weight ρ ⊤) (v : V) :
    centSub ρ (orbitDiff ρ ⊤ v) ≠ ⊥ ∧
      weight ρ (centSub ρ (orbitDiff ρ ⊤ v)) = weight ρ ⊤ ∧
      (∀ a : A, ρ a v - v ∈ fixSub ρ (centSub ρ (orbitDiff ρ ⊤ v))) ∧
      (∀ a a' : A, ((ρ a' v - v) - (ρ a v - v) ∈ fixSub ρ ⊤ ↔
          a⁻¹ * a' ∈ centSub ρ (orbitDiff ρ ⊤ v))) ∧
      (∀ x ∈ fixSub ρ (centSub ρ (orbitDiff ρ ⊤ v)),
          ∃ a : A, x - (ρ a v - v) ∈ fixSub ρ ⊤) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := orbitDiff_centralizer ρ ⊤ top_ne_bot (fun x _ y _ => hab x y)
    (fun x _ => hp x) (fun D _ => hmax D) v
  simp only [top_inf_eq] at h1 h2 h3 h4 h5
  refine ⟨h1, h2, fun a => h3 a trivial, fun a a' => h4 a trivial a' trivial, fun x hx => ?_⟩
  obtain ⟨a, -, ha⟩ := h5 x hx
  exact ⟨a, ha⟩

theorem abelian_prime_offender_quadratic_replacement [Finite A] [Finite V] [Nontrivial A]
    (ρ : A →* (V ≃ₗ[k] V)) (hab : ∀ x y : A, x * y = y * x) (hp : IsPGroup p A)
    (h : Nat.card V ≤ weight ρ ⊤) :
    ∃ B : Subgroup A, B ≠ ⊥ ∧ weight ρ ⊤ ≤ weight ρ B ∧
      (∀ D, D ≤ B → weight ρ D ≤ weight ρ B) ∧
      (∀ D, ⊥ < D → D < B → weight ρ D < weight ρ B) ∧ QuadAct ρ B ∧
      (CFSG.IsElementaryAbelian p A → CFSG.IsElementaryAbelian p B) := by
  obtain ⟨B, hBbot, hw, hmax, hstrict, hel⟩ := exists_maxWeight_minimalSubgroup ρ h
  refine ⟨B, hBbot, hw, hmax, hstrict, ?_, hel p⟩
  intro b hb c hc v
  obtain ⟨hne, hweq, -, -, -⟩ := orbitDiff_centralizer ρ B hBbot (fun x _ y _ => hab x y)
    (fun x _ => hp x) hmax v
  have hBB' : B ⊓ centSub ρ (orbitDiff ρ B v) = B := by
    by_contra hne'
    have hlt : B ⊓ centSub ρ (orbitDiff ρ B v) < B := lt_of_le_of_ne inf_le_left hne'
    exact absurd (hstrict _ (bot_lt_iff_ne_bot.2 hne) hlt) (by rw [hweq]; exact lt_irrefl _)
  have hc' : c ∈ centSub ρ (orbitDiff ρ B v) := by
    have : c ∈ B ⊓ centSub ρ (orbitDiff ρ B v) := by rw [hBB']; exact hc
    exact this.2
  exact hc' _ (Submodule.subset_span ⟨b, hb, rfl⟩)

@[expose] def resHom (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) :
    A →* (W ≃ₗ[k] W) where
  toFun a := LinearEquiv.ofSubmodules (ρ a) W W (by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩; exact hW a w hw
    · intro w hw; exact ⟨ρ a⁻¹ w, hW a⁻¹ w hw, ρ_apply_inv ρ a w⟩)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem coe_resHom_apply (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W)
    (a : A) (w : W) : ((resHom ρ W hW a w : W) : V) = ρ a w := rfl

theorem ker_resHom (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) :
    (resHom ρ W hW).ker = centSub ρ W := by
  ext a
  rw [MonoidHom.mem_ker, mem_centSub]
  constructor
  · intro h u hu
    have h1 := congrArg (fun f : W ≃ₗ[k] W => ((f ⟨u, hu⟩ : W) : V)) h
    simpa [coe_resHom_apply] using h1
  · intro h
    ext w
    simp [coe_resHom_apply, h w w.2]

theorem card_range_resHom (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) :
    Nat.card (resHom ρ W hW).range = (centSub ρ W).index := by
  rw [← ker_resHom ρ W hW, Subgroup.index_ker]

theorem commSub_eq_bot_iff (ρ : A →* (V ≃ₗ[k] V)) (B : Subgroup A) (U : Submodule k V) :
    commSub ρ B U = ⊥ ↔ ∀ b ∈ B, ∀ u ∈ U, ρ b u = u := by
  unfold commSub
  rw [Submodule.span_eq_bot]
  constructor
  · intro h b hb u hu
    exact sub_eq_zero.1 (h _ ⟨b, hb, u, hu, rfl⟩)
  · rintro h w ⟨b, hb, u, hu, rfl⟩
    simp [h b hb u hu]

theorem card_fixSub_id_map [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (B : Subgroup A) :
    Nat.card ↥(fixSub (MonoidHom.id (W ≃ₗ[k] W)) (B.map (resHom ρ W hW))) =
      Nat.card ↥(W ⊓ fixSub ρ B) := by
  refine Nat.card_congr
    { toFun := fun w => ⟨(w.1 : V), w.1.2, fun b hb => by
        have := w.2 (resHom ρ W hW b) ⟨b, hb, rfl⟩
        simpa [coe_resHom_apply] using congrArg (fun x : W => (x : V)) this⟩
      invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun d hd => by
        obtain ⟨b, hb, rfl⟩ := hd
        ext
        simpa [coe_resHom_apply] using v.2.2 b hb⟩
      left_inv := fun w => rfl
      right_inv := fun v => rfl }

theorem weightId_map [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (B : Subgroup A) :
    weight (MonoidHom.id (W ≃ₗ[k] W)) (B.map (resHom ρ W hW)) =
      (centSub ρ W).relIndex B * Nat.card ↥(W ⊓ fixSub ρ B) := by
  unfold weight
  rw [card_fixSub_id_map, ← ker_resHom ρ W hW, Subgroup.relIndex_ker]

theorem weightId_range [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) :
    weight (MonoidHom.id (W ≃ₗ[k] W)) (resHom ρ W hW).range =
      (centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) := by
  have h1 := weightId_map ρ W hW ⊤
  rw [← MonoidHom.range_eq_map] at h1
  rw [h1, Subgroup.relIndex_top_right]

theorem restrict_ineq [Finite A] [Finite V]
    (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hmax : ∀ B : Subgroup A, weight ρ B ≤ weight ρ ⊤)
    {B : Subgroup A} (hCB : centSub ρ W ≤ B) :
    (centSub ρ W).relIndex B * Nat.card ↥(W ⊓ fixSub ρ B) *
        (Nat.card ↥(fixSub ρ B) / Nat.card ↥(fixSub ρ ⊤ ⊔ W ⊓ fixSub ρ B)) ≤
      (centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) ∧
    ((centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) =
        (centSub ρ W).relIndex B * Nat.card ↥(W ⊓ fixSub ρ B) →
      fixSub ρ B = fixSub ρ ⊤ ⊔ W ⊓ fixSub ρ B ∧ weight ρ ⊤ = weight ρ B) := by
  set C := centSub ρ W with hC
  set X := fixSub ρ ⊤ with hX
  set Y := W ⊓ fixSub ρ B with hY
  set Z := fixSub ρ B with hZ
  have hXZ : X ≤ Z := fixSub_anti ρ le_top
  have hYZ : Y ≤ Z := inf_le_right
  have hsZ : X ⊔ Y ≤ Z := sup_le hXZ hYZ
  have hXY : X ⊓ Y = W ⊓ X := by
    ext x
    simp only [Submodule.mem_inf, hY]
    constructor
    · rintro ⟨hx, hxW, _⟩; exact ⟨hxW, hx⟩
    · rintro ⟨hxW, hx⟩; exact ⟨hx, hxW, hXZ hx⟩
  have hprod := natCard_sup_mul_natCard_inf X Y
  rw [hXY] at hprod
  have hnA : Nat.card C * C.index = Nat.card ↥(⊤ : Subgroup A) := by
    rw [Subgroup.card_top]; exact Subgroup.card_mul_index C
  have hnB : Nat.card C * C.relIndex B = Nat.card B := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv] at h1
    rw [h1, Subgroup.relIndex, ← Subgroup.index_eq_card, mul_comm]
  obtain ⟨m, hm⟩ := natCard_dvd_of_le hsZ
  have hspos : 0 < Nat.card ↥(X ⊔ Y) := Nat.card_pos
  have hdiv : Nat.card Z / Nat.card ↥(X ⊔ Y) = m := by
    rw [hm]; exact Nat.mul_div_cancel_left _ hspos
  rw [hdiv]
  have hw := hmax B
  unfold weight at hw
  rw [← hnA, ← hnB, hm] at hw
  have hnCpos : 0 < Nat.card C := Nat.card_pos
  have hapos : 0 < Nat.card ↥X := Nat.card_pos
  have hcpos : 0 < Nat.card ↥(W ⊓ X) := Nat.card_pos
  have hypos : 0 < Nat.card ↥Y := Nat.card_pos
  have hw1 : C.relIndex B * m * Nat.card ↥(X ⊔ Y) ≤ C.index * Nat.card ↥X := by
    have : Nat.card C * (C.relIndex B * m * Nat.card ↥(X ⊔ Y)) ≤
        Nat.card C * (C.index * Nat.card ↥X) := by
      calc _ = Nat.card C * C.relIndex B * (Nat.card ↥(X ⊔ Y) * m) := by ring
        _ ≤ Nat.card C * C.index * Nat.card ↥X := hw
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hnCpos
  have hw2 : C.relIndex B * Nat.card ↥Y * m ≤ C.index * Nat.card ↥(W ⊓ X) := by
    have : Nat.card ↥X * (C.relIndex B * Nat.card ↥Y * m) ≤
        Nat.card ↥X * (C.index * Nat.card ↥(W ⊓ X)) := by
      calc _ = C.relIndex B * m * (Nat.card ↥X * Nat.card ↥Y) := by ring
        _ = C.relIndex B * m * (Nat.card ↥(X ⊔ Y) * Nat.card ↥(W ⊓ X)) := by rw [hprod]
        _ = (C.relIndex B * m * Nat.card ↥(X ⊔ Y)) * Nat.card ↥(W ⊓ X) := by ring
        _ ≤ (C.index * Nat.card ↥X) * Nat.card ↥(W ⊓ X) := Nat.mul_le_mul_right _ hw1
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hapos
  refine ⟨hw2, fun heq => ?_⟩
  have hiBpos : 0 < C.relIndex B := by
    rcases Nat.eq_zero_or_pos (C.relIndex B) with h0 | h0
    · rw [h0, mul_zero] at hnB; exact absurd hnB.symm (Nat.card_pos (α := B)).ne'
    · exact h0
  have hm1 : m = 1 := by
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm; exact absurd hm (Nat.card_pos (α := ↥Z)).ne'
      · exact h0
    have : C.relIndex B * Nat.card ↥Y * m ≤ C.relIndex B * Nat.card ↥Y * 1 := by
      rw [mul_one]; exact heq ▸ hw2
    have := Nat.le_of_mul_le_mul_left this (Nat.mul_pos hiBpos hypos)
    omega
  subst hm1
  refine ⟨?_, ?_⟩
  · exact (submodule_eq_of_le_of_card_ge hsZ (by rw [hm, mul_one])).symm
  · unfold weight
    rw [← hnA, ← hnB, hm, mul_one]
    have hcancel : C.index * Nat.card ↥X = C.relIndex B * Nat.card ↥(X ⊔ Y) := by
      have : Nat.card ↥(W ⊓ X) * (C.index * Nat.card ↥X) =
          Nat.card ↥(W ⊓ X) * (C.relIndex B * Nat.card ↥(X ⊔ Y)) := by
        calc _ = (C.index * Nat.card ↥(W ⊓ X)) * Nat.card ↥X := by ring
          _ = (C.relIndex B * Nat.card ↥Y) * Nat.card ↥X := by rw [heq]
          _ = C.relIndex B * (Nat.card ↥X * Nat.card ↥Y) := by ring
          _ = C.relIndex B * (Nat.card ↥(X ⊔ Y) * Nat.card ↥(W ⊓ X)) := by rw [hprod]
          _ = _ := by ring
      exact Nat.eq_of_mul_eq_mul_left hcpos this
    calc Nat.card C * C.index * Nat.card ↥X = Nat.card C * (C.index * Nat.card ↥X) := by ring
      _ = Nat.card C * (C.relIndex B * Nat.card ↥(X ⊔ Y)) := by rw [hcancel]
      _ = _ := by ring

theorem restrict_ineq_weak [Finite A] [Finite V]
    (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hmax : ∀ B : Subgroup A, weight ρ B ≤ weight ρ ⊤)
    {B : Subgroup A} (hCB : centSub ρ W ≤ B) :
    (centSub ρ W).relIndex B * Nat.card ↥(W ⊓ fixSub ρ B) ≤
      (centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) := by
  have h := (restrict_ineq ρ W hmax hCB).1
  have hsZ : fixSub ρ ⊤ ⊔ W ⊓ fixSub ρ B ≤ fixSub ρ B :=
    sup_le (fixSub_anti ρ le_top) inf_le_right
  have hm : 1 ≤ Nat.card ↥(fixSub ρ B) / Nat.card ↥(fixSub ρ ⊤ ⊔ W ⊓ fixSub ρ B) :=
    Nat.div_pos (Nat.le_of_dvd Nat.card_pos (natCard_dvd_of_le hsZ)) Nat.card_pos
  exact le_trans (Nat.le_mul_of_pos_right _ hm) h

theorem fixedWeight_restrict [Finite A] [Finite V] (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V)
    (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W) (hmax : ∀ B : Subgroup A, weight ρ B ≤ weight ρ ⊤) :
    (∀ D : Subgroup (W ≃ₗ[k] W), D ≤ (resHom ρ W hW).range →
      weight (MonoidHom.id (W ≃ₗ[k] W)) D ≤
        weight (MonoidHom.id (W ≃ₗ[k] W)) (resHom ρ W hW).range) ∧
    (∀ B : Subgroup A, centSub ρ W ≤ B →
      (centSub ρ W).relIndex B * Nat.card ↥(W ⊓ fixSub ρ B) *
        (Nat.card ↥(fixSub ρ B) / Nat.card ↥(fixSub ρ ⊤ ⊔ W ⊓ fixSub ρ B)) ≤
      (centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) ∧
      ((centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) =
        (centSub ρ W).relIndex B * Nat.card ↥(W ⊓ fixSub ρ B) →
        fixSub ρ B = fixSub ρ ⊤ ⊔ W ⊓ fixSub ρ B ∧ weight ρ ⊤ = weight ρ B)) := by
  refine ⟨fun D hD => ?_, fun B hCB => restrict_ineq ρ W hmax hCB⟩
  set r := resHom ρ W hW
  have hDB : (D.comap r).map r = D := Subgroup.map_comap_eq_self hD
  have hCB : centSub ρ W ≤ D.comap r := by
    rw [← ker_resHom ρ W hW]; exact MonoidHom.ker_le_comap r D
  rw [weightId_range, ← hDB, weightId_map]
  exact restrict_ineq_weak ρ W hmax hCB

theorem minimal_fixedWeight_restriction_faithful_splitting [Finite A] [Finite V]
    (ρ : A →* (V ≃ₗ[k] V)) (W : Submodule k V) (hW : ∀ a, ∀ w ∈ W, ρ a w ∈ W)
    (hmax : ∀ B : Subgroup A, weight ρ B ≤ weight ρ ⊤)
    (hstrict : ∀ B : Subgroup A, ⊥ < B → B < ⊤ → weight ρ B < weight ρ ⊤)
    (hWA : commSub ρ ⊤ W ≠ ⊥) :
    (∀ D : Subgroup (W ≃ₗ[k] W), D ≤ (resHom ρ W hW).range →
      weight (MonoidHom.id (W ≃ₗ[k] W)) D ≤
        weight (MonoidHom.id (W ≃ₗ[k] W)) (resHom ρ W hW).range) ∧
    (∀ D : Subgroup (W ≃ₗ[k] W), D ≤ (resHom ρ W hW).range → ⊥ < D → D < (resHom ρ W hW).range →
      weight (MonoidHom.id (W ≃ₗ[k] W)) D <
        weight (MonoidHom.id (W ≃ₗ[k] W)) (resHom ρ W hW).range) ∧
    ((centSub ρ W).index * Nat.card ↥(W ⊓ fixSub ρ ⊤) = Nat.card ↥W →
      centSub ρ W = ⊥ ∧ W ⊔ fixSub ρ ⊤ = ⊤) := by
  obtain ⟨h1, h2⟩ := fixedWeight_restrict ρ W hW hmax
  refine ⟨h1, fun D hD hbot hlt => ?_, fun heq => ?_⟩
  · refine lt_of_le_of_ne (h1 D hD) fun hweq => ?_
    set r := resHom ρ W hW
    have hDB : (D.comap r).map r = D := Subgroup.map_comap_eq_self hD
    have hCB : centSub ρ W ≤ D.comap r := by
      rw [← ker_resHom ρ W hW]; exact MonoidHom.ker_le_comap r D
    rw [weightId_range, ← hDB, weightId_map] at hweq
    have hB := ((h2 _ hCB).2 hweq.symm).2
    have hBbot : ⊥ < D.comap r := by
      refine bot_lt_iff_ne_bot.2 fun h => ?_
      rw [h, Subgroup.map_bot] at hDB
      exact (bot_lt_iff_ne_bot.1 hbot) hDB.symm
    have hBtop : D.comap r < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => ?_
      rw [h, ← MonoidHom.range_eq_map] at hDB
      exact hlt.ne hDB.symm
    exact absurd (hstrict _ hBbot hBtop) (by rw [hB]; exact lt_irrefl _)
  · have hCtop : centSub ρ W ≠ ⊤ := fun h => hWA
      ((commSub_eq_bot_iff ρ ⊤ W).2 fun b _ u hu => by
        have : b ∈ centSub ρ W := h ▸ Subgroup.mem_top b
        exact this u hu)
    have hWC : W ⊓ fixSub ρ (centSub ρ W) = W :=
      inf_eq_left.2 fun w hw b hb => hb w hw
    have hrel : (centSub ρ W).relIndex (centSub ρ W) = 1 := Subgroup.relIndex_self _
    have hC : centSub ρ W = ⊥ := by
      by_contra hne
      have hlt : centSub ρ W < ⊤ := lt_top_iff_ne_top.2 hCtop
      have := ((h2 _ le_rfl).2 (by rw [hrel, hWC, one_mul]; exact heq)).2
      exact absurd (hstrict _ (bot_lt_iff_ne_bot.2 hne) hlt) (by rw [this]; exact lt_irrefl _)
    refine ⟨hC, ?_⟩
    have := ((h2 _ le_rfl).2 (by rw [hrel, hWC, one_mul]; exact heq)).1
    rw [hC, fixSub_bot, inf_top_eq] at this
    rw [sup_comm]
    exact this.symm

end CFSG.QuasithinUnique.Setup.Offender
