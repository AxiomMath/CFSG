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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Holt

open MulAction

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

variable (Ω) in
@[expose] def fixSet (Y : Subgroup X) : Set Ω := {ω | ∀ y ∈ Y, y • ω = ω}

theorem mem_fixSet {Y : Subgroup X} {ω : Ω} : ω ∈ fixSet Ω Y ↔ ∀ y ∈ Y, y • ω = ω := Iff.rfl

theorem mem_fixSet_iff_le_stabilizer {Y : Subgroup X} {ω : Ω} :
    ω ∈ fixSet Ω Y ↔ Y ≤ stabilizer X ω := Iff.rfl

theorem fixSet_eq_fixedPoints (Y : Subgroup X) : fixSet Ω Y = fixedPoints Y Ω := by
  ext ω
  simp only [mem_fixSet, mem_fixedPoints, Subtype.forall, Subgroup.mk_smul]

theorem fixSet_anti {Y Y' : Subgroup X} (h : Y ≤ Y') : fixSet Ω Y' ⊆ fixSet Ω Y :=
  fun _ hω y hy => hω y (h hy)

theorem fixSet_zpowers (x : X) : fixSet Ω (Subgroup.zpowers x) = fixedBy Ω x := by
  ext ω
  rw [mem_fixSet_iff_le_stabilizer, Subgroup.zpowers_le, mem_stabilizer_iff, mem_fixedBy]

theorem fixSet_sup (Y Y' : Subgroup X) : fixSet Ω (Y ⊔ Y') = fixSet Ω Y ∩ fixSet Ω Y' := by
  ext ω
  simp only [Set.mem_inter_iff, mem_fixSet_iff_le_stabilizer, sup_le_iff]

@[simp] theorem fixSet_bot : fixSet Ω (⊥ : Subgroup X) = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true, mem_fixSet, Subgroup.mem_bot]
  rintro y rfl
  exact one_smul X ω

theorem fixSet_subset_singleton_of_mem {Y : Subgroup X} {d : X} (hdY : d ∈ Y) {α : Ω}
    (hd : ∀ ω, d • ω = ω ↔ ω = α) : fixSet Ω Y ⊆ {α} :=
  fun ω hω => (hd ω).mp (hω d hdY)

theorem smul_mem_fixSet_of_mem_normalizer {Y : Subgroup X} {n : X}
    (hn : n ∈ Subgroup.normalizer (Y : Set X)) {ω : Ω} (hω : ω ∈ fixSet Ω Y) :
    n • ω ∈ fixSet Ω Y := by
  intro y hy
  have h := congrArg (n • ·) (hω _ ((Subgroup.mem_normalizer_iff''.mp hn y).mp hy))
  simpa only [mul_smul, smul_inv_smul] using h

instance instMulActionNormalizerFixSet (Y : Subgroup X) :
    MulAction (Subgroup.normalizer (Y : Set X)) (fixSet Ω Y) where
  smul n ω := ⟨(n : X) • (ω : Ω), smul_mem_fixSet_of_mem_normalizer n.2 ω.2⟩
  one_smul ω := Subtype.ext (one_smul X (ω : Ω))
  mul_smul m n ω := Subtype.ext (mul_smul (m : X) (n : X) (ω : Ω))

@[simp] theorem coe_normalizer_smul {Y : Subgroup X} (n : Subgroup.normalizer (Y : Set X))
    (ω : fixSet Ω Y) : ((n • ω : fixSet Ω Y) : Ω) = (n : X) • (ω : Ω) := rfl

instance instMulActionCentralizerFixSet (Y : Subgroup X) :
    MulAction (Subgroup.centralizer (Y : Set X)) (fixSet Ω Y) where
  smul c ω := ⟨(c : X) • (ω : Ω),
    smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ c.2) ω.2⟩
  one_smul ω := Subtype.ext (one_smul X (ω : Ω))
  mul_smul m n ω := Subtype.ext (mul_smul (m : X) (n : X) (ω : Ω))

@[simp] theorem coe_centralizer_smul {Y : Subgroup X} (c : Subgroup.centralizer (Y : Set X))
    (ω : fixSet Ω Y) : ((c • ω : fixSet Ω Y) : Ω) = (c : X) • (ω : Ω) := rfl

theorem card_modEq_card_fixSet [Finite Ω] {p : ℕ} [Fact p.Prime] {P : Subgroup X}
    (hP : IsPGroup p P) : Nat.card Ω ≡ Nat.card (fixSet Ω P) [MOD p] := by
  rw [fixSet_eq_fixedPoints]
  exact hP.card_modEq_card_fixedPoints Ω

theorem odd_card_fixSet_of_odd [Finite Ω] (hΩ : Odd (Nat.card Ω)) {P : Subgroup X}
    (hP : IsPGroup 2 P) : Odd (Nat.card (fixSet Ω P)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff] at hΩ ⊢
  rw [← (card_modEq_card_fixSet hP), hΩ]

theorem fixSet_nonempty_of_odd [Finite Ω] (hΩ : Odd (Nat.card Ω)) {P : Subgroup X}
    (hP : IsPGroup 2 P) : (fixSet Ω P).Nonempty := by
  have h := (odd_card_fixSet_of_odd hΩ hP).pos
  rw [Nat.card_pos_iff] at h
  exact Set.nonempty_coe_sort.mp h.1

theorem card_orbit_modEq_card_fixSet_inter [Finite Ω] {p : ℕ} [Fact p.Prime] {P : Subgroup X}
    (hP : IsPGroup p P) (α : Ω) :
    Nat.card (orbit X α) ≡ Nat.card ↥(fixSet Ω P ∩ orbit X α) [MOD p] := by
  have e : Nat.card (fixedPoints P (orbit X α)) = Nat.card ↥(fixSet Ω P ∩ orbit X α) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, fun y hy => congrArg Subtype.val (x.2 ⟨y, hy⟩), x.1.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.2⟩, fun m => Subtype.ext (x.2.1 m m.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← e]
  exact hP.card_modEq_card_fixedPoints (orbit X α)

theorem isPretransitive_of_forall_exists_fixSet_eq_singleton {G : Type*} [Group G] {Δ : Type*}
    [MulAction G Δ] [Finite Δ] (p : ℕ) [Fact p.Prime]
    (h : ∀ δ : Δ, ∃ P : Subgroup G, IsPGroup p P ∧ fixSet Δ P = {δ}) :
    IsPretransitive G Δ := by
  refine ⟨fun δ₁ δ₂ => ?_⟩
  by_contra hne
  have hδ₂ : δ₂ ∉ orbit G δ₁ := fun ⟨g, hg⟩ => hne ⟨g, hg⟩
  obtain ⟨P₁, hP₁, hF₁⟩ := h δ₁
  obtain ⟨P₂, hP₂, hF₂⟩ := h δ₂
  have h1 : Nat.card ↥(fixSet Δ P₁ ∩ orbit G δ₁) = 1 := by
    rw [hF₁, Set.singleton_inter_of_mem (mem_orbit_self δ₁)]
    exact Nat.card_unique
  have h0 : Nat.card ↥(fixSet Δ P₂ ∩ orbit G δ₁) = 0 := by
    rw [hF₂, Set.singleton_inter_eq_empty.mpr hδ₂]
    exact Nat.card_of_isEmpty
  have hmod := (card_orbit_modEq_card_fixSet_inter hP₁ δ₁).symm.trans
    (card_orbit_modEq_card_fixSet_inter hP₂ δ₁)
  rw [h1, h0] at hmod
  exact (Fact.out : p.Prime).not_dvd_one (Nat.modEq_zero_iff_dvd.mp hmod)

end CFSG.Holt
