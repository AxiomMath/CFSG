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

namespace CFSG.ClassicalInvolution.Asc77.T7K

variable {G : Type} [Group G] [Finite G]

theorem card_involutions_le_eight {W : Subgroup G} (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {a b c : G} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W)
    (hgen : W ≤ Subgroup.closure ({a, b, c} : Set G)) :
    Nat.card {w : G // w ∈ W ∧ w * w = 1} ≤ 8 := by
  classical
  let _ : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with mul_comm := fun x y => Subtype.ext (hcomm _ x.2 _ y.2) }
  let sq : ↥W →* ↥W := powMonoidHom 2
  have hker : Nat.card {w : G // w ∈ W ∧ w * w = 1} = Nat.card sq.ker := by
    refine Nat.card_congr
      { toFun := fun w => ⟨⟨w.1, w.2.1⟩, by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (by simpa [sq, pow_two] using w.2.2)⟩
        invFun := fun w => ⟨(w.1 : G), w.1.2, by
          have := (MonoidHom.mem_ker.mp w.2)
          simpa [sq, pow_two] using congrArg Subtype.val this⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  rw [hker, ← Subgroup.index_range (f := sq)]
  let Q := ↥W ⧸ sq.range
  have hQ2 : ∀ q : Q, q * q = 1 := by
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ⟨w, by simp [sq, pow_two]⟩
  let _ : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (fun x => by
    have := hQ2 (Additive.toMul x)
    apply Additive.toMul.injective
    simpa [two_nsmul, pow_two] using this)
  let ha' : Additive Q := Additive.ofMul (QuotientGroup.mk ⟨a, ha⟩)
  let hb' : Additive Q := Additive.ofMul (QuotientGroup.mk ⟨b, hb⟩)
  let hc' : Additive Q := Additive.ofMul (QuotientGroup.mk ⟨c, hc⟩)
  have hcl : Subgroup.closure ({a, b, c} : Set G) ≤ W := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have key : ∀ x (hx : x ∈ Subgroup.closure ({a, b, c} : Set G)),
      Additive.ofMul (QuotientGroup.mk (⟨x, hcl hx⟩ : ↥W) : Q) ∈
        Submodule.span (ZMod 2) {ha', hb', hc'} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact Submodule.subset_span (by simp [ha'])
      · exact Submodule.subset_span (by simp [hb'])
      · exact Submodule.subset_span (by simp [hc'])
    | one =>
      have : (⟨1, hcl (Subgroup.one_mem _)⟩ : ↥W) = 1 := rfl
      rw [this, QuotientGroup.mk_one]
      exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, hcl (Subgroup.mul_mem _ hx hy)⟩ : ↥W) = ⟨x, hcl hx⟩ * ⟨y, hcl hy⟩ := rfl
      rw [this, QuotientGroup.mk_mul, ofMul_mul]
      exact Submodule.add_mem _ ihx ihy
    | inv x hx ihx =>
      have : (⟨x⁻¹, hcl (Subgroup.inv_mem _ hx)⟩ : ↥W) = (⟨x, hcl hx⟩)⁻¹ := rfl
      rw [this, QuotientGroup.mk_inv, ofMul_inv]
      exact Submodule.neg_mem _ ihx
  have hspan : Submodule.span (ZMod 2) {ha', hb', hc'} = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    have := key w.1 (hgen w.2)
    have e : q = Additive.ofMul (QuotientGroup.mk (⟨w.1, hcl (hgen w.2)⟩ : ↥W) : Q) :=
      Additive.toMul.injective hw.symm
    rw [e]
    exact this
  have hfin : Module.finrank (ZMod 2) (Additive Q) ≤ 3 := by
    have h1 := finrank_span_finset_le_card (R := ZMod 2) ({ha', hb', hc'} : Finset (Additive Q))
    have h2 : ((({ha', hb', hc'} : Finset (Additive Q)) : Set (Additive Q))) =
        {ha', hb', hc'} := by
      ext x
      simp
    simp only [Set.finrank] at h1
    rw [h2, hspan, finrank_top] at h1
    exact h1.trans Finset.card_le_three
  have hcard : Nat.card (Additive Q) = 2 ^ Module.finrank (ZMod 2) (Additive Q) := by
    exact (FiniteField.pow_finrank_eq_natCard 2 (Additive Q)).symm
  rw [Subgroup.index_eq_card]
  have h3 : Nat.card Q = Nat.card (Additive Q) := Nat.card_congr Additive.ofMul
  rw [h3, hcard]
  calc 2 ^ Module.finrank (ZMod 2) (Additive Q) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hfin
    _ = 8 := by norm_num

theorem mem_of_involution_of_card_eq_eight {W S : Subgroup G}
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {a b c : G} (ha : a ∈ W) (hb : b ∈ W)
    (hc : c ∈ W) (hgen : W ≤ Subgroup.closure ({a, b, c} : Set G)) (hSW : S ≤ W)
    (hS : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8) {w : G} (hw : w ∈ W) (hw2 : w * w = 1) :
    w ∈ S := by
  classical
  have hle := card_involutions_le_eight hcomm ha hb hc hgen
  let X : Set G := {w | w ∈ W ∧ w * w = 1}
  have hSX : (S : Set G) ⊆ X := fun s hs => ⟨hSW hs, hS s hs⟩
  have hXfin : X.Finite := Set.toFinite X
  have hX8 : X.ncard ≤ 8 := by
    have : Nat.card ↥X ≤ 8 := hle
    simpa [Nat.card_coe_set_eq] using this
  have hS8' : (S : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hS8
  have := Set.eq_of_subset_of_ncard_le hSX (by omega) hXfin
  have hwX : w ∈ X := ⟨hw, hw2⟩
  rw [← this] at hwX
  exact hwX

end CFSG.ClassicalInvolution.Asc77.T7K
