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

namespace CFSG.Wreathed

variable {α β γ : Type*}

theorem map_val_eq_replicate (X : Finset α) (f : α → γ) (c : γ) (h : ∀ x ∈ X, f x = c) :
    X.val.map f = Multiset.replicate X.card c := by
  rw [Multiset.eq_replicate]
  refine ⟨by rw [Multiset.card_map]; rfl, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  exact h x hx

theorem map_val_eq_replicate_four [DecidableEq α] (B X₁ X₂ X₃ X₄ : Finset α) (f : α → γ)
    (c₁ c₂ c₃ c₄ : γ) (hB : B = X₁ ∪ X₂ ∪ X₃ ∪ X₄) (h₁ : ∀ x ∈ X₁, f x = c₁)
    (h₂ : ∀ x ∈ X₂, f x = c₂) (h₃ : ∀ x ∈ X₃, f x = c₃) (h₄ : ∀ x ∈ X₄, f x = c₄)
    (h12 : c₁ ≠ c₂) (h13 : c₁ ≠ c₃) (h14 : c₁ ≠ c₄) (h23 : c₂ ≠ c₃) (h24 : c₂ ≠ c₄)
    (h34 : c₃ ≠ c₄) :
    B.val.map f = Multiset.replicate X₁.card c₁ + Multiset.replicate X₂.card c₂ +
      Multiset.replicate X₃.card c₃ + Multiset.replicate X₄.card c₄ := by
  have hd : ∀ {X Y : Finset α} {c d : γ}, (∀ x ∈ X, f x = c) → (∀ x ∈ Y, f x = d) → c ≠ d →
      Disjoint X Y := by
    intro X Y c d hX hY hcd
    rw [Finset.disjoint_left]
    intro x hxX hxY
    exact hcd ((hX x hxX).symm.trans (hY x hxY))
  have d12 := hd h₁ h₂ h12
  have d123 : Disjoint (X₁ ∪ X₂) X₃ :=
    Finset.disjoint_union_left.mpr ⟨hd h₁ h₃ h13, hd h₂ h₃ h23⟩
  have d1234 : Disjoint (X₁ ∪ X₂ ∪ X₃) X₄ :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hd h₁ h₄ h14,
      hd h₂ h₄ h24⟩, hd h₃ h₄ h34⟩
  have hval : B.val = X₁.val + X₂.val + X₃.val + X₄.val := by
    rw [hB, ← Finset.disjUnion_eq_union _ _ d1234, Finset.disjUnion_val,
      ← Finset.disjUnion_eq_union _ _ d123, Finset.disjUnion_val,
      ← Finset.disjUnion_eq_union _ _ d12, Finset.disjUnion_val]
  rw [hval, Multiset.map_add, Multiset.map_add, Multiset.map_add, map_val_eq_replicate X₁ f c₁ h₁,
    map_val_eq_replicate X₂ f c₂ h₂, map_val_eq_replicate X₃ f c₃ h₃,
    map_val_eq_replicate X₄ f c₄ h₄]

theorem map_val_eq_of_equiv {s : Finset α} {t : Finset β} (τ : s ≃ t) (f : α → γ) (g : β → γ)
    (h : ∀ x : s, g (τ x) = f x) : t.val.map g = s.val.map f := by
  have ht : t.val.map g = (Finset.univ : Finset t).val.map (g ∘ Subtype.val) := by
    rw [← Multiset.map_map, ← Finset.attach_eq_univ, Finset.attach_val, Multiset.attach_map_val]
  have hs : s.val.map f = (Finset.univ : Finset s).val.map (f ∘ Subtype.val) := by
    rw [← Multiset.map_map, ← Finset.attach_eq_univ, Finset.attach_val, Multiset.attach_map_val]
  rw [ht, hs, ← Finset.univ_map_equiv_to_embedding τ, Finset.map_val, Multiset.map_map]
  congr 1
  funext x
  exact h x

theorem card_eq_of_equiv_mem {s : Finset α} {t : Finset β} (τ : s ≃ t) {s' : Finset α}
    {t' : Finset β} (hs : s' ⊆ s) (ht : t' ⊆ t) (h : ∀ x : s, x.1 ∈ s' ↔ (τ x).1 ∈ t') :
    s'.card = t'.card := by
  refine Finset.card_bij (fun a ha => (τ ⟨a, hs ha⟩).1) (fun a ha => (h ⟨a, hs ha⟩).mp ha)
    (fun a₁ ha₁ a₂ ha₂ he => ?_) (fun b hb => ?_)
  · have := τ.injective (Subtype.ext he)
    exact congrArg Subtype.val this
  · refine ⟨(τ.symm ⟨b, ht hb⟩).1, (h _).mpr (by rw [Equiv.apply_symm_apply]; exact hb), ?_⟩
    simp

end CFSG.Wreathed
