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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace CFSG.LocalAnalysis.RankThreeUC

theorem card_ringEquiv_lt (F : Type) [Field F] [Finite F] : Nat.card (F ≃+* F) < Nat.card F := by
  haveI : Finite Fˣ := Finite.of_injective (Units.val : Fˣ → F) Units.val_injective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  let κ : (F ≃+* F) → {x : F // x ≠ 0} := fun θ =>
    ⟨θ (g : F), fun h => g.ne_zero (θ.injective (h.trans (map_zero θ).symm))⟩
  have hκ : Function.Injective κ := by
    intro θ θ' h
    have h' : θ (g : F) = θ' (g : F) := congrArg Subtype.val h
    apply RingEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 x hx))
      have hxk : x = ((g ^ k : Fˣ) : F) := by rw [hk, Units.val_mk0]
      rw [hxk, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, h']
  calc Nat.card (F ≃+* F) ≤ Nat.card {x : F // x ≠ 0} := Nat.card_le_card_of_injective κ hκ
    _ < Nat.card F := Finite.card_subtype_lt (p := fun x : F => x ≠ 0) (x := 0) (by simp)

theorem exists_ne_zero_fixed {H : Type} [Group H] [Finite H] (hH : IsPGroup 2 H)
    {W : Type} [Zero W] [Finite W] (hW : Even (Nat.card W)) (ρ : H →* Equiv.Perm W)
    (h0 : ∀ h : H, ρ h 0 = 0) : ∃ x : W, x ≠ 0 ∧ ∀ h : H, ρ h x = x := by
  letI : MulAction H W := MulAction.compHom W ρ
  have hsmul : ∀ (h : H) (x : W), h • x = ρ h x := fun _ _ => rfl
  have hmod : Nat.card W ≡ Nat.card (MulAction.fixedPoints H W) [MOD 2] :=
    hH.card_modEq_card_fixedPoints W
  have hev : Nat.card (MulAction.fixedPoints H W) % 2 = 0 := by
    have h1 : Nat.card W % 2 = 0 := Nat.even_iff.mp hW
    have h2 : Nat.card W % 2 = Nat.card (MulAction.fixedPoints H W) % 2 := hmod
    omega
  have hzfix : (0 : W) ∈ MulAction.fixedPoints H W := by
    rw [MulAction.mem_fixedPoints]
    intro h
    rw [hsmul]
    exact h0 h
  have hpos : 0 < Nat.card (MulAction.fixedPoints H W) :=
    Finite.card_pos_iff.2 ⟨⟨0, hzfix⟩⟩
  have hgt : 1 < Nat.card (MulAction.fixedPoints H W) := by omega
  rw [Finite.one_lt_card_iff_nontrivial] at hgt
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(MulAction.fixedPoints H W)
  by_cases ha0 : (a : W) = 0
  · have hb0 : (b : W) ≠ 0 := fun hb => hab (Subtype.ext (ha0.trans hb.symm))
    exact ⟨(b : W), hb0, fun h => by rw [← hsmul]; exact MulAction.mem_fixedPoints.mp b.2 h⟩
  · exact ⟨(a : W), ha0, fun h => by rw [← hsmul]; exact MulAction.mem_fixedPoints.mp a.2 h⟩

end CFSG.LocalAnalysis.RankThreeUC
