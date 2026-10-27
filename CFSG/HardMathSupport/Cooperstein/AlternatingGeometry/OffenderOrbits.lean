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

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv Equiv.Perm MulAction

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def IsExp2 (E : Subgroup (Perm Ω)) : Prop := ∀ g ∈ E, g * g = 1

variable {E : Subgroup (Perm Ω)}

theorem IsExp2.comm (hE : IsExp2 E) {g h : Perm Ω} (hg : g ∈ E) (hh : h ∈ E) :
    g * h = h * g := by
  have h1 : (g * h) * (g * h) = 1 := hE _ (E.mul_mem hg hh)
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hE g hg)
  have hh' : h⁻¹ = h := inv_eq_of_mul_eq_one_right (hE h hh)
  have h2 : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, hg', hh'] at h2
  exact h2.symm

theorem IsExp2.isPGroup (hE : IsExp2 E) : IsPGroup 2 E := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_two] using hE g g.2

theorem IsExp2.card_orbit (hE : IsExp2 E) (p : Ω) : ∃ m : ℕ, Nat.card (orbit E p) = 2 ^ m :=
  hE.isPGroup.card_orbit p

theorem IsExp2.smul_eq_of_mem_stabilizer (hE : IsExp2 E) {p q : Ω} (hq : q ∈ orbit E p)
    {g : E} (hg : g ∈ stabilizer E p) : g • q = q := by
  obtain ⟨h, rfl⟩ := hq
  have hc : (g : Perm Ω) * h = (h : Perm Ω) * g := hE.comm g.2 h.2
  have : (g * h) • p = (h * g) • p := by
    show ((g : Perm Ω) * h) p = ((h : Perm Ω) * g) p
    rw [hc]
  rw [mul_smul, mul_smul, hg] at this
  exact this

abbrev Orb (E : Subgroup (Perm Ω)) : Type _ := orbitRel.Quotient E Ω

noncomputable instance (E : Subgroup (Perm Ω)) : Fintype (Orb E) := Fintype.ofFinite _

theorem card_orbit_eq_index {G α : Type*} [Group G] [MulAction G α] (p : α) :
    Nat.card (orbit G p) = (stabilizer G p).index := by
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]

theorem card_mul_index_pow_le (hE : IsExp2 E) (Y : Subgroup E)
    (hY : ∀ p : Ω, stabilizer E p ≤ Y) :
    Nat.card Y * Y.index ^ Nat.card (Orb E) ≤ ∏ ω : Orb E, Nat.card (orbit E ω.out) := by
  classical
  let b : Orb E → Ω := fun ω => ω.out
  let ι : Y → ∀ ω : Orb E, orbit Y (b ω) := fun y ω => ⟨y • b ω, mem_orbit _ _⟩
  have hinj : Function.Injective ι := by
    intro y1 y2 h
    have hpt : ∀ ω, (y1 : E) • b ω = (y2 : E) • b ω := fun ω => congrArg Subtype.val (congrFun h ω)
    apply Subtype.ext
    apply Subtype.ext
    ext q
    have hq : ∃ h0 : E, h0 • b (Quotient.mk'' q) = q := by
      have h' : (orbitRel E Ω) q (b (Quotient.mk'' q)) :=
        Quotient.exact' (Quotient.out_eq' (Quotient.mk'' q)).symm
      exact orbitRel_apply.1 h'
    obtain ⟨h0, hh0⟩ := hq
    have hp := hpt (Quotient.mk'' q)
    generalize b (Quotient.mk'' q) = x at hh0 hp
    have key : ∀ y : E, y • q = h0 • (y • x) := by
      intro y
      rw [← hh0, ← mul_smul, ← mul_smul]
      congr 1
      exact Subtype.ext (hE.comm y.2 h0.2)
    exact (key (y1 : E)).trans ((congrArg (h0 • ·) hp).trans (key (y2 : E)).symm)
  have h1 : Nat.card Y ≤ ∏ ω : Orb E, Nat.card (orbit Y (b ω)) := by
    have := Nat.card_le_card_of_injective ι hinj
    rwa [Nat.card_pi] at this
  have h2 : ∀ ω : Orb E, Nat.card (orbit Y (b ω)) * Y.index = Nat.card (orbit E (b ω)) := by
    intro ω
    have hs : stabilizer Y (b ω) = (stabilizer E (b ω)).subgroupOf Y := by
      ext y
      simp [mem_stabilizer_iff]
    rw [card_orbit_eq_index (G := E) (b ω), card_orbit_eq_index (G := Y) (b ω), hs]
    exact Subgroup.relIndex_mul_index (hY (b ω))
  have h3 : (∏ ω : Orb E, Nat.card (orbit Y (b ω))) * Y.index ^ Nat.card (Orb E) =
      ∏ ω : Orb E, Nat.card (orbit E (b ω)) := by
    have hc : Y.index ^ Nat.card (Orb E) = ∏ _ω : Orb E, Y.index := by
      rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
    rw [hc, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun ω _ => h2 ω
  calc Nat.card Y * Y.index ^ Nat.card (Orb E)
      ≤ (∏ ω : Orb E, Nat.card (orbit Y (b ω))) * Y.index ^ Nat.card (Orb E) :=
        Nat.mul_le_mul_right _ h1
    _ = ∏ ω : Orb E, Nat.card (orbit E (b ω)) := h3

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
