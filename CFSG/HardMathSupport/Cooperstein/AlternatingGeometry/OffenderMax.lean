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

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type*} [Group G]

@[expose] def IsElemAb2 (B : Subgroup G) : Prop := ∀ a ∈ B, a * a = 1 ∧ ∀ b ∈ B, a * b = b * a

theorem card_mul_le_card_inf_mul_card_sup [Finite G] (X V : Subgroup G) :
    Nat.card X * Nat.card V ≤ Nat.card ↥(X ⊓ V) * Nat.card ↥(X ⊔ V) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let f : X × V → G := fun p => (p.1 : G) * (p.2 : G)
  have himg : ∀ p, f p ∈ (X ⊔ V : Subgroup G) := fun p =>
    (X ⊔ V).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
  have hcard1 : Nat.card (X × V) = Nat.card X * Nat.card V := Nat.card_prod _ _
  have hfib : ∀ a ∈ (Finset.univ : Finset (X × V)).image f,
      ((Finset.univ : Finset (X × V)).filter (fun p => f p = a)).card ≤ Nat.card ↥(X ⊓ V) := by
    intro a ha
    obtain ⟨p0, -, rfl⟩ := Finset.mem_image.1 ha
    let g : {p : X × V // f p = f p0} → ↥(X ⊓ V) := fun p =>
      ⟨(p0.1 : G)⁻¹ * (p.1.1 : G), X.mul_mem (X.inv_mem p0.1.2) p.1.1.2, by
        have h := p.2
        simp only [f] at h
        have h' : (p.1.1 : G) = (p0.1 : G) * (p0.2 : G) * (p.1.2 : G)⁻¹ := by
          rw [← h]; group
        have : (p0.1 : G)⁻¹ * (p.1.1 : G) = (p0.2 : G) * (p.1.2 : G)⁻¹ := by
          rw [h']; group
        rw [this]
        exact V.mul_mem p0.2.2 (V.inv_mem p.1.2.2)⟩
    have hg : Function.Injective g := by
      intro p q hpq
      have h1 : (p.1.1 : G) = (q.1.1 : G) := by
        have h0 := congrArg Subtype.val hpq
        have h0' : (p0.1 : G)⁻¹ * (p.1.1 : G) = (p0.1 : G)⁻¹ * (q.1.1 : G) := h0
        exact mul_left_cancel h0'

      have h2 : (p.1.2 : G) = (q.1.2 : G) := by
        have hp := p.2; have hq := q.2
        simp only [f] at hp hq
        rw [h1] at hp
        exact mul_left_cancel (hp.trans hq.symm)
      apply Subtype.ext
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    have := Nat.card_le_card_of_injective g hg
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    simpa [Finset.filter_congr_decidable] using this
  have hle : (Finset.univ : Finset (X × V)).card ≤
      Nat.card ↥(X ⊓ V) * ((Finset.univ : Finset (X × V)).image f).card :=
    Finset.card_le_mul_card_image _ _ hfib
  have himg_le : ((Finset.univ : Finset (X × V)).image f).card ≤ Nat.card ↥(X ⊔ V) := by
    have hsub : (Finset.univ : Finset (X × V)).image f ⊆ ((X ⊔ V : Subgroup G) : Set G).toFinset := by
      intro a ha
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ha
      simpa using himg p
    have h1 := Finset.card_le_card hsub
    have h2 : Nat.card ↥(X ⊔ V) = ((X ⊔ V : Subgroup G) : Set G).toFinset.card :=
      Nat.card_eq_card_toFinset ((X ⊔ V : Subgroup G) : Set G)
    rw [h2]
    exact h1
  calc Nat.card X * Nat.card V = Nat.card (X × V) := hcard1.symm
    _ = (Finset.univ : Finset (X × V)).card := by rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ ≤ Nat.card ↥(X ⊓ V) * ((Finset.univ : Finset (X × V)).image f).card := hle
    _ ≤ Nat.card ↥(X ⊓ V) * Nat.card ↥(X ⊔ V) := Nat.mul_le_mul_left _ himg_le

theorem IsElemAb2.mono {B B' : Subgroup G} (h : IsElemAb2 B) (hle : B' ≤ B) : IsElemAb2 B' :=
  fun a ha => ⟨(h a (hle ha)).1, fun b hb => (h a (hle ha)).2 b (hle hb)⟩

theorem isElemAb2_sup {X V : Subgroup G} (hX : IsElemAb2 X) (hV : IsElemAb2 V)
    (hc : ∀ x ∈ X, ∀ v ∈ V, x * v = v * x) : IsElemAb2 (X ⊔ V) := by
  have h1 : X ⊔ V ≤ Subgroup.centralizer (X : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; exact ((hX h hh).2 x hx)
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; exact hc h hh v hv
  have h2 : X ⊔ V ≤ Subgroup.centralizer (V : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; exact (hc x hx h hh).symm
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro h hh; exact ((hV h hh).2 v hv)
  have h3 : X ≤ Subgroup.centralizer ((X ⊔ V : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 h1
  have h4 : V ≤ Subgroup.centralizer ((X ⊔ V : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 h2
  have h5 : X ⊔ V ≤ Subgroup.centralizer ((X ⊔ V : Subgroup G) : Set G) := sup_le h3 h4
  have hcomm : ∀ a ∈ X ⊔ V, ∀ b ∈ X ⊔ V, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.mem_centralizer_iff.1 (h5 ha) b hb
    exact this.symm
  intro a ha
  refine ⟨?_, fun b hb => hcomm a ha b hb⟩
  rw [Subgroup.sup_eq_closure] at ha hcomm
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact (hX x hx).1
    · exact (hV x hx).1
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := hcomm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ihx, inv_one]

theorem card_le_relIndex_mul_of_max [Finite G] {H V A : Subgroup G} (hV : IsElemAb2 V)
    (hVH : V ≤ H) (hA : IsElemAb2 A) (hAH : A ≤ H)
    (hmax : ∀ B : Subgroup G, B ≤ H → IsElemAb2 B → Nat.card B ≤ Nat.card A) :
    Nat.card V ≤ (H ⊓ Subgroup.centralizer (V : Set G)).relIndex A *
      Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := by
  set C := H ⊓ Subgroup.centralizer (V : Set G) with hC
  set X := A ⊓ C with hX
  have hXA : X ≤ A := inf_le_left
  have hXc : ∀ x ∈ X, ∀ v ∈ V, x * v = v * x := by
    intro x hx v hv
    have h := Subgroup.mem_centralizer_iff.1 hx.2.2 v hv
    exact h.symm
  have hXab : IsElemAb2 X := hA.mono hXA
  have hD := isElemAb2_sup hXab hV hXc
  have hDH : X ⊔ V ≤ H := sup_le (hXA.trans hAH) hVH
  have hDA : Nat.card ↥(X ⊔ V) ≤ Nat.card A := hmax _ hDH hD
  have hprod := card_mul_le_card_inf_mul_card_sup X V
  have hXV : X ⊓ V ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    show x ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hA a ha).2 x (hXA hx.1)
  have hcv : Nat.card ↥(X ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.card_le_of_le hXV
  have hri : C.relIndex A * Nat.card ↥X = Nat.card A := by
    have := Subgroup.relIndex_mul_card C A
    rwa [inf_comm] at this
  have hXpos : 0 < Nat.card X := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left (c := Nat.card X) ?_ hXpos
  calc Nat.card X * Nat.card V ≤ Nat.card ↥(X ⊓ V) * Nat.card ↥(X ⊔ V) := hprod
    _ ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) * Nat.card A :=
        Nat.mul_le_mul hcv hDA
    _ = Nat.card X * (C.relIndex A * Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) := by
        rw [← hri]; ring

theorem relIndex_centralizer_le [Finite G] {U V : Subgroup G} (hUV : U ≤ V) (A : Set G) :
    (Subgroup.centralizer A).relIndex U ≤ (Subgroup.centralizer A).relIndex V :=
  have : (Subgroup.centralizer A).relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
  Subgroup.relIndex_le_of_le_right hUV this

theorem relIndex_le_of_max [Finite G] {H V U A : Subgroup G} (hV : IsElemAb2 V)
    (hVH : V ≤ H) (hUV : U ≤ V) (hA : IsElemAb2 A) (hAH : A ≤ H)
    (hmax : ∀ B : Subgroup G, B ≤ H → IsElemAb2 B → Nat.card B ≤ Nat.card A) :
    (Subgroup.centralizer (A : Set G)).relIndex U ≤
      (H ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
  have h1 := card_le_relIndex_mul_of_max hV hVH hA hAH hmax
  have h2 : (Subgroup.centralizer (A : Set G)).relIndex V *
      Nat.card ↥(Subgroup.centralizer (A : Set G) ⊓ V) = Nat.card V :=
    Subgroup.relIndex_mul_card _ _
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
  have h3 : (Subgroup.centralizer (A : Set G)).relIndex V ≤
      (H ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
    rw [inf_comm (Subgroup.centralizer (A : Set G)) V] at h2
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (Subgroup.centralizer (A : Set G)).relIndex V *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) = Nat.card V := h2
      _ ≤ _ := h1
  exact le_trans (relIndex_centralizer_le hUV _) h3

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
