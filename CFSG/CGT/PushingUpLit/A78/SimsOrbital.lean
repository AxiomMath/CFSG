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

namespace CFSG.CGT.PushingUpLit.A78.Sims

open MulAction Relation

variable (G : Type*) [Group G] {Ω : Type*} [MulAction G Ω]

@[expose] def Invariant (E : Ω → Ω → Prop) : Prop :=
  ∀ (g : G) (a b : Ω), E a b → E (g • a) (g • b)

variable {G}

theorem Invariant.reflTransGen {E : Ω → Ω → Prop} (hE : Invariant G E) (g : G) {a b : Ω}
    (h : ReflTransGen E a b) : ReflTransGen E (g • a) (g • b) :=
  h.lift (fun x => g • x) fun _ _ hxy => hE g _ _ hxy

theorem Invariant.eqvGen {E : Ω → Ω → Prop} (hE : Invariant G E) (g : G) {a b : Ω}
    (h : EqvGen E a b) : EqvGen E (g • a) (g • b) := by
  induction h with
  | rel x y hxy => exact EqvGen.rel _ _ (hE g x y hxy)
  | refl x => exact EqvGen.refl _
  | symm x y _ ih => exact EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

theorem Invariant.reflTransGen_symm [Finite Ω] [IsPretransitive G Ω] {E : Ω → Ω → Prop}
    (hE : Invariant G E) {a b : Ω} (hab : ReflTransGen E a b) : ReflTransGen E b a := by
  obtain ⟨g, hg⟩ := exists_smul_eq G a b
  set S : Set Ω := {w | ReflTransGen E a w} with hS
  set S' : Set Ω := {w | ReflTransGen E b w} with hS'
  have h1 : S' ⊆ S := fun w hw => hab.trans hw
  have h2 : (fun w => g • w) '' S ⊆ S' := by
    rintro _ ⟨w, hw, rfl⟩
    have := hE.reflTransGen g hw
    rwa [hg] at this
  have h3 : S.ncard ≤ S'.ncard := by
    calc S.ncard = ((fun w => g • w) '' S).ncard :=
          (Set.ncard_image_of_injective _ (MulAction.injective g)).symm
      _ ≤ S'.ncard := Set.ncard_le_ncard h2 (Set.toFinite _)
  have h4 : S' = S := Set.eq_of_subset_of_ncard_le h1 h3 (Set.toFinite _)
  have : a ∈ S' := by
    rw [h4]
    exact ReflTransGen.refl
  exact this

theorem eqvGen_iff_reflTransGen [Finite Ω] [IsPretransitive G Ω] {E : Ω → Ω → Prop}
    (hE : Invariant G E) (a b : Ω) : EqvGen E a b ↔ ReflTransGen E a b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact ReflTransGen.single hxy
    | refl x => exact ReflTransGen.refl
    | symm x y _ ih => exact hE.reflTransGen_symm ih
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact EqvGen.refl _
    | tail _ hbc ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hbc)

theorem connected_of_stabilizer_sup [IsPretransitive G Ω] {E : Ω → Ω → Prop}
    (hE : Invariant G E) {α : Ω} {g : G} (hg : E α (g • α))
    (hgen : stabilizer G α ⊔ Subgroup.zpowers g = ⊤) (a : Ω) : EqvGen E α a := by
  let P : Subgroup G :=
    { carrier := {x | EqvGen E α (x • α)}
      one_mem' := by
        change EqvGen E α ((1 : G) • α)
        rw [one_smul]
        exact EqvGen.refl _
      mul_mem' := by
        intro x y hx hy
        change EqvGen E α ((x * y) • α)
        rw [mul_smul]
        exact EqvGen.trans _ _ _ (hx : EqvGen E α (x • α)) (hE.eqvGen x (hy : EqvGen E α (y • α)))
      inv_mem' := by
        intro x hx
        change EqvGen E α (x⁻¹ • α)
        have := hE.eqvGen x⁻¹ (hx : EqvGen E α (x • α))
        rw [inv_smul_smul] at this
        exact EqvGen.symm _ _ this }
  have hstab : stabilizer G α ≤ P := fun x hx => by
    change EqvGen E α (x • α)
    rw [mem_stabilizer_iff.mp hx]
    exact EqvGen.refl _
  have hz : Subgroup.zpowers g ≤ P := by
    rw [Subgroup.zpowers_le]
    exact EqvGen.rel _ _ hg
  have htop : P = ⊤ := top_le_iff.mp (hgen ▸ sup_le hstab hz)
  obtain ⟨x, hx⟩ := exists_smul_eq G α a
  have : x ∈ P := htop ▸ Subgroup.mem_top x
  rw [← hx]
  exact this

theorem eq_bot_of_fixes_all [FaithfulSMul G Ω] {A : Subgroup G} (h : ∀ a ∈ A, ∀ x : Ω, a • x = x) :
    A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  exact FaithfulSMul.eq_of_smul_eq_smul fun x => by
    rw [one_smul]
    exact h a ha x

end CFSG.CGT.PushingUpLit.A78.Sims
