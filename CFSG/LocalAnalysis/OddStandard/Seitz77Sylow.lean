module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
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

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Field

variable {F : Type} [Field F]

theorem exists_add_map_eq [Finite F] [CharP F 2] (φ : F ≃+* F) (hφ : ∀ x, φ (φ x) = x)
    (hne : ∃ x, φ x ≠ x) : ∀ c, φ c = c → ∃ d, c = d + φ d := by
  classical
  let K : Subfield F := RingHom.eqLocusField (φ : F →+* F) (RingHom.id F)
  have hK : ∀ x : F, x ∈ K ↔ φ x = x := fun x => Iff.rfl
  have hchar : ∀ x : F, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  have : Module.Finite K F := Module.Finite.of_finite
  let ψ : F →ₗ[K] F :=
    { toFun := fun x => x + φ x
      map_add' := fun x y => by
        rw [map_add]
        ring
      map_smul' := fun k x => by
        have hk : φ (k : F) = k := (hK k).1 k.2
        show k * x + φ (k * x) = k * (x + φ x)
        rw [map_mul, hk]
        ring }
  have hψ : ∀ x, ψ x = x + φ x := fun x => rfl
  have hker : LinearMap.ker ψ = LinearMap.range (Algebra.linearMap K F) := by
    ext x
    rw [LinearMap.mem_ker, hψ, LinearMap.mem_range]
    constructor
    · intro h
      have h1 : φ x = x := by
        have := eq_neg_of_add_eq_zero_right h
        rwa [CharTwo.neg_eq] at this
      exact ⟨⟨x, (hK x).2 h1⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      have hk : φ (k : F) = k := (hK k).1 k.2
      show (k : F) + φ k = 0
      rw [hk]
      exact hchar _
  have hrange_le : LinearMap.range ψ ≤ LinearMap.ker ψ := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hψ, hψ, map_add, hφ]
    have h1 := hchar x
    have h2 := hchar (φ x)
    calc x + φ x + (φ x + x) = (x + x) + (φ x + φ x) := by ring
      _ = 0 := by rw [h1, h2, add_zero]
  have hker_dim : Module.finrank K (LinearMap.ker ψ) = 1 := by
    rw [hker, LinearMap.finrank_range_of_inj (f := Algebra.linearMap K F)
      (show Function.Injective (algebraMap K F) from (algebraMap K F).injective)]
    exact Module.finrank_self K
  have hrange_ne : 1 ≤ Module.finrank K (LinearMap.range ψ) := by
    obtain ⟨x, hx⟩ := hne
    have hψx : ψ x ≠ 0 := by
      intro h
      apply hx
      have := eq_neg_of_add_eq_zero_right (show x + φ x = 0 from h)
      rwa [CharTwo.neg_eq] at this
    have : LinearMap.range ψ ≠ ⊥ := fun h => hψx (by
      have : ψ x ∈ LinearMap.range ψ := ⟨x, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot K).1 this)
    exact Submodule.one_le_finrank_iff.2 this
  have hle : Module.finrank K (LinearMap.range ψ) ≤ 1 := by
    rw [← hker_dim]
    exact Submodule.finrank_mono hrange_le
  have heq : LinearMap.range ψ = LinearMap.ker ψ :=
    Submodule.eq_of_le_of_finrank_eq hrange_le (by rw [hker_dim]; omega)
  intro c hc
  have hcker : c ∈ LinearMap.ker ψ := by
    rw [LinearMap.mem_ker, hψ, hc]
    exact hchar c
  rw [← heq] at hcker
  obtain ⟨d, hd⟩ := hcker
  exact ⟨d, hd.symm⟩

end Field

section SL

variable {F : Type} [Field F]

theorem unipU_inj {a b c a' b' c' : F} (h : unipU F a b c = unipU F a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_unipU] at h'
  have h01 := congrFun (congrFun h' 0) 1
  have h12 := congrFun (congrFun h' 1) 2
  have h02 := congrFun (congrFun h' 0) 2
  simp at h01 h12 h02
  exact ⟨h01, h12, h02⟩

theorem mem_unipCenter {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ unipCenter F ↔ ∃ c, unipU F 0 0 c = g := Iff.rfl

theorem mem_unipAll {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ unipAll F ↔ ∃ a b c, unipU F a b c = g := Iff.rfl

theorem card_unipAll : Nat.card (unipAll F) = Nat.card F ^ 3 := by
  let e : F × F × F ≃ unipAll F :=
    { toFun := fun x => ⟨unipU F x.1 x.2.1 x.2.2, ⟨x.1, x.2.1, x.2.2, rfl⟩⟩
      invFun := fun g => ((mem_unipAll.1 g.2).choose, (mem_unipAll.1 g.2).choose_spec.choose,
        (mem_unipAll.1 g.2).choose_spec.choose_spec.choose)
      left_inv := fun x => by
        have h := (mem_unipAll.1 (⟨unipU F x.1 x.2.1 x.2.2, ⟨x.1, x.2.1, x.2.2, rfl⟩⟩ :
          unipAll F).2).choose_spec.choose_spec.choose_spec
        obtain ⟨h1, h2, h3⟩ := unipU_inj h
        exact Prod.ext h1 (Prod.ext h2 h3)
      right_inv := fun g => by
        apply Subtype.ext
        exact (mem_unipAll.1 g.2).choose_spec.choose_spec.choose_spec }
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem mem_unipOne {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ unipOne F ↔ ∃ a c, unipU F a 0 c = g := Iff.rfl

theorem mem_unipTwo {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ unipTwo F ↔ ∃ b c, unipU F 0 b c = g := Iff.rfl

variable [CharP F 2]

theorem le_unipOne_or_le_unipTwo (E : Subgroup (SpecialLinearGroup (Fin 3) F)) (hE : E ≤ unipAll F)
    (hsq : ∀ g ∈ E, g * g = 1) : E ≤ unipOne F ∨ E ≤ unipTwo F := by
  have hab : ∀ a b c : F, unipU F a b c ∈ E → a * b = 0 := by
    intro a b c hg
    have h := hsq _ hg
    rw [unipU_mul, ← unipU_zero] at h
    have := (unipU_inj h).2.2
    have h2 : c + c = 0 := CharTwo.add_self_eq_zero c
    linear_combination this - h2
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h1' : ∃ g ∈ E, g ∉ unipOne F := by
    by_contra h
    push Not at h
    exact h1 h
  have h2' : ∃ g ∈ E, g ∉ unipTwo F := by
    by_contra h
    push Not at h
    exact h2 h
  obtain ⟨g₁, hg₁E, hg₁⟩ := h1'
  obtain ⟨g₂, hg₂E, hg₂⟩ := h2'
  obtain ⟨a₁, b₁, c₁, rfl⟩ := mem_unipAll.1 (hE hg₁E)
  obtain ⟨a₂, b₂, c₂, rfl⟩ := mem_unipAll.1 (hE hg₂E)
  have hb₁ : b₁ ≠ 0 := fun h => hg₁ (mem_unipOne.2 ⟨a₁, c₁, by rw [h]⟩)
  have ha₂ : a₂ ≠ 0 := fun h => hg₂ (mem_unipTwo.2 ⟨b₂, c₂, by rw [h]⟩)
  have ha₁ : a₁ = 0 := by
    have := hab _ _ _ hg₁E
    exact (mul_eq_zero.1 this).resolve_right hb₁
  have hb₂ : b₂ = 0 := by
    have := hab _ _ _ hg₂E
    exact (mul_eq_zero.1 this).resolve_left ha₂
  have hprod := E.mul_mem hg₁E hg₂E
  rw [unipU_mul] at hprod
  have := hab _ _ _ hprod
  rw [ha₁, hb₂, zero_add, add_zero] at this
  exact mul_ne_zero ha₂ hb₁ this

end SL

end CFSG.OddStandard.Seitz77
