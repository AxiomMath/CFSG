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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

@[expose] def invTr : MulAut (GL (Fin 3) F) where
  toFun M := ⟨((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose,
    (M : Matrix (Fin 3) (Fin 3) F).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  invFun M := ⟨((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose,
    (M : Matrix (Fin 3) (Fin 3) F).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  left_inv M := Units.ext (by simp)
  right_inv M := Units.ext (by simp)
  map_mul' M N := Units.ext (by simp [Matrix.transpose_mul])

theorem coe_invTr (M : GL (Fin 3) F) :
    ((invTr M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose :=
  rfl

@[expose] def dpow (ε : Bool) : MulAut (GL (Fin 3) F) := cond ε invTr 1

theorem dpow_comm (ε δ : Bool) :
    (dpow ε : MulAut (GL (Fin 3) F)) * dpow δ = dpow δ * dpow ε := by
  cases ε <;> cases δ <;> simp [dpow]

theorem mul_conj_eq {Γ : Type} [Group Γ] (φ : MulAut Γ) (g : Γ) :
    φ * MulAut.conj g = MulAut.conj (φ g) * φ := by
  ext x
  simp [MulAut.conj_apply]

variable {S E : Type} [Group S] [Group E]

@[expose] def innerDiag (θ : S →* E) (ι : S →* GL (Fin 3) F) (hι : Function.Injective ι)
    (N : Subgroup (GL (Fin 3) F)) (hN : ∀ M ∈ N, ∀ x : S, ∃ z : S, ι z = M * ι x * M⁻¹) :
    Subgroup (MulAut E) where
  carrier := {ψ | ∃ M ∈ N, ∀ x z : S, ι z = M * ι x * M⁻¹ → ψ (θ x) = θ z}
  one_mem' := ⟨1, N.one_mem, fun x z h => by
    rw [one_mul, inv_one, mul_one] at h
    rw [hι h]
    rfl⟩
  mul_mem' := by
    rintro ψ₁ ψ₂ ⟨M₁, hM₁, h₁⟩ ⟨M₂, hM₂, h₂⟩
    refine ⟨M₁ * M₂, N.mul_mem hM₁ hM₂, fun x z h => ?_⟩
    obtain ⟨w, hw⟩ := hN M₂ hM₂ x
    rw [MulAut.mul_apply, h₂ x w hw]
    refine h₁ w z ?_
    rw [h, hw]
    group
  inv_mem' := by
    rintro ψ ⟨M, hM, h⟩
    refine ⟨M⁻¹, N.inv_mem hM, fun x z hz => ?_⟩
    have h1 := h z x (by rw [hz]; group)
    rw [← h1, MulAut.inv_apply_self]

variable (θ : S →* E) (ι : S →* GL (Fin 3) F) (hι : Function.Injective ι)
  (N : Subgroup (GL (Fin 3) F)) (hN : ∀ M ∈ N, ∀ x : S, ∃ z : S, ι z = M * ι x * M⁻¹)

theorem commutator_mem_innerDiag (hND : ∀ M ∈ N, invTr M ∈ N) {φ₁ φ₂ : MulAut E}
    {α₁ α₂ : S →* S} {G₁ G₂ : GL (Fin 3) F} {ε₁ ε₂ : Bool} (hG₁ : G₁ ∈ N) (hG₂ : G₂ ∈ N)
    (hα₁ : ∀ x, θ (α₁ x) = φ₁ (θ x)) (hα₂ : ∀ x, θ (α₂ x) = φ₂ (θ x))
    (hf₁ : ∀ x, ι (α₁ x) = (MulAut.conj G₁ * dpow ε₁ : MulAut (GL (Fin 3) F)) (ι x))
    (hf₂ : ∀ x, ι (α₂ x) = (MulAut.conj G₂ * dpow ε₂ : MulAut (GL (Fin 3) F)) (ι x))
    (hsurj : Function.Surjective (α₂.comp α₁)) :
    ⁅φ₁, φ₂⁆ ∈ innerDiag θ ι hι N hN := by
  have hdN : ∀ (ε : Bool), ∀ M ∈ N, dpow ε M ∈ N := fun ε M hM => by
    cases ε
    · exact hM
    · exact hND M hM
  set P := G₁ * dpow ε₁ G₂
  set Q := G₂ * dpow ε₂ G₁
  have hΛ : (MulAut.conj G₁ * dpow ε₁) * (MulAut.conj G₂ * dpow ε₂) =
      MulAut.conj (P * Q⁻¹) * ((MulAut.conj G₂ * dpow ε₂) * (MulAut.conj G₁ * dpow ε₁)) := by
    have e1 : (MulAut.conj G₁ * dpow ε₁) * (MulAut.conj G₂ * dpow ε₂) =
        MulAut.conj P * (dpow ε₁ * dpow ε₂) := by
      rw [mul_assoc, ← mul_assoc (dpow ε₁), mul_conj_eq, mul_assoc, ← mul_assoc, map_mul]
    have e2 : (MulAut.conj G₂ * dpow ε₂) * (MulAut.conj G₁ * dpow ε₁) =
        MulAut.conj Q * (dpow ε₂ * dpow ε₁) := by
      rw [mul_assoc, ← mul_assoc (dpow ε₂), mul_conj_eq, mul_assoc, ← mul_assoc, map_mul]
    rw [e1, e2, dpow_comm ε₂ ε₁, map_mul MulAut.conj P Q⁻¹, map_inv MulAut.conj Q]
    group
  refine ⟨P * Q⁻¹, N.mul_mem (N.mul_mem hG₁ (hdN ε₁ G₂ hG₂))
    (N.inv_mem (N.mul_mem hG₂ (hdN ε₂ G₁ hG₁))), fun x z hz => ?_⟩
  obtain ⟨w, hw⟩ := hsurj x
  simp only [MonoidHom.comp_apply] at hw
  set Λ₁ : MulAut (GL (Fin 3) F) := MulAut.conj G₁ * dpow ε₁
  set Λ₂ : MulAut (GL (Fin 3) F) := MulAut.conj G₂ * dpow ε₂
  have e3 : ι (α₁ (α₂ w)) = (P * Q⁻¹) * ι (α₂ (α₁ w)) * (P * Q⁻¹)⁻¹ := by
    calc ι (α₁ (α₂ w)) = (Λ₁ * Λ₂) (ι w) := by rw [hf₁, hf₂]; rfl
      _ = (MulAut.conj (P * Q⁻¹) * (Λ₂ * Λ₁)) (ι w) := by rw [hΛ]
      _ = (P * Q⁻¹) * ι (α₂ (α₁ w)) * (P * Q⁻¹)⁻¹ := by
        rw [MulAut.mul_apply, MulAut.conj_apply, hf₂, hf₁]
        rfl
  have hz' : z = α₁ (α₂ w) := by
    apply hι
    rw [hz, ← hw, e3]
  rw [hz', hα₁, hα₂, ← hw, hα₂, hα₁, commutatorElement_def]
  simp only [MulAut.mul_apply, MulAut.inv_apply_self]

theorem derived_derived_eq_bot {G : Type} [Group G] {H A : Subgroup G} (hHA : ⁅H, H⁆ ≤ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : ⁅⁅H, H⁆, ⁅H, H⁆⁆ = ⊥ := by
  refine eq_bot_iff.mpr ((Subgroup.commutator_mono hHA hHA).trans ?_)
  rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hA b hb a ha

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
