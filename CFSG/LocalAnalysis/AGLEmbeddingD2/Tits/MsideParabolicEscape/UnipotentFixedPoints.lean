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

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem card_ker_comp_le {A : Type*} [Group A] [Finite A] (φ ψ : A →* A) :
    Nat.card (φ.comp ψ).ker ≤ Nat.card ψ.ker * Nat.card φ.ker := by
  set K := (φ.comp ψ).ker with hK
  let f : K →* A := ψ.comp K.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker ≤ Nat.card ψ.ker := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : K) : A), k.2⟩) ?_
    intro a b hab
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  have hrange : Nat.card f.range ≤ Nat.card φ.ker := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨k, rfl⟩
    exact k.2
  calc Nat.card K = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card ψ.ker * Nat.card φ.ker := Nat.mul_le_mul hker hrange

theorem sub_cube_apply {A : Type*} [AddCommGroup A] (σ : A →+ A) (hσ : ∀ a, σ (σ (σ a)) = a)
    (hexp : ∀ a : A, 3 • a = 0) (a : A) :
    (AddMonoidHom.id A - σ) ((AddMonoidHom.id A - σ) ((AddMonoidHom.id A - σ) a)) = 0 := by
  simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub]
  have h1 := hexp (σ a)
  have h2 := hexp (σ (σ a))
  have h3 := hσ a
  calc a - σ a - (σ a - σ (σ a)) - (σ a - σ (σ a) - (σ (σ a) - σ (σ (σ a))))
      = a - σ (σ (σ a)) - 3 • σ a + 3 • σ (σ a) := by abel
    _ = 0 := by rw [h3, h1, h2]; abel

theorem card_le_card_ker_pow_three {A : Type*} [CommGroup A] [Finite A] (σ : A →* A)
    (hσ : ∀ a, σ (σ (σ a)) = a) (hexp : ∀ a : A, a ^ 3 = 1) :
    Nat.card A ≤ Nat.card (MonoidHom.id A * σ⁻¹).ker ^ 3 := by
  set ψ : A →* A := MonoidHom.id A * σ⁻¹ with hψ
  have hcube : ∀ a, ψ (ψ (ψ a)) = 1 := by
    intro a
    have h := sub_cube_apply (A := Additive A) (MonoidHom.toAdditive σ)
      (fun a => hσ a.toMul) (fun a => by
        show Additive.ofMul (a.toMul ^ 3) = 0
        rw [hexp]; rfl) (Additive.ofMul a)
    have step : ∀ b : A, (AddMonoidHom.id (Additive A) - MonoidHom.toAdditive σ)
        (Additive.ofMul b) = Additive.ofMul (ψ b) := fun b => by
      show Additive.ofMul b - Additive.ofMul (σ b) = _
      rw [sub_eq_add_neg]
      rfl
    rw [step, step, step] at h
    exact h
  have hK3 : (ψ.comp (ψ.comp ψ)).ker = ⊤ := by
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_top, iff_true]
    exact hcube a
  have h21 := card_ker_comp_le ψ ψ
  have h32 := card_ker_comp_le ψ (ψ.comp ψ)
  rw [hK3, Subgroup.card_top] at h32
  have hle : Nat.card A ≤ Nat.card (ψ.comp ψ).ker * Nat.card ψ.ker := h32
  calc Nat.card A ≤ Nat.card (ψ.comp ψ).ker * Nat.card ψ.ker := hle
    _ ≤ (Nat.card ψ.ker * Nat.card ψ.ker) * Nat.card ψ.ker :=
        Nat.mul_le_mul_right _ h21
    _ = Nat.card ψ.ker ^ 3 := by ring

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
