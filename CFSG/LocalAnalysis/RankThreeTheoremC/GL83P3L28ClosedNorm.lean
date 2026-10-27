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

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

section NormHom

variable {Y : Type} [Group Y] (D : Subgroup Y) [D.Normal] (t : Y)

@[expose] def normMap : D →* Abelianization D where
  toFun d := Abelianization.of d * Abelianization.of (MulAut.conjNormal t d)
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem normMap_apply (d : D) :
    normMap D t d = Abelianization.of d * Abelianization.of (MulAut.conjNormal t d) := rfl

theorem exists_norm_hom (ht : ∀ y : Y, y ∉ D → t⁻¹ * y ∈ D) :
    ∃ h : Y →* Abelianization D, ∀ d : D, h d = (normMap D t d) ^ 2 := by
  have hconj : ∀ (g d : Y), d ∈ D → g * d * g⁻¹ ∈ D := fun g d hd => by
    simpa using (inferInstance : D.Normal).conj_mem d hd g
  have ht2 : ∀ y : Y, y ∉ D → t ^ 2 ∈ D := by
    intro y hy
    have h1 := ht y hy
    have htD : t ∉ D := fun htD => hy (by simpa using D.mul_mem htD h1)
    by_contra h2
    have := ht (t ^ 2) h2
    exact htD (by simpa [pow_two] using this)
  have hsq : ∀ y : Y, y ^ 2 ∈ D := by
    intro y
    by_cases hy : y ∈ D
    · exact D.pow_mem hy 2
    · have h1 := ht y hy
      have e : y ^ 2 = t ^ 2 * (t⁻¹ * (t⁻¹ * y) * t) * (t⁻¹ * y) := by
        simp only [pow_two]
        group
      rw [e]
      exact D.mul_mem (D.mul_mem (ht2 y hy) (by simpa using hconj t⁻¹ _ h1)) h1
  have hD : ∀ c d : D, normMap D t (c * d * c⁻¹) = normMap D t d := by
    intro c d
    rw [map_mul, map_mul, map_inv]
    rw [mul_comm (normMap D t c) (normMap D t d), mul_inv_cancel_right]
  have hinv : ∀ (y : Y) (d e : D), (e : Y) = y * d * y⁻¹ → normMap D t e = normMap D t d := by
    intro y d e hye
    by_cases hy : y ∈ D
    · have : e = ⟨y, hy⟩ * d * ⟨y, hy⟩⁻¹ := Subtype.ext hye
      rw [this]
      exact hD _ _
    · have h1 := ht y hy
      obtain ⟨d', hd'def⟩ : ∃ d' : D, d' = (⟨t⁻¹ * y, h1⟩ : D) * d * (⟨t⁻¹ * y, h1⟩ : D)⁻¹ :=
        ⟨_, rfl⟩
      have hed : e = MulAut.conjNormal t d' := Subtype.ext (by
        rw [hye, MulAut.conjNormal_apply, hd'def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group)
      have hdd : normMap D t d' = normMap D t d := by rw [hd'def]; exact hD _ _
      have htt : MulAut.conjNormal t (MulAut.conjNormal t d') =
          (⟨t ^ 2, ht2 y hy⟩ : D) * d' * (⟨t ^ 2, ht2 y hy⟩ : D)⁻¹ := Subtype.ext (by
        simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, pow_two]
        group)
      rw [hed, ← hdd]
      show Abelianization.of (MulAut.conjNormal t d') *
          Abelianization.of (MulAut.conjNormal t (MulAut.conjNormal t d')) =
        Abelianization.of d' * Abelianization.of (MulAut.conjNormal t d')
      rw [htt, map_mul, map_mul, map_inv, mul_comm (Abelianization.of (⟨t ^ 2, ht2 y hy⟩ : D)),
        mul_inv_cancel_right, mul_comm]
  have hcomm : ∀ y₁ y₂ : Y, ∃ hc : y₁⁻¹ * y₂ * y₁ * y₂⁻¹ ∈ D,
      normMap D t ⟨y₁⁻¹ * y₂ * y₁ * y₂⁻¹, hc⟩ = 1 := by
    intro y₁ y₂
    by_cases h2 : y₂ ∈ D
    · have e1 : y₁⁻¹ * y₂ * y₁ ∈ D := by simpa using hconj y₁⁻¹ y₂ h2
      have hc : y₁⁻¹ * y₂ * y₁ * y₂⁻¹ ∈ D := D.mul_mem e1 (D.inv_mem h2)
      refine ⟨hc, ?_⟩
      have : (⟨y₁⁻¹ * y₂ * y₁ * y₂⁻¹, hc⟩ : D) = ⟨y₁⁻¹ * y₂ * y₁, e1⟩ * ⟨y₂, h2⟩⁻¹ :=
        Subtype.ext rfl
      rw [this, map_mul, map_inv, hinv y₁⁻¹ ⟨y₂, h2⟩ ⟨y₁⁻¹ * y₂ * y₁, e1⟩ (by simp),
        mul_inv_cancel]
    · by_cases h1 : y₁ ∈ D
      · have e2 : y₂ * y₁ * y₂⁻¹ ∈ D := hconj y₂ y₁ h1
        have hc : y₁⁻¹ * y₂ * y₁ * y₂⁻¹ ∈ D := by
          have : y₁⁻¹ * y₂ * y₁ * y₂⁻¹ = y₁⁻¹ * (y₂ * y₁ * y₂⁻¹) := by group
          rw [this]
          exact D.mul_mem (D.inv_mem h1) e2
        refine ⟨hc, ?_⟩
        have : (⟨y₁⁻¹ * y₂ * y₁ * y₂⁻¹, hc⟩ : D) = ⟨y₁, h1⟩⁻¹ * ⟨y₂ * y₁ * y₂⁻¹, e2⟩ :=
          Subtype.ext (by simp [mul_assoc])
        rw [this, map_mul, map_inv, hinv y₂ ⟨y₁, h1⟩ ⟨y₂ * y₁ * y₂⁻¹, e2⟩ rfl, inv_mul_cancel]
      · have hd : y₁⁻¹ * y₂ ∈ D := by
          have := D.mul_mem (D.inv_mem (ht y₁ h1)) (ht y₂ h2)
          have e : (t⁻¹ * y₁)⁻¹ * (t⁻¹ * y₂) = y₁⁻¹ * y₂ := by group
          rwa [e] at this
        have e3 : y₁ * (y₁⁻¹ * y₂)⁻¹ * y₁⁻¹ ∈ D := hconj y₁ _ (D.inv_mem hd)
        have hc : y₁⁻¹ * y₂ * y₁ * y₂⁻¹ ∈ D := by
          have : y₁⁻¹ * y₂ * y₁ * y₂⁻¹ = (y₁⁻¹ * y₂) * (y₁ * (y₁⁻¹ * y₂)⁻¹ * y₁⁻¹) := by group
          rw [this]
          exact D.mul_mem hd e3
        refine ⟨hc, ?_⟩
        have : (⟨y₁⁻¹ * y₂ * y₁ * y₂⁻¹, hc⟩ : D) =
            ⟨y₁⁻¹ * y₂, hd⟩ * ⟨y₁ * (y₁⁻¹ * y₂)⁻¹ * y₁⁻¹, e3⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul]
          group)
        rw [this, map_mul, hinv y₁ (⟨y₁⁻¹ * y₂, hd⟩ : D)⁻¹ ⟨y₁ * (y₁⁻¹ * y₂)⁻¹ * y₁⁻¹, e3⟩ rfl,
          map_inv, mul_inv_cancel]
  refine ⟨MonoidHom.mk' (fun y => normMap D t ⟨y ^ 2, hsq y⟩) ?_, ?_⟩
  · intro y₁ y₂
    obtain ⟨hc, hc1⟩ := hcomm y₁ y₂
    have hprod : (⟨(y₁ * y₂) ^ 2, hsq _⟩ : D) =
        ⟨y₁ ^ 2, hsq y₁⟩ * ⟨y₁⁻¹ * y₂ * y₁ * y₂⁻¹, hc⟩ * ⟨y₂ ^ 2, hsq y₂⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, pow_two]; group)
    show normMap D t ⟨(y₁ * y₂) ^ 2, hsq _⟩ =
      normMap D t ⟨y₁ ^ 2, hsq y₁⟩ * normMap D t ⟨y₂ ^ 2, hsq y₂⟩
    rw [hprod, map_mul, map_mul, hc1, mul_one]
  · intro d
    show normMap D t ⟨(d : Y) ^ 2, hsq d⟩ = (normMap D t d) ^ 2
    rw [show (⟨(d : Y) ^ 2, hsq d⟩ : D) = d ^ 2 from Subtype.ext rfl, map_pow]

end NormHom

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
