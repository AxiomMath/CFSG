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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix

theorem eq_scalar_of_forall_commute {k : Type*} [Field k] (g : GL (Fin 3) k)
    (h : ∀ s : SpecialLinearGroup (Fin 3) k,
      (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) =
        (s : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)) :
    ∃ c : kˣ, (g : Matrix (Fin 3) (Fin 3) k) = (c : k) • (1 : Matrix (Fin 3) (Fin 3) k) := by
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct
    (M := (g : Matrix (Fin 3) (Fin 3) k)) fun t =>
      (h (Matrix.TransvectionStruct.toSpecialLinearGroup t)).symm
  have hdet : (g : Matrix (Fin 3) (Fin 3) k).det = r ^ 3 := by
    rw [← hr]; simp
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact Matrix.GeneralLinearGroup.det_ne_zero g (by rw [hdet]; norm_num)
  refine ⟨Units.mk0 r hr0, ?_⟩
  rw [← hr]
  ext i j
  simp [Matrix.one_apply, Matrix.diagonal_apply]

private theorem exists_scalar_of_conj_eq {k : Type*} [Field k] (g₁ g₂ : GL (Fin 3) k)
    (h : ∀ s : SpecialLinearGroup (Fin 3) k,
      g₁ * SpecialLinearGroup.toGL s * g₁⁻¹ = g₂ * SpecialLinearGroup.toGL s * g₂⁻¹) :
    ∃ c : kˣ, g₂ = g₁ * GeneralLinearGroup.scalar (Fin 3) c := by
  have hc : ∀ s : SpecialLinearGroup (Fin 3) k,
      ((g₁⁻¹ * g₂ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) =
        (s : Matrix (Fin 3) (Fin 3) k) *
          ((g₁⁻¹ * g₂ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
    intro s
    have h1 : g₁⁻¹ * g₂ * SpecialLinearGroup.toGL s =
        SpecialLinearGroup.toGL s * (g₁⁻¹ * g₂) := by
      calc g₁⁻¹ * g₂ * SpecialLinearGroup.toGL s
          = g₁⁻¹ * (g₂ * SpecialLinearGroup.toGL s * g₂⁻¹) * g₂ := by group
        _ = g₁⁻¹ * (g₁ * SpecialLinearGroup.toGL s * g₁⁻¹) * g₂ := by rw [h s]
        _ = SpecialLinearGroup.toGL s * (g₁⁻¹ * g₂) := by group
    exact congrArg Units.val h1
  obtain ⟨c, hc'⟩ := eq_scalar_of_forall_commute (g₁⁻¹ * g₂) hc
  refine ⟨c, ?_⟩
  have h2 : g₁⁻¹ * g₂ = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [hc', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [← h2]
  group

private theorem card_units_quotient_cubes_dvd_three {k : Type*} [Field k] [Finite k] :
    Nat.card (kˣ ⧸ (powMonoidHom 3 : kˣ →* kˣ).range) ∣ 3 := by
  have : IsCyclic (kˣ ⧸ (powMonoidHom 3 : kˣ →* kˣ).range) :=
    isCyclic_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨u, rfl⟩

theorem exists_inner_of_index {k : Type} [Field k] [Finite k]
    {A : Type} [Group A] [Finite A]
    (φ : A →* MulAut (SpecialLinearGroup (Fin 3) k))
    (hφ : ∀ a, ∃ g : GL (Fin 3) k, ∀ s : SpecialLinearGroup (Fin 3) k,
      ((φ a s : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
          ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k))
    (hcard : 3 * Nat.card φ.ker < Nat.card A) :
    ∃ a : A, a ∉ φ.ker ∧ ∃ s : SpecialLinearGroup (Fin 3) k, ∀ t, φ a t = s * t * s⁻¹ := by
  classical
  choose g hg using hφ
  have hg' : ∀ (a : A) (s : SpecialLinearGroup (Fin 3) k),
      SpecialLinearGroup.toGL (φ a s) = g a * SpecialLinearGroup.toGL s * (g a)⁻¹ := by
    intro a s
    exact Units.ext (hg a s)
  set H : Subgroup kˣ := (powMonoidHom 3 : kˣ →* kˣ).range
  let D : GL (Fin 3) k →* kˣ ⧸ H :=
    (QuotientGroup.mk' H).comp GeneralLinearGroup.det
  have hD : ∀ g₁ g₂ : GL (Fin 3) k,
      (∀ s : SpecialLinearGroup (Fin 3) k,
        g₁ * SpecialLinearGroup.toGL s * g₁⁻¹ = g₂ * SpecialLinearGroup.toGL s * g₂⁻¹) →
      D g₁ = D g₂ := by
    intro g₁ g₂ h
    obtain ⟨c, rfl⟩ := exists_scalar_of_conj_eq g₁ g₂ h
    have hc : D (GeneralLinearGroup.scalar (Fin 3) c) = 1 := by
      simp only [D, MonoidHom.comp_apply, GeneralLinearGroup.det_scalar, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq_one_iff]
      exact ⟨c, by simp⟩
    rw [map_mul, hc, mul_one]
  let Δ : A →* kˣ ⧸ H :=
    { toFun := fun a => D (g a)
      map_one' := by
        rw [hD (g 1) 1 ?_, map_one]
        intro s
        rw [← hg' 1 s]
        simp
      map_mul' := by
        intro a b
        rw [← map_mul]
        apply hD
        intro s
        rw [← hg' (a * b) s, map_mul, MulAut.mul_apply, hg' a, hg' b]
        group }
  have hindex : Nat.card A ≤ 3 * Nat.card Δ.ker := by
    have h1 : Nat.card Δ.ker * Δ.ker.index = Nat.card A := Subgroup.card_mul_index _
    have h2 : Δ.ker.index = Nat.card Δ.range := Subgroup.index_ker Δ
    have h3 : Nat.card Δ.range ≤ Nat.card (kˣ ⧸ H) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have h4 : Nat.card (kˣ ⧸ H) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) card_units_quotient_cubes_dvd_three
    calc Nat.card A = Nat.card Δ.ker * Δ.ker.index := h1.symm
      _ ≤ Nat.card Δ.ker * 3 := Nat.mul_le_mul_left _ (h2 ▸ h3.trans h4)
      _ = 3 * Nat.card Δ.ker := mul_comm _ _
  have hex : ∃ a ∈ Δ.ker, a ∉ φ.ker := by
    by_contra hne
    have hle : Δ.ker ≤ φ.ker := fun a ha => by
      by_contra ha'
      exact hne ⟨a, ha, ha'⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨a, haΔ, haφ⟩ := hex
  refine ⟨a, haφ, ?_⟩
  have hdet : GeneralLinearGroup.det (g a) ∈ H := by
    have h0 : D (g a) = 1 := haΔ
    simpa [D, QuotientGroup.eq_one_iff] using h0
  obtain ⟨u, hu⟩ := hdet
  have hs : GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g a ∈
      (GeneralLinearGroup.det : GL (Fin 3) k →* kˣ).ker := by
    rw [MonoidHom.mem_ker, map_mul, GeneralLinearGroup.det_scalar, ← hu]
    simp
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det] at hs
  obtain ⟨s, hs⟩ := hs
  refine ⟨s, fun t => ?_⟩
  apply SpecialLinearGroup.toGL_injective
  rw [hg' a t, map_mul, map_mul, map_inv, hs]
  have hcomm := GeneralLinearGroup.scalar_commute (n := Fin 3) (R := k) u⁻¹
  calc g a * SpecialLinearGroup.toGL t * (g a)⁻¹
      = GeneralLinearGroup.scalar (Fin 3) u⁻¹ * (g a * SpecialLinearGroup.toGL t * (g a)⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) u⁻¹)⁻¹ := by
        rw [hcomm (g a * SpecialLinearGroup.toGL t * (g a)⁻¹)]; group
    _ = _ := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
