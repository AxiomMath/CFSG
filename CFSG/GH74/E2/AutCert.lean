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

namespace CFSG.GH74.E2

variable {M : Type*} [Group M] {k : ℕ}

theorem lift_comp_aut (g : Fin k → M) (ψ : MulAut M) (w : FreeGroup (Fin k)) :
    ψ (FreeGroup.lift g w) = FreeGroup.lift (fun i => ψ (g i)) w := by
  have h : (ψ : M →* M).comp (FreeGroup.lift g) = FreeGroup.lift (fun i => ψ (g i)) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun h w

theorem lift_comp_aut_rel (g : Fin k → M) (rs : List (FreeGroup (Fin k)))
    (hrs : ∀ r ∈ rs, FreeGroup.lift g r = 1) (ψ : MulAut M) :
    ∀ r ∈ rs, FreeGroup.lift (fun i => ψ (g i)) r = 1 := by
  intro r hr
  rw [← lift_comp_aut, hrs r hr, map_one]

theorem fix_of_relators (g : Fin k → M) (rs : List (FreeGroup (Fin k)))
    (hrs : ∀ r ∈ rs, FreeGroup.lift g r = 1) (wt : FreeGroup (Fin k))
    (hcert : ∀ h : Fin k → M, (∀ r ∈ rs, FreeGroup.lift h r = 1) →
      FreeGroup.lift h wt ∈ Subgroup.center M → FreeGroup.lift h wt = FreeGroup.lift g wt) :
    ∀ ψ : MulAut M, ψ (FreeGroup.lift g wt) ∈ Subgroup.center M →
      ψ (FreeGroup.lift g wt) = FreeGroup.lift g wt := by
  intro ψ hψ
  rw [lift_comp_aut] at hψ ⊢
  exact hcert _ (lift_comp_aut_rel g rs hrs ψ) hψ

theorem inner_of_relators (g : Fin k → M) (rs : List (FreeGroup (Fin k)))
    (hrs : ∀ r ∈ rs, FreeGroup.lift g r = 1)
    (hcert : ∀ h : Fin k → M, (∀ r ∈ rs, FreeGroup.lift h r = 1) →
      ∃ a : M, ∀ i, h i = a * g i * a⁻¹) :
    ∀ ψ : MulAut M, ∃ a : M, ∀ i, ψ (g i) = a * g i * a⁻¹ := by
  intro ψ
  exact hcert _ (lift_comp_aut_rel g rs hrs ψ)

theorem fix_of_cert4 (a b c d : M) (R : M → M → M → M → Prop)
    (hRaut : ∀ (ψ : MulAut M) (a b c d : M), R a b c d → R (ψ a) (ψ b) (ψ c) (ψ d))
    (hRg : R a b c d) (w : M → M → M → M → M)
    (hw : ∀ (ψ : MulAut M) (a b c d : M), ψ (w a b c d) = w (ψ a) (ψ b) (ψ c) (ψ d))
    (hcert : ∀ a' b' c' d' : M, R a' b' c' d' → w a' b' c' d' ∈ Subgroup.center M →
      w a' b' c' d' = w a b c d) :
    ∀ ψ : MulAut M, ψ (w a b c d) ∈ Subgroup.center M → ψ (w a b c d) = w a b c d := by
  intro ψ hψ
  rw [hw] at hψ ⊢
  exact hcert _ _ _ _ (hRaut ψ a b c d hRg) hψ

theorem fix_transport {S N : Type*} [Group S] [Group N] (e : S ≃* N) {t : S}
    (h : ∀ ψ : MulAut N, ψ (e t) ∈ Subgroup.center N → ψ (e t) = e t) :
    ∀ ψ : MulAut S, ψ t ∈ Subgroup.center S → ψ t = t := by
  intro ψ hψ
  let ψ' : MulAut N := e.symm.trans (ψ.trans e)
  have h1 : ψ' (e t) = e (ψ t) := by simp [ψ']
  have hc : e (ψ t) ∈ Subgroup.center N := by
    rw [← Subgroup.map_center_eq e]
    exact Subgroup.mem_map.2 ⟨ψ t, hψ, rfl⟩
  have h2 := h ψ' (by rw [h1]; exact hc)
  rw [h1] at h2
  exact e.injective h2

end CFSG.GH74.E2
