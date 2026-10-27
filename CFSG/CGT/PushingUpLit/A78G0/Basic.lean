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

namespace CFSG.CGT.PushingUpLit.A78G0

variable {G : Type} [Group G]

abbrev cs (H : Subgroup G) (g : G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cs {H : Subgroup G} {g x : G} : x ∈ cs H g ↔ g⁻¹ * x * g ∈ H := by
  show x ∈ H.map (MulAut.conj g).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conj_mem_cs {H : Subgroup G} (g : G) {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cs H g :=
  Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem cs_mul (H : Subgroup G) (x y : G) : cs H (x * y) = cs (cs H y) x := by
  ext z
  rw [mem_cs, mem_cs, mem_cs]
  have : y⁻¹ * (x⁻¹ * z * x) * y = (x * y)⁻¹ * z * (x * y) := by group
  rw [this]

theorem cs_one (H : Subgroup G) : cs H 1 = H := by
  ext z
  rw [mem_cs]
  simp

theorem cs_cs_inv (H : Subgroup G) (g : G) : cs (cs H g) g⁻¹ = H := by
  rw [← cs_mul, inv_mul_cancel, cs_one]

theorem cs_inv_cs (H : Subgroup G) (g : G) : cs (cs H g⁻¹) g = H := by
  have := cs_cs_inv H g⁻¹
  rwa [inv_inv] at this

theorem cs_mono {H K : Subgroup G} (h : H ≤ K) (g : G) : cs H g ≤ cs K g := Subgroup.map_mono h

theorem cs_le_cs_iff {H K : Subgroup G} (g : G) : cs H g ≤ cs K g ↔ H ≤ K := by
  constructor
  · intro h x hx
    have := h (conj_mem_cs g hx)
    rw [mem_cs] at this
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at this
  · exact fun h => cs_mono h g

theorem cs_inj_iff {H K : Subgroup G} (g : G) : cs H g = cs K g ↔ H = K := by
  constructor
  · intro h
    exact le_antisymm ((cs_le_cs_iff g).1 h.le) ((cs_le_cs_iff g).1 h.ge)

  · intro h
    rw [h]

theorem cs_sup (A B : Subgroup G) (g : G) : cs (A ⊔ B) g = cs A g ⊔ cs B g :=
  Subgroup.map_sup A B _

theorem card_cs (H : Subgroup G) (g : G) : Nat.card (cs H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cs_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    cs H g = H := by
  ext x
  rw [mem_cs]
  exact (Subgroup.mem_normalizer_iff''.1 hg x).symm

theorem mem_normalizer_of_cs_eq {H : Subgroup G} {g : G} (h : cs H g = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  rw [← mem_cs, h]

theorem le_normalizer_of_conj' {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h a ha x hx, fun hx => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hx
  simpa [mul_assoc] using this

theorem conj_mem_of_mem_normalizer' {H : Subgroup G} {x a : G}
    (hx : x ∈ Subgroup.normalizer (H : Set G)) (ha : a ∈ H) : x * a * x⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.1 hx a).1 ha

end CFSG.CGT.PushingUpLit.A78G0
