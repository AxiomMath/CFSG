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

namespace CFSG.QuasithinUnique.I43Dihedral

variable {G : Type*} [Group G]

theorem exists_central_involution_of_sylow_two [Finite G] (P : Sylow 2 G)
    (hP : Nontrivial (P : Subgroup G)) :
    ∃ z : G, z ∈ (P : Subgroup G) ∧ orderOf z = 2 ∧ ∀ x ∈ (P : Subgroup G), x * z = z * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  have : Nontrivial (Subgroup.center (P : Subgroup G)) := hPp.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center (P : Subgroup G)) := hPp.to_subgroup _
  have h2 : 2 ∣ Nat.card (Subgroup.center (P : Subgroup G)) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card (α := Subgroup.center (P : Subgroup G))).ne'
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hx' : orderOf ((x : (P : Subgroup G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  refine ⟨((x : (P : Subgroup G)) : G), (x : (P : Subgroup G)).2, hx', fun y hy => ?_⟩
  have := Subgroup.mem_center_iff.mp x.2 ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem card_eq_of_sylow_le_of_isPGroup [Finite G] (P : Sylow 2 G) {C : Subgroup G}
    (hPC : (P : Subgroup G) ≤ C) (hC : IsPGroup 2 C) : Nat.card C = Nat.card P := by
  obtain ⟨Q, hCQ⟩ := hC.exists_le_sylow
  have h1 : Nat.card C ≤ Nat.card Q := Subgroup.card_le_of_le hCQ
  have h2 : Nat.card Q = Nat.card P := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card P ≤ Nat.card C := Subgroup.card_le_of_le hPC
  omega

theorem natCard_centralizer_singleton_mulEquiv {H : Type*} [Group H] (φ : G ≃* H) (z : G) :
    Nat.card (Subgroup.centralizer {φ z} : Subgroup H) =
      Nat.card (Subgroup.centralizer {z} : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨φ.symm x, ?_⟩
      invFun := fun y => ⟨φ y, ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  · have hx := x.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply φ.injective
    simpa using hx
  · have hy := y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]

theorem exists_comm_subgroup_of_mulEquiv {H : Type*} [Group H] (φ : G ≃* H) (z : G)
    {T : Subgroup H} (hTC : T ≤ Subgroup.centralizer {φ z})
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hcard : Nat.card (Subgroup.centralizer {φ z} : Subgroup H) = 2 * Nat.card T) :
    ∃ A : Subgroup G, A ≤ Subgroup.centralizer {z} ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      Nat.card A = Nat.card T ∧
      Nat.card (Subgroup.centralizer {z} : Subgroup G) = 2 * Nat.card A := by
  refine ⟨T.map φ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hTC ht)
    apply φ.injective
    simpa using h
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hcomm s hs t ht]
  · exact Subgroup.card_map_of_injective φ.symm.injective
  · rw [← natCard_centralizer_singleton_mulEquiv φ z, hcard,
      Subgroup.card_map_of_injective φ.symm.injective]

end CFSG.QuasithinUnique.I43Dihedral
