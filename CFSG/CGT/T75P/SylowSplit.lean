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

namespace CFSG.CGT.T75P

open scoped Pointwise

variable {G : Type*} [Group G]

theorem card_sup_of_commute {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hA : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm
  have hmul : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B
      (hA.trans (Subgroup.centralizer_le_normalizer _))
  let f : A × B → ↥(A ⊔ B) := fun p => ⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
      have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
          _ = b' * (b : G)⁻¹ := by group
      have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem a'.2) a.2, by
        rw [h2]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have hab : a = a' := Subtype.ext (inv_mul_eq_one.1 h3).symm
      have h4 : (b' : G) * (b : G)⁻¹ = 1 := by rw [← h2, h3]
      have hbb : b = b' := Subtype.ext (mul_inv_eq_one.1 h4).symm
      rw [hab, hbb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by rw [← hmul]; exact hx
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm, Nat.card_prod]

theorem exists_sylow_of_prod [Finite G] {H C A B : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ c ∈ C, h * c = c * h) (hinf : H ⊓ C = ⊥)
    (hodd : ¬ 2 ∣ (H ⊔ C).index) (hAH : A ≤ H) (hBC : B ≤ C) (hA2 : IsPGroup 2 A)
    (hAodd : ¬ 2 ∣ (A.subgroupOf H).index) (hB2 : IsPGroup 2 B)
    (hBodd : ¬ 2 ∣ (B.subgroupOf C).index) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = A ⊔ B := by
  have hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb => hcomm a (hAH ha) b (hBC hb)
  have hiAB : A ⊓ B = ⊥ := eq_bot_iff.2 (hinf ▸ inf_le_inf hAH hBC)
  have hcard : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B :=
    card_sup_of_commute hcAB hiAB
  have hcardN : Nat.card (H ⊔ C : Subgroup G) = Nat.card H * Nat.card C :=
    card_sup_of_commute hcomm hinf
  have hP2 : IsPGroup 2 (A ⊔ B : Subgroup G) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hA2
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hB2
    exact (IsPGroup.iff_card).2 ⟨a + b, by rw [hcard, ha, hb, pow_add]⟩
  have hHA : Nat.card H = Nat.card A * (A.subgroupOf H).index := by
    have := Subgroup.card_mul_index (A.subgroupOf H)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv] at this
    exact this.symm
  have hCB : Nat.card C = Nat.card B * (B.subgroupOf C).index := by
    have := Subgroup.card_mul_index (B.subgroupOf C)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv] at this
    exact this.symm
  have hG1 := Subgroup.card_mul_index (A ⊔ B : Subgroup G)
  have hG2 := Subgroup.card_mul_index (H ⊔ C : Subgroup G)
  have hpos : 0 < Nat.card (A ⊔ B : Subgroup G) := Nat.card_pos
  have hidx : (A ⊔ B : Subgroup G).index =
      ((A.subgroupOf H).index * (B.subgroupOf C).index) * (H ⊔ C).index := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hG1, ← hG2, hcardN, hHA, hCB, hcard]
    ring
  have hodd' : ¬ 2 ∣ (A ⊔ B : Subgroup G).index := by
    rw [hidx]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
      · exact hAodd h
      · exact hBodd h
    · exact hodd h
  exact ⟨hP2.toSylow hodd', rfl⟩

end CFSG.CGT.T75P
