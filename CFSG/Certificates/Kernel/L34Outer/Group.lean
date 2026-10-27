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
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.L34Outer

variable {G : Type*} [Group G]

theorem cover_of {H : Subgroup G} {C A : Set G} (h1 : (1 : G) ∈ C)
    (hA : ∀ a ∈ A, (a ∈ H ∧ ∀ c ∈ C, c⁻¹ * a * c ∈ H) ∨ (∀ c ∈ C, a * c ∈ C ∧ a⁻¹ * c ∈ C)) :
    ∀ x ∈ Subgroup.closure A, ∃ c ∈ C, c⁻¹ * x ∈ H := by
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨1, h1, by simp⟩
  | mul_left a ha y _ ih =>
    obtain ⟨c, hc, hy⟩ := ih
    rcases hA a ha with ⟨-, hconj⟩ | hmove
    · refine ⟨c, hc, ?_⟩
      have := H.mul_mem (hconj c hc) hy
      simpa [mul_assoc] using this
    · exact ⟨a * c, (hmove c hc).1, by simpa [mul_assoc] using hy⟩
  | inv_mul_cancel a ha y _ ih =>
    obtain ⟨c, hc, hy⟩ := ih
    rcases hA a ha with ⟨-, hconj⟩ | hmove
    · refine ⟨c, hc, ?_⟩
      have := H.mul_mem (H.inv_mem (hconj c hc)) hy
      simpa [mul_assoc] using this
    · exact ⟨a⁻¹ * c, (hmove c hc).2, by simpa [mul_assoc] using hy⟩

theorem card_le_of_cover [Finite G] {H K : Subgroup G} {C : Set G}
    (h : ∀ x ∈ K, ∃ c ∈ C, c⁻¹ * x ∈ H) : Nat.card K ≤ Nat.card C * Nat.card H := by
  choose f hf using h
  let φ : K → C × H := fun x =>
    (⟨f x.1 x.2, (hf x.1 x.2).1⟩, ⟨(f x.1 x.2)⁻¹ * x.1, (hf x.1 x.2).2⟩)
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨e1, e2⟩ := hxy
    rw [e1] at e2
    exact Subtype.ext (mul_left_cancel e2)
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective φ hφ

theorem mem_of_pow_three [Finite G] {T R : Subgroup G} (hTR : T ≤ R)
    (hN : ∀ r ∈ R, ∀ t ∈ T, r * t * r⁻¹ ∈ T) (hcard : Nat.card R = 4 * Nat.card T) {r : G}
    (hr : r ∈ R) (h3 : r ^ 3 = 1) : r ∈ T := by
  have hn : (T.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN g.1 g.2 n.1 hn⟩
  have hcT : Nat.card (T.subgroupOf R) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv
  have hidx : (T.subgroupOf R).index = 4 := by
    have e := Subgroup.card_mul_index (T.subgroupOf R)
    rw [hcT, hcard] at e
    have hpos : 0 < Nat.card T := Nat.card_pos
    nlinarith
  have hm := Subgroup.pow_index_mem (T.subgroupOf R) (⟨r, hr⟩ : R)
  rw [hidx, Subgroup.mem_subgroupOf] at hm
  have e : r ^ 4 = r := by rw [pow_succ, h3, one_mul]
  simpa [e] using hm

theorem eq_of_card_nine [Finite G] {P H : Subgroup G} {Es : List (Subgroup G)} {z : G}
    (hP : Nat.card P = 27) (hE : ∀ E ∈ Es, E ≤ P ∧ Nat.card E = 9)
    (hcov : ∀ g ∈ P, ∃ E ∈ Es, g ∈ E)
    (hZ : ∀ g ∈ P, (∀ p ∈ P, g * p = p * g) → g = 1 ∨ g = z ∨ g = z * z)
    (hHP : H ≤ P) (hH : Nat.card H = 9) : ∃ E ∈ Es, H = E := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ H, ¬(h = 1 ∨ h = z ∨ h = z * z) := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : (H : Set G) ⊆ {1, z, z * z} := fun x hx => by
      rcases hcon x hx with rfl | rfl | rfl <;> simp
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z, z * z} : Set G).ncard ≤ 3 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      have := Set.ncard_insert_le z {z * z}
      rw [Set.ncard_singleton] at this
      omega
    have h3 : Nat.card H = (H : Set G).ncard := Nat.card_coe_set_eq (H : Set G)
    omega
  obtain ⟨E, hEm, hhE⟩ := hcov h (hHP hh)
  obtain ⟨hEP, hEc⟩ := hE E hEm
  have hcH := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := H) (by rw [hH]; norm_num)
  have hcE := IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (G := E) (by rw [hEc]; norm_num)
  have hHc : H ≤ Subgroup.centralizer {h} := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcH ⟨x, hx⟩ ⟨h, hh⟩)
  have hEc' : E ≤ Subgroup.centralizer {h} := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcE ⟨x, hx⟩ ⟨h, hhE⟩)
  have hKP : H ⊔ E ≤ P := sup_le hHP hEP
  have hKc : H ⊔ E ≤ Subgroup.centralizer {h} := sup_le hHc hEc'
  have hd1 : Nat.card (H ⊔ E : Subgroup G) ∣ 27 := hP ▸ Subgroup.card_dvd_of_le hKP
  have hd2 : 9 ∣ Nat.card (H ⊔ E : Subgroup G) := hH ▸ Subgroup.card_dvd_of_le le_sup_left
  have hK : Nat.card (H ⊔ E : Subgroup G) = 9 ∨ Nat.card (H ⊔ E : Subgroup G) = 27 := by
    have hle := Nat.le_of_dvd (by norm_num) hd1
    generalize Nat.card (H ⊔ E : Subgroup G) = k at hd1 hd2 hle ⊢
    interval_cases k <;> omega
  rcases hK with hK | hK
  · have hHK : H = H ⊔ E := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hK, hH])
    refine ⟨E, hEm, ?_⟩
    have hEH : E ≤ H := hHK ▸ le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge hEH (by rw [hH, hEc])).symm
  · exfalso
    have hKe : H ⊔ E = P := Subgroup.eq_of_le_of_card_ge hKP (by rw [hK, hP])
    apply hne
    refine hZ h (hHP hh) fun p hp => ?_
    have := hKc (hKe ▸ hp)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm

end CFSG.KS.L34Outer

end
