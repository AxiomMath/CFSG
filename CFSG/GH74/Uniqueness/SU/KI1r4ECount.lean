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

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup

theorem index_ge_four_of_nonabelian {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hN : N ≤ center G) (a b : G) (hab : a * b ≠ b * a) : 4 ≤ N.index := by
  by_contra hlt
  push Not at hlt
  have hnorm : N.Normal := Subgroup.normal_of_le_center hN
  have hcyc : IsCyclic (G ⧸ N) := by
    have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    have hidx : Nat.card (G ⧸ N) = N.index := rfl
    have hc : Nat.card (G ⧸ N) = 1 ∨ Nat.card (G ⧸ N) = 2 ∨ Nat.card (G ⧸ N) = 3 := by omega
    rcases hc with h1 | h2 | h3
    · have : Subsingleton (G ⧸ N) := (Nat.card_eq_one_iff_unique.mp h1).1
      infer_instance
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card h2
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card h3
  have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [QuotientGroup.ker_mk']; exact hN)
  exact hab (hcomm.is_comm.comm a b)

theorem exists_pow_orderOf_eq_two {G : Type*} [Group G] {z : G} (hz1 : z ≠ 1)
    (hn : ∃ n : ℕ, z ^ 2 ^ n = 1) : ∃ j : ℕ, orderOf (z ^ j) = 2 := by
  obtain ⟨n, hn'⟩ := hn
  have hord : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hz1' : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have hj1 : j ≠ 0 := by
    rintro rfl
    exact hz1' (by simpa using hj)
  have hord0 : orderOf z ≠ 0 := by rw [hj]; positivity
  have h2dvd : 2 ∣ orderOf z := by rw [hj]; exact dvd_pow_self 2 hj1
  exact ⟨orderOf z / 2, orderOf_pow_orderOf_div hord0 h2dvd⟩

theorem eq_of_two_distinct_involutions {G : Type*} [Group G] [Finite G] {A Z : Subgroup G}
    (hZA : Z ≤ A) (hA4 : Nat.card A = 4) {z w : G} (hz : z ∈ Z) (hw : w ∈ Z) (hz1 : z ≠ 1)
    (hw1 : w ≠ 1) (hwz : w ≠ z) (hz2 : z * z = 1) : Z = A := by
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzc : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  have hzZ : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hz
  obtain ⟨k, hk⟩ : ∃ k, Nat.card Z = Nat.card (Subgroup.zpowers z) * k :=
    Subgroup.card_dvd_of_le hzZ
  rw [hzc] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Nat.card_pos (α := Z)).ne' (by rw [hk])
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hzZ' : Subgroup.zpowers z = Z :=
      Subgroup.eq_of_le_of_card_ge hzZ (le_of_eq (by rw [hk, hzc]))
    have hwz' : w ∈ Subgroup.zpowers z := hzZ' ▸ hw
    have hsq : ∀ c ∈ Subgroup.zpowers z, c = 1 ∨ c = z := by
      intro c hc
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
      · left
        rw [zpow_mul, zpow_two, hz2, one_zpow]
      · right
        rw [zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]
    rcases hsq w hwz' with h | h
    · exact hw1 h
    · exact hwz h
  have hZ4 : 4 ≤ Nat.card Z := by omega
  exact Subgroup.eq_of_le_of_card_ge hZA (by rw [hA4]; exact hZ4) ▸ rfl

theorem card_ge_of_three_commuting {H : Type*} [Group H] [Finite H] (R A S₁ S₂ S₃ : Subgroup H)
    (hS₁R : S₁ ≤ R) (hS₂R : S₂ ≤ R) (hS₃R : S₃ ≤ R)
    (hAR : A ≤ R) (hAc : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a)
    (h12 : ∀ s ∈ S₁, ∀ t ∈ S₂, s * t = t * s) (h13 : ∀ s ∈ S₁, ∀ t ∈ S₃, s * t = t * s)
    (h23 : ∀ s ∈ S₂, ∀ t ∈ S₃, s * t = t * s)
    (hn₁ : ∃ a ∈ S₁, ∃ b ∈ S₁, a * b ≠ b * a) (hn₂ : ∃ a ∈ S₂, ∃ b ∈ S₂, a * b ≠ b * a)
    (hn₃ : ∃ a ∈ S₃, ∃ b ∈ S₃, a * b ≠ b * a)
    (hi₁ : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, ∀ s₃ ∈ S₃, s₁ * s₂ * s₃ ∈ A → s₁ ∈ A)
    (hi₂ : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, ∀ s₃ ∈ S₃, s₁ * s₂ * s₃ ∈ A → s₂ ∈ A)
    (hi₃ : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, ∀ s₃ ∈ S₃, s₁ * s₂ * s₃ ∈ A → s₃ ∈ A) :
    64 * Nat.card A ≤ Nat.card R := by
  classical
  have key : ∀ S : Subgroup H, S ≤ R → (∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) →
      4 * Nat.card (A.subgroupOf S) ≤ Nat.card S := by
    intro S hSR ⟨a, ha, b, hb, hab⟩
    have hc : A.subgroupOf S ≤ center ↥S := by
      intro s hs
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hs) _ (hSR g.2)).symm
    have h4 := index_ge_four_of_nonabelian (A.subgroupOf S) hc ⟨a, ha⟩ ⟨b, hb⟩
      (fun h => hab (congrArg Subtype.val h))
    have := (A.subgroupOf S).card_mul_index
    nlinarith
  have k₁ := key S₁ hS₁R hn₁
  have k₂ := key S₂ hS₂R hn₂
  have k₃ := key S₃ hS₃R hn₃
  let G : ↥S₁ × ↥S₂ × ↥S₃ →* ↥R :=
    MonoidHom.mk' (fun s => ⟨(s.1 : H) * s.2.1 * s.2.2, R.mul_mem (R.mul_mem (hS₁R s.1.2)
      (hS₂R s.2.1.2)) (hS₃R s.2.2.2)⟩) (by
      intro s t
      apply Subtype.ext
      show ((s.1 * t.1 : ↥S₁) : H) * ((s.2.1 * t.2.1 : ↥S₂) : H) * ((s.2.2 * t.2.2 : ↥S₃) : H) =
        (s.1 : H) * s.2.1 * s.2.2 * ((t.1 : H) * t.2.1 * t.2.2)
      simp only [Subgroup.coe_mul]
      have c1 : (t.1 : H) * (s.2.1 : H) = (s.2.1 : H) * t.1 := (h12 _ t.1.2 _ s.2.1.2)
      have c2 : (t.1 : H) * (s.2.2 : H) = (s.2.2 : H) * t.1 := (h13 _ t.1.2 _ s.2.2.2)
      have c3 : (t.2.1 : H) * (s.2.2 : H) = (s.2.2 : H) * t.2.1 := (h23 _ t.2.1.2 _ s.2.2.2)
      calc (s.1 : H) * t.1 * ((s.2.1 : H) * t.2.1) * ((s.2.2 : H) * t.2.2)
          = (s.1 : H) * (t.1 * (s.2.1 : H)) * t.2.1 * ((s.2.2 : H) * t.2.2) := by group
        _ = (s.1 : H) * ((s.2.1 : H) * t.1) * t.2.1 * ((s.2.2 : H) * t.2.2) := by rw [c1]
        _ = (s.1 : H) * (s.2.1 : H) * (t.1 * t.2.1 * ((s.2.2 : H) * t.2.2)) := by group
        _ = (s.1 : H) * (s.2.1 : H) * (t.1 * (t.2.1 * (s.2.2 : H)) * t.2.2) := by group
        _ = (s.1 : H) * (s.2.1 : H) * (t.1 * ((s.2.2 : H) * t.2.1) * t.2.2) := by rw [c3]
        _ = (s.1 : H) * (s.2.1 : H) * ((t.1 * (s.2.2 : H)) * t.2.1 * t.2.2) := by group
        _ = (s.1 : H) * (s.2.1 : H) * (((s.2.2 : H) * t.1) * t.2.1 * t.2.2) := by rw [c2]
        _ = (s.1 : H) * s.2.1 * s.2.2 * ((t.1 : H) * t.2.1 * t.2.2) := by group)
  set AR : Subgroup ↥R := A.subgroupOf R with hAR_def
  have hARc : AR ≤ center ↥R := fun r hr => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.mp hr) _ g.2).symm
  have hARn : AR.Normal := Subgroup.normal_of_le_center hARc
  let F : ↥S₁ × ↥S₂ × ↥S₃ →* ↥R ⧸ AR := (QuotientGroup.mk' AR).comp G
  have hker : ∀ s ∈ F.ker, (s.1 : H) ∈ A ∧ (s.2.1 : H) ∈ A ∧ (s.2.2 : H) ∈ A := by
    intro s hs
    have h1 : G s ∈ AR := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hs)
    have h2 : (s.1 : H) * s.2.1 * s.2.2 ∈ A := Subgroup.mem_subgroupOf.mp h1
    exact ⟨hi₁ _ s.1.2 _ s.2.1.2 _ s.2.2.2 h2, hi₂ _ s.1.2 _ s.2.1.2 _ s.2.2.2 h2,
      hi₃ _ s.1.2 _ s.2.1.2 _ s.2.2.2 h2⟩
  have hkercard : Nat.card F.ker ≤
      Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) * Nat.card (A.subgroupOf S₃) := by
    let φ : F.ker → ↥(A.subgroupOf S₁) × ↥(A.subgroupOf S₂) × ↥(A.subgroupOf S₃) := fun s =>
      (⟨s.1.1, Subgroup.mem_subgroupOf.mpr (hker s.1 s.2).1⟩,
        ⟨s.1.2.1, Subgroup.mem_subgroupOf.mpr (hker s.1 s.2).2.1⟩,
        ⟨s.1.2.2, Subgroup.mem_subgroupOf.mpr (hker s.1 s.2).2.2⟩)
    have hinj : Function.Injective φ := by
      intro s t hst
      have h1 := congrArg (fun p => ((p.1 : ↥S₁))) hst
      have h2 := congrArg (fun p => ((p.2.1 : ↥S₂))) hst
      have h3 := congrArg (fun p => ((p.2.2 : ↥S₃))) hst
      exact Subtype.ext (Prod.ext (Subtype.ext (congrArg Subtype.val h1))
        (Prod.ext (Subtype.ext (congrArg Subtype.val h2)) (Subtype.ext (congrArg Subtype.val h3))))
    have := Nat.card_le_card_of_injective φ hinj
    simpa [Nat.card_prod, mul_assoc] using this
  have hrange : Nat.card F.range ≤ AR.index :=
    Nat.card_le_card_of_injective (Subtype.val : F.range → ↥R ⧸ AR) Subtype.val_injective
  have hcardprod : Nat.card S₁ * (Nat.card S₂ * Nat.card S₃) =
      Nat.card F.ker * Nat.card F.range := by
    have := Subgroup.card_ker_mul_card_range F
    simpa [Nat.card_prod] using this.symm
  have hARcard : Nat.card AR = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv
  have hRidx := AR.card_mul_index
  have hposN : 0 < Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) *
      Nat.card (A.subgroupOf S₃) := by
    have a1 : 0 < Nat.card (A.subgroupOf S₁) := Nat.card_pos
    have a2 : 0 < Nat.card (A.subgroupOf S₂) := Nat.card_pos
    have a3 : 0 < Nat.card (A.subgroupOf S₃) := Nat.card_pos
    positivity
  have h1 : 64 * (Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) *
      Nat.card (A.subgroupOf S₃)) ≤ Nat.card S₁ * (Nat.card S₂ * Nat.card S₃) := by
    calc 64 * (Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) *
        Nat.card (A.subgroupOf S₃))
        = (4 * Nat.card (A.subgroupOf S₁)) * ((4 * Nat.card (A.subgroupOf S₂)) *
          (4 * Nat.card (A.subgroupOf S₃))) := by ring
      _ ≤ Nat.card S₁ * (Nat.card S₂ * Nat.card S₃) :=
        Nat.mul_le_mul k₁ (Nat.mul_le_mul k₂ k₃)
  have h3 : Nat.card F.ker * Nat.card F.range ≤ (Nat.card (A.subgroupOf S₁) *
      Nat.card (A.subgroupOf S₂) * Nat.card (A.subgroupOf S₃)) * AR.index :=
    Nat.mul_le_mul hkercard hrange
  have h4 : 64 ≤ AR.index := by
    have : (Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) *
        Nat.card (A.subgroupOf S₃)) * 64 ≤
        (Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) *
        Nat.card (A.subgroupOf S₃)) * AR.index := by
      calc _ = 64 * (Nat.card (A.subgroupOf S₁) * Nat.card (A.subgroupOf S₂) *
            Nat.card (A.subgroupOf S₃)) := by ring
        _ ≤ Nat.card S₁ * (Nat.card S₂ * Nat.card S₃) := h1
        _ = Nat.card F.ker * Nat.card F.range := hcardprod
        _ ≤ _ := h3
    exact Nat.le_of_mul_le_mul_left this hposN
  calc 64 * Nat.card A = Nat.card AR * 64 := by rw [hARcard]; ring
    _ ≤ Nat.card AR * AR.index := Nat.mul_le_mul_left _ h4
    _ = Nat.card R := hRidx

end CFSG.GH74.Uniqueness.SU.K.R4
