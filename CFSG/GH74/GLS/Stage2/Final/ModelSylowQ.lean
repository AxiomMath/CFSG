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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.GH74.GLS.Stage2.Final.ModelSylowQ

open Subgroup

theorem card_zpowers_two_pow {X : Type*} [Group X] {a : X} (ha : ∃ i : ℕ, a ^ 2 ^ i = 1) :
    ∃ j : ℕ, Nat.card ↥(zpowers a) = 2 ^ j := by
  obtain ⟨i, hi⟩ := ha
  have h1 : orderOf a ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hi
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨j, by rw [Nat.card_zpowers]; exact hj⟩

theorem isPGroup_sup_zpowers {X : Type*} [Group X] {a b : X} (hab : Commute a b)
    (ha : ∃ i : ℕ, a ^ 2 ^ i = 1) (hb : ∃ i : ℕ, b ^ 2 ^ i = 1) :
    IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := by
  obtain ⟨j₁, hj₁⟩ := card_zpowers_two_pow ha
  obtain ⟨j₂, hj₂⟩ := card_zpowers_two_pow hb
  let φ : ↥(zpowers a) × ↥(zpowers b) →* X :=
    (zpowers a).subtype.noncommCoprod (zpowers b).subtype (fun x y => by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
      show Commute (x : X) (y : X)
      rw [← hm, ← hn]
      exact hab.zpow_zpow m n)
  have hrange : φ.range = zpowers a ⊔ zpowers b := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hP : IsPGroup 2 (↥(zpowers a) × ↥(zpowers b)) := by
    apply IsPGroup.of_card (n := j₁ + j₂)
    rw [Nat.card_prod, hj₁, hj₂, pow_add]
  have h2 : IsPGroup 2 ↥φ.range :=
    hP.of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
  rw [← hrange]
  exact h2

theorem card_subgroupOf_eq_inf {X : Type*} [Group X] (S E : Subgroup X) :
    Nat.card ↥(E.subgroupOf S) = Nat.card ↥(S ⊓ E : Subgroup X) := by
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype E S]
  exact (Subgroup.card_map_of_injective S.subtype_injective).symm

theorem card_dvd_four {Y : Type*} [Group Y] [Finite Y] (T : Subgroup Y) (hT : IsPGroup 2 T) {o : ℕ}
    (ho : Odd o) (hdvd : Nat.card T ∣ 4 * o) : Nat.card T ∣ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hT
  rw [hm] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ m) o := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 ho)
  exact hcop.dvd_of_dvd_mul_right hdvd


theorem exists_sylow_quot4 {X : Type*} [Group X] [Finite X] (E : Subgroup X) [E.Normal] {o : ℕ}
    (ho : Odd o) (hidx : E.index = 4 * o) {a b : X} {W : Subgroup X} (hW : IsPGroup 2 W)
    (haW : a ∈ W) (hbW : b ∈ W)
    (ha2 : a * a ∈ E) (haE : a ∉ E) (hbE : b ∉ E) (habE : a * b ∉ E) :
    ∃ S : Sylow 2 X, a ∈ (S : Subgroup X) ∧ b ∈ (S : Subgroup X) ∧
      Nat.card (S : Subgroup X) = 4 * Nat.card ↥((S : Subgroup X) ⊓ E) ∧
      ∀ s ∈ (S : Subgroup X), ∃ k ∈ (S : Subgroup X) ⊓ E,
        s = k ∨ s = k * a ∨ s = k * b ∨ s = k * (a * b) := by
  classical
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  have haS : a ∈ (S : Subgroup X) := hS haW
  have hbS : b ∈ (S : Subgroup X) := hS hbW
  refine ⟨S, haS, hbS, ?_⟩
  set π : X →* X ⧸ E := QuotientGroup.mk' E with hπ
  let f : ↥(S : Subgroup X) →* X ⧸ E := π.comp (S : Subgroup X).subtype
  have hker : f.ker = E.subgroupOf (S : Subgroup X) := by
    ext s
    simp [f, hπ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hRp : IsPGroup 2 ↥f.range :=
    (S.isPGroup').of_surjective f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
  have hmemR : ∀ x ∈ (S : Subgroup X), π x ∈ f.range := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hne1 : π a ≠ 1 := fun h => haE ((QuotientGroup.eq_one_iff a).1 h)
  have hne2 : π b ≠ 1 := fun h => hbE ((QuotientGroup.eq_one_iff b).1 h)
  have hne3 : π (a * b) ≠ 1 := fun h => habE ((QuotientGroup.eq_one_iff _).1 h)
  have hne4 : π a ≠ π b := by
    intro h
    apply habE
    have h' : a⁻¹ * b ∈ E := QuotientGroup.eq.1 h
    have : a * b = a * a * (a⁻¹ * b) := by group
    rw [this]
    exact E.mul_mem ha2 h'
  have hne5 : π (a * b) ≠ π a := by
    intro h
    apply hbE
    have h' : a⁻¹ * (a * b) ∈ E := QuotientGroup.eq.1 h.symm
    simpa using h'
  have hne6 : π (a * b) ≠ π b := by
    intro h
    apply haE
    have h' : b⁻¹ * (a * b) ∈ E := QuotientGroup.eq.1 h.symm
    have hn : E.Normal := inferInstance
    have := hn.conj_mem _ h' b
    simpa [mul_assoc] using this
  let T : Finset (X ⧸ E) := {1, π a, π b, π (a * b)}
  have hTcard : T.card = 4 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hne6.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne4, hne5.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne1.symm, hne2.symm, hne3.symm⟩
  have hTsub : (T : Set (X ⧸ E)) ⊆ (f.range : Set (X ⧸ E)) := by
    intro x hx
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact f.range.one_mem
    · exact hmemR a haS
    · exact hmemR b hbS
    · exact hmemR (a * b) ((S : Subgroup X).mul_mem haS hbS)
  have hge : 4 ≤ Nat.card f.range := by
    have h1 : (T : Set (X ⧸ E)).ncard ≤ (f.range : Set (X ⧸ E)).ncard :=
      Set.ncard_le_ncard hTsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hTcard] at h1
    rwa [← Nat.card_coe_set_eq] at h1
  have hdvd : Nat.card f.range ∣ 4 * o := by
    have h1 : Nat.card f.range ∣ Nat.card (X ⧸ E) := Subgroup.card_subgroup_dvd_card f.range
    rwa [← Subgroup.index_eq_card, hidx] at h1
  have hle : Nat.card f.range ∣ 4 := card_dvd_four f.range hRp ho hdvd
  have hR4 : Nat.card f.range = 4 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hle) hge
  have hTeq : (T : Set (X ⧸ E)) = (f.range : Set (X ⧸ E)) := by
    apply Set.eq_of_subset_of_ncard_le hTsub _ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq]
    exact hR4.le
  constructor
  · have h1 := Subgroup.card_ker_mul_card_range f
    rw [hR4, hker, card_subgroupOf_eq_inf] at h1
    rw [← h1]
    ring
  · intro s hs
    have hsr : π s ∈ (f.range : Set (X ⧸ E)) := hmemR s hs
    rw [← hTeq] at hsr
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hsr
    have key : ∀ x ∈ (S : Subgroup X), π s = π x → ∃ k ∈ (S : Subgroup X) ⊓ E, s = k * x := by
      intro x hx hsx
      have h' : x⁻¹ * s ∈ E := QuotientGroup.eq.1 hsx.symm
      have h'' : s * x⁻¹ ∈ E := by
        have hn : (E).Normal := inferInstance
        have := hn.conj_mem _ h' x
        simpa [mul_assoc] using this
      refine ⟨s * x⁻¹, ⟨(S : Subgroup X).mul_mem hs ((S : Subgroup X).inv_mem hx), h''⟩, ?_⟩
      group
    rcases hsr with h | h | h | h
    · obtain ⟨k, hk, hs'⟩ := key 1 (Subgroup.one_mem _) (by rw [h, map_one])
      exact ⟨k, hk, Or.inl (by rw [hs', mul_one])⟩
    · obtain ⟨k, hk, hs'⟩ := key a haS h
      exact ⟨k, hk, Or.inr (Or.inl hs')⟩
    · obtain ⟨k, hk, hs'⟩ := key b hbS h
      exact ⟨k, hk, Or.inr (Or.inr (Or.inl hs'))⟩
    · obtain ⟨k, hk, hs'⟩ := key (a * b) ((S : Subgroup X).mul_mem haS hbS) h
      exact ⟨k, hk, Or.inr (Or.inr (Or.inr hs'))⟩

theorem exists_sylow_quot2 {X : Type*} [Group X] [Finite X] (E : Subgroup X) [E.Normal] {o : ℕ}
    (ho : Odd o) (hidx : E.index = 2 * o) {a : X} {W : Subgroup X} (hW : IsPGroup 2 W)
    (haW : a ∈ W) (haE : a ∉ E) :
    ∃ S : Sylow 2 X, a ∈ (S : Subgroup X) ∧ W ≤ (S : Subgroup X) ∧
      Nat.card (S : Subgroup X) = 2 * Nat.card ↥((S : Subgroup X) ⊓ E) ∧
      ∀ s ∈ (S : Subgroup X), ∃ k ∈ (S : Subgroup X) ⊓ E, s = k ∨ s = k * a := by
  classical
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  have haS : a ∈ (S : Subgroup X) := hS haW
  refine ⟨S, haS, hS, ?_⟩
  set π : X →* X ⧸ E := QuotientGroup.mk' E with hπ
  let f : ↥(S : Subgroup X) →* X ⧸ E := π.comp (S : Subgroup X).subtype
  have hker : f.ker = E.subgroupOf (S : Subgroup X) := by
    ext s
    simp [f, hπ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hRp : IsPGroup 2 ↥f.range :=
    (S.isPGroup').of_surjective f.rangeRestrict (MonoidHom.rangeRestrict_surjective f)
  have hmemR : ∀ x ∈ (S : Subgroup X), π x ∈ f.range := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hne1 : π a ≠ 1 := fun h => haE ((QuotientGroup.eq_one_iff a).1 h)
  let T : Finset (X ⧸ E) := {1, π a}
  have hTcard : T.card = 2 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa using hne1.symm
  have hTsub : (T : Set (X ⧸ E)) ⊆ (f.range : Set (X ⧸ E)) := by
    intro x hx
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact f.range.one_mem
    · exact hmemR a haS
  have hge : 2 ≤ Nat.card f.range := by
    have h1 : (T : Set (X ⧸ E)).ncard ≤ (f.range : Set (X ⧸ E)).ncard :=
      Set.ncard_le_ncard hTsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hTcard] at h1
    rwa [← Nat.card_coe_set_eq] at h1
  have hdvd : Nat.card f.range ∣ 2 * o := by
    have h1 : Nat.card f.range ∣ Nat.card (X ⧸ E) := Subgroup.card_subgroup_dvd_card f.range
    rwa [← Subgroup.index_eq_card, hidx] at h1
  have hle : Nat.card f.range ∣ 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hRp
    rw [hm] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ m) o := Nat.Coprime.pow_left m (Nat.coprime_two_left.2 ho)
    exact hcop.dvd_of_dvd_mul_right hdvd
  have hR2 : Nat.card f.range = 2 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) hle) hge
  have hTeq : (T : Set (X ⧸ E)) = (f.range : Set (X ⧸ E)) := by
    apply Set.eq_of_subset_of_ncard_le hTsub _ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hTcard, ← Nat.card_coe_set_eq]
    exact hR2.le
  constructor
  · have h1 := Subgroup.card_ker_mul_card_range f
    rw [hR2, hker, card_subgroupOf_eq_inf] at h1
    rw [← h1]
    ring
  · intro s hs
    have hsr : π s ∈ (f.range : Set (X ⧸ E)) := hmemR s hs
    rw [← hTeq] at hsr
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hsr
    have key : ∀ x ∈ (S : Subgroup X), π s = π x → ∃ k ∈ (S : Subgroup X) ⊓ E, s = k * x := by
      intro x hx hsx
      have h' : x⁻¹ * s ∈ E := QuotientGroup.eq.1 hsx.symm
      have h'' : s * x⁻¹ ∈ E := by
        have hn : (E).Normal := inferInstance
        have := hn.conj_mem _ h' x
        simpa [mul_assoc] using this
      refine ⟨s * x⁻¹, ⟨(S : Subgroup X).mul_mem hs ((S : Subgroup X).inv_mem hx), h''⟩, ?_⟩
      group
    rcases hsr with h | h
    · obtain ⟨k, hk, hs'⟩ := key 1 (Subgroup.one_mem _) (by rw [h, map_one])
      exact ⟨k, hk, Or.inl (by rw [hs', mul_one])⟩
    · obtain ⟨k, hk, hs'⟩ := key a haS h
      exact ⟨k, hk, Or.inr hs'⟩

end CFSG.GH74.GLS.Stage2.Final.ModelSylowQ
