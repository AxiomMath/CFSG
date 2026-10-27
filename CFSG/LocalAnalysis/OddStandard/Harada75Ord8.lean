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
public import Mathlib.GroupTheory.Commutator.Finite
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

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

private theorem ord8_inv_mul_mem {M : Type} [Group M] [Finite M] {H K : Subgroup M}
    (hHK : H ≤ K) (hcard : Nat.card K = 2 * Nat.card H) {x y : M} (hx : x ∈ K) (hy : y ∈ K)
    (hxH : x ∉ H) (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_eq_left.mpr hHK, hcard] at h1
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h2 : H.relIndex K = 2 := by
    have : H.relIndex K * Nat.card H = 2 * Nat.card H := h1
    exact Nat.eq_of_mul_eq_mul_right hpos this
  obtain ⟨a, ha, hall⟩ := Subgroup.relIndex_eq_two_iff'.mp h2
  have hax : a * x ∈ H := by
    rcases hall x hx with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hxH
  have hay : a * y ∈ H := by
    rcases hall y hy with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hyH
  have := H.mul_mem (H.inv_mem hax) hay
  simpa [mul_assoc] using this

private theorem ord8_commutator_mem {M : Type} [Group M] [Finite M] {A Q : Subgroup M}
    (hAn : A.Normal) (hQn : Q.Normal) (hAQ : A ≤ Q) (hQ : Nat.card Q = 2 * Nat.card A) {p : M}
    (hp : p ∈ Q) (n : M) : p⁻¹ * (n⁻¹ * p * n) ∈ A := by
  have hq : n⁻¹ * p * n ∈ Q := by
    simpa using hQn.conj_mem p hp n⁻¹
  by_cases hpA : p ∈ A
  · have hqA : n⁻¹ * p * n ∈ A := by simpa using hAn.conj_mem p hpA n⁻¹
    exact A.mul_mem (A.inv_mem hpA) hqA
  · have hqA : n⁻¹ * p * n ∉ A := by
      intro h
      apply hpA
      have := hAn.conj_mem _ h n
      simpa [mul_assoc] using this
    exact ord8_inv_mul_mem hAQ hQ hp hq hpA hqA

private theorem ord8_card_center {G : Type} [Group G] [Finite G] (hG : Nat.card G = 8)
    (hnc : ∃ x y : G, x * y ≠ y * x) : Nat.card (Subgroup.center G) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 2) (n := 3)
    (by rw [hG]; norm_num) (by norm_num)
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
  rw [hG, hk] at hq
  have hqpos : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
  have hk3 : k ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    have h2 : 2 ^ k ≤ Nat.card (G ⧸ Subgroup.center G) * 2 ^ k := Nat.le_mul_of_pos_left _ hqpos
    omega
  by_contra hne
  have hqd : Nat.card (G ⧸ Subgroup.center G) ∣ 2 := by
    interval_cases k
    · exact absurd (by rw [hk]; norm_num) hne
    · have : Nat.card (G ⧸ Subgroup.center G) = 2 := by omega
      rw [this]
    · have : Nat.card (G ⧸ Subgroup.center G) = 1 := by omega
      rw [this]
      exact one_dvd 2
  have : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_card_dvd_prime hqd
  have := isMulCommutative_of_isCyclic_quotient_center_self G
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (isMulCommutative_iff.mp this x y)

private theorem ord8_eq_of_normal {M : Type} [Group M] [Finite M] {A P P' : Subgroup M}
    [hAn : A.Normal] [hPn : P.Normal] [hP'n : P'.Normal] (hM : Nat.card M = 64)
    (hA : Nat.card A = 8) (hnc : ∃ x y : M, ⁅x, y⁆ ∉ A) (hAP : A ≤ P) (hP : Nat.card P = 16)
    (hAP' : A ≤ P') (hP' : Nat.card P' = 16) : P = P' := by
  have hG : Nat.card (M ⧸ A) = 8 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup A
    rw [hM, hA] at this
    omega
  have hGnc : ∃ x y : M ⧸ A, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨(x : M ⧸ A), (y : M ⧸ A), fun h => hxy ?_⟩
    have h1 : ⁅x, y⁆ ∈ (QuotientGroup.mk' A).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h
    rwa [QuotientGroup.ker_mk'] at h1
  have hZ := ord8_card_center hG hGnc
  have hsurj := QuotientGroup.mk'_surjective A
  have hZc : Nat.card ((Subgroup.center (M ⧸ A)).comap (QuotientGroup.mk' A)) = 16 := by
    have h1 := Subgroup.card_mul_index (Subgroup.center (M ⧸ A))
    rw [hZ, hG] at h1
    have hidx : (Subgroup.center (M ⧸ A)).index = 4 := by omega
    have h2 := Subgroup.card_mul_index ((Subgroup.center (M ⧸ A)).comap (QuotientGroup.mk' A))
    rw [Subgroup.index_comap_of_surjective _ hsurj, hidx, hM] at h2
    omega
  have hle : ∀ Q : Subgroup M, Q.Normal → A ≤ Q → Nat.card Q = 16 →
      Q ≤ (Subgroup.center (M ⧸ A)).comap (QuotientGroup.mk' A) := by
    intro Q hQn hAQ hQ p hp
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨n, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr ?_
    have h1 := ord8_commutator_mem hAn hQn hAQ (by rw [hQ, hA]) hp n
    have e : (n * p)⁻¹ * (p * n) = p⁻¹ * (n⁻¹ * p * n) := by group
    rw [e]
    exact h1
  have h1 := Subgroup.eq_of_le_of_card_ge (hle P hPn hAP hP) (by omega)
  have h2 := Subgroup.eq_of_le_of_card_ge (hle P' hP'n hAP' hP') (by omega)
  exact h1.trans h2.symm

theorem eq_of_card_sixteen_of_nonabelian {S : Type} [Group S] [Finite S] {N A P P' : Subgroup S}
    (hN : Nat.card N = 64) (hA : Nat.card A = 8) (hAN : A ≤ N)
    (hAnorm : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A)
    (hnc : ∃ x ∈ N, ∃ y ∈ N, ⁅x, y⁆ ∉ A)
    (hAP : A ≤ P) (hPN : P ≤ N) (hPnorm : ∀ n ∈ N, ∀ p ∈ P, n * p * n⁻¹ ∈ P)
    (hP : Nat.card P = 16)
    (hAP' : A ≤ P') (hP'N : P' ≤ N) (hP'norm : ∀ n ∈ N, ∀ p ∈ P', n * p * n⁻¹ ∈ P')
    (hP' : Nat.card P' = 16) : P = P' := by
  have hAn : (A.subgroupOf N).Normal := ⟨fun a ha g => hAnorm g.1 g.2 a.1 ha⟩
  have hPn : (P.subgroupOf N).Normal := ⟨fun a ha g => hPnorm g.1 g.2 a.1 ha⟩
  have hP'n : (P'.subgroupOf N).Normal := ⟨fun a ha g => hP'norm g.1 g.2 a.1 ha⟩
  have hcard : ∀ {H : Subgroup S}, H ≤ N → Nat.card (H.subgroupOf N) = Nat.card H :=
    fun hH => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have key : P.subgroupOf N = P'.subgroupOf N :=
    ord8_eq_of_normal (M := N) hN (by rw [hcard hAN]; exact hA)
      (by
        obtain ⟨x, hx, y, hy, hxy⟩ := hnc
        exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩)
      (fun x hx => hAP hx) (by rw [hcard hPN]; exact hP)
      (fun x hx => hAP' hx) (by rw [hcard hP'N]; exact hP')
  have := Subgroup.subgroupOf_inj.mp key
  rwa [inf_eq_left.mpr hPN, inf_eq_left.mpr hP'N] at this

end CFSG.OddStandard.Harada75
