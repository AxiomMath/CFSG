module

public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.CentralExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped MatrixGroups

theorem card_centralizer_le_of_orderOf_eq_two {F : Type*} [Field F] [Finite F] {a : ℕ}
    (hF : Nat.card F = 2 ^ a) {x : SL(2, F)} (hx : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set SL(2, F))) ≤ 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := a)
    (by rw [← Nat.card_eq_fintype_card, hF])
  have hx1 : x ≠ 1 := (orderOf_eq_prime_iff.mp hx).2
  have hx2 : x * x = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hx).1
  have hP : IsPGroup 2 (Subgroup.centralizer ({x} : Set SL(2, F))) := fun y =>
    ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq]
      exact CFSG.Walter.sl2_mul_self_eq_one_of_commute hx1 hx2
        (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm)⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      omega
    · exact h
  have hdvd : 2 ^ n ∣ 2 ^ a * ((2 ^ a) ^ 2 - 1) := by
    rw [← hn, ← hF, ← CFSG.UnitaryInvolutionIndex.card_specialLinearGroup_fin_two]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : Odd ((2 ^ a) ^ 2 - 1) := by
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) ?_ odd_one
    rw [← pow_mul]
    exact (Nat.even_pow' (by omega)).mpr even_two
  have hcop : Nat.Coprime (2 ^ n) ((2 ^ a) ^ 2 - 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  rw [hn]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

variable {G : Type*} [Group G]

theorem sq_sub_one_le_card_conjugacyWithin [Finite G] {K : Subgroup G} {F : Type*} [Field F]
    [Finite F] {a : ℕ} (hF : Nat.card F = 2 ^ a) (ψ : K ≃* SL(2, F)) {t : G} (htK : t ∈ K)
    (ht : orderOf t = 2) :
    (2 ^ a) ^ 2 - 1 ≤ Nat.card (conjugacyWithin K t) := by
  set t' : K := ⟨t, htK⟩
  have ht' : orderOf (ψ t') = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact ht
  have hcent : Nat.card (Subgroup.centralizer ({t'} : Set K)) ≤ 2 ^ a := by
    refine le_trans ?_ (card_centralizer_le_of_orderOf_eq_two hF ht')
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change ψ y * ψ t' = ψ t' * ψ y
    rw [← map_mul, ← map_mul, hy']
  have hmul := conjugacy_class_card_mul_centralizer t'
  have hK : Nat.card K = 2 ^ a * ((2 ^ a) ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.UnitaryInvolutionIndex.card_specialLinearGroup_fin_two, hF]
  have hc : Nat.card (conjugatesOf t') = Nat.card (conjugacyWithin K t) :=
    Nat.card_congr (conjugacyWithinEquiv K t')
  rw [hK, hc] at hmul
  have hpos : 0 < Nat.card (Subgroup.centralizer ({t'} : Set K)) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card (conjugacyWithin K t) * Nat.card (Subgroup.centralizer ({t'} : Set K)) <
      ((2 ^ a) ^ 2 - 1) * 2 ^ a :=
    calc _ < ((2 ^ a) ^ 2 - 1) * Nat.card (Subgroup.centralizer ({t'} : Set K)) :=
          Nat.mul_lt_mul_of_pos_right hlt hpos
      _ ≤ ((2 ^ a) ^ 2 - 1) * 2 ^ a := Nat.mul_le_mul_left _ hcent
  rw [hmul, mul_comm] at h1
  exact lt_irrefl _ h1

theorem isCyclic_of_isPGroup_three_of_le [Finite G] {L A : Subgroup G} {F : Type*} [Field F]
    [Finite F] (hF : Nat.card F = 4) (ψ : L ≃* SL(2, F)) (hAL : A ≤ L) (hA : IsPGroup 3 A) :
    IsCyclic A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hdvd : 3 ^ n ∣ 60 := by
    rw [← hn]
    have h60 : Nat.card L = 60 := by
      rw [Nat.card_congr ψ.toEquiv, CFSG.UnitaryInvolutionIndex.card_specialLinearGroup_fin_two,
        hF]
      rfl
    rw [← h60]
    exact Subgroup.card_dvd_of_le hAL
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 9 ∣ 60 := (pow_dvd_pow 3 h).trans hdvd
    omega
  interval_cases n
  · rw [pow_zero] at hn
    have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hn).1
    infer_instance
  · rw [pow_one] at hn
    exact isCyclic_of_prime_card hn

end CFSG.ProperTwoGeneratedCore.HighRankPair
