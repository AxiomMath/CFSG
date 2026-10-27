module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.Semidihedral.Principal

open scoped Pointwise

theorem hom_eq_one_of_odd_orderOf {H K : Type*} [Group H] [Group K] (hK : IsPGroup 2 K)
    (f : H →* K) (x : H) (hx : Odd (orderOf x)) : f x = 1 := by
  by_contra hne
  have h2 : 2 ∣ orderOf (f x) := hK.dvd_orderOf hne
  exact (Nat.not_even_iff_odd.mpr (hx.of_dvd_nat (orderOf_map_dvd f x)))
    (even_iff_two_dvd.mpr h2)

variable {H : Type*} [Group H] [Finite H]

theorem sylowTwo_eq_bot_of_not_two_dvd (P : Sylow 2 H) (hodd : ¬ 2 ∣ Nat.card H) :
    (P : Subgroup H) = ⊥ := by
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card H := hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup H)
  have hk0 : k = 0 := by
    by_contra hne
    exact hodd ((dvd_pow_self 2 hne).trans hdvd)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem cyclicSylowTwo_normalizer_le_centralizer (P : Sylow 2 H)
    (hP : IsCyclic (P : Subgroup H)) :
    Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
  by_cases heven : 2 ∣ Nat.card H
  · exact hP.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr heven)
  · intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ (P : Subgroup H) := hy
    rw [sylowTwo_eq_bot_of_not_two_dvd P heven, Subgroup.mem_bot] at hy'
    rw [hy', one_mul, mul_one]

theorem cyclicSylowTwo_normal_odd_complement (P : Sylow 2 H)
    (hP : IsCyclic (P : Subgroup H)) :
    ∃ (N : Subgroup H) (_ : N.Normal),
      (Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∧
      (∀ N' : Subgroup H, N'.Normal → Odd (Nat.card N') → (∃ k : ℕ, N'.index = 2 ^ k) →
        N' = N) ∧
      N.Characteristic ∧ (∀ x : H, x ∈ N ↔ Odd (orderOf x)) ∧
      (N : Set H) * (P : Set H) = Set.univ ∧ N ⊓ (P : Subgroup H) = ⊥ ∧
      Function.Bijective ((QuotientGroup.mk' N).comp (P : Subgroup H).subtype) := by
  have hNC := cyclicSylowTwo_normalizer_le_centralizer P hP
  let N : Subgroup H := (MonoidHom.transferSylow P hNC).ker
  have hcomp : N.IsComplement' (P : Subgroup H) :=
    MonoidHom.ker_transferSylow_isComplement' P hNC
  have hodd : Odd (Nat.card N) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (MonoidHom.not_dvd_card_ker_transferSylow P hNC))
  have hmem : ∀ x : H, x ∈ N ↔ Odd (orderOf x) := by
    intro x
    constructor
    · intro hx
      exact hodd.of_dvd_nat (N.orderOf_dvd_natCard hx)
    · intro hx
      exact hom_eq_one_of_odd_orderOf P.isPGroup' (MonoidHom.transferSylow P hNC) x hx
  have hindex : N.index = Nat.card (P : Subgroup H) := hcomp.symm.index_eq_card
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  refine ⟨N, inferInstance, ⟨hodd, k, hindex.trans hk⟩, ?_, ?_, hmem,
    Subgroup.IsComplement.mul_eq hcomp, disjoint_iff.mp hcomp.disjoint, ?_⟩
  · intro N' hN' hN'odd ⟨k', hk'⟩
    apply le_antisymm
    · intro x hx
      exact (hmem x).mpr (hN'odd.of_dvd_nat (N'.orderOf_dvd_natCard hx))
    · intro x hx
      have hq : QuotientGroup.mk' N' x = 1 :=
        hom_eq_one_of_odd_orderOf (IsPGroup.of_card (n := k') hk') (QuotientGroup.mk' N') x
          ((hmem x).mp hx)
      exact (QuotientGroup.eq_one_iff x).mp hq
  · constructor
    intro φ
    ext x
    change φ x ∈ N ↔ x ∈ N
    rw [hmem, hmem, φ.orderOf_eq]
  · exact Subgroup.isComplement_subgroup_right_iff_bijective.mp hcomp.symm

end CFSG.Semidihedral.Principal
