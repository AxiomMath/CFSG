module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_three_cycle_of_ncard_conj_eq_three {A D : Subgroup G}
    (hAc : IsMulCommutative ↥A) (hnot : ¬ A ≤ normalizer (D : Set G))
    (hcard : {R : Subgroup G | ∃ g ∈ A, R = D.map (MulAut.conj g).toMonoidHom}.ncard = 3) :
    ∃ a : G, a ∈ A ∧ ∃ k : ℕ, 1 ≤ k ∧ orderOf a = 3 ^ k ∧
      D.map (MulAut.conj a).toMonoidHom ≠ D ∧
      (D.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom ≠ D ∧
      ((D.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a).toMonoidHom = D := by
  classical
  have hStabNormal : ((A ⊓ normalizer (D : Set G)).subgroupOf A).Normal :=
    Subgroup.normal_of_comm _
  have : Fintype ↥A := Fintype.ofFinite _
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  let _ : MulAction ↥A (Subgroup G) := MulAction.compHom _ (MulAut.conj.comp A.subtype)
  have hset : (MulAction.orbit (↥A) D : Set (Subgroup G)) =
      {R : Subgroup G | ∃ g ∈ A, R = D.map (MulAut.conj g).toMonoidHom} := by
    ext K
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨(m : G), m.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hfin : Fintype.card (MulAction.orbit (↥A) D) =
      {R : Subgroup G | ∃ g ∈ A, R = D.map (MulAut.conj g).toMonoidHom}.ncard := by
    rw [← Nat.card_eq_fintype_card, ← hset, Nat.card_coe_set_eq]
  have hstab : MulAction.stabilizer (↥A) D = (A ⊓ normalizer (D : Set G)).subgroupOf A := by
    ext x
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      change D.map (MulAut.conj (x : G)).toMonoidHom = D at hx
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
    · rintro ⟨-, hx⟩
      change D.map (MulAut.conj (x : G)).toMonoidHom = D
      rwa [Subgroup.mem_normalizer_iff_map_conj_eq] at hx
  have hstabcard : Nat.card ↥(MulAction.stabilizer (↥A) D) =
      Nat.card ↥((A ⊓ normalizer (D : Set G)).subgroupOf A) := by
    rw [hstab]
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (↥A) D
  have h1 : Fintype.card (MulAction.orbit (↥A) D) = 3 := by
    rw [hfin, hcard]
  have h2 : Fintype.card ↥A = Nat.card ↥A := Nat.card_eq_fintype_card.symm
  have h3 : Fintype.card ↥(MulAction.stabilizer (↥A) D) =
      Nat.card ↥(MulAction.stabilizer (↥A) D) := Nat.card_eq_fintype_card.symm
  rw [h1, h3, h2] at horbit
  rw [hstabcard] at horbit
  have hquot : Nat.card (↥A ⧸ (A ⊓ normalizer (D : Set G)).subgroupOf A) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((A ⊓ normalizer (D : Set G)).subgroupOf A)
    have hpos : 0 < Nat.card ↥((A ⊓ normalizer (D : Set G)).subgroupOf A) := Nat.card_pos
    rw [h] at horbit
    exact (Nat.eq_of_mul_eq_mul_right hpos horbit).symm
  obtain ⟨a₀, ha₀A, ha₀not⟩ := Set.not_subset.mp hnot
  let π : ↥A →* (↥A ⧸ (A ⊓ normalizer (D : Set G)).subgroupOf A) :=
    QuotientGroup.mk' _
  have hπne : π ⟨a₀, ha₀A⟩ ≠ 1 := by
    intro h
    exact ha₀not (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)).2
  have hπ3 : orderOf (π ⟨a₀, ha₀A⟩) = 3 := by
    refine orderOf_eq_prime ?_ hπne
    have : Fintype (↥A ⧸ (A ⊓ normalizer (D : Set G)).subgroupOf A) := Fintype.ofFinite _
    rw [← hquot, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have h3dvd : 3 ∣ orderOf a₀ := by
    have h := orderOf_map_dvd π ⟨a₀, ha₀A⟩
    rw [hπ3, Subgroup.orderOf_mk a₀ ha₀A] at h
    exact h
  obtain ⟨k, s, hs3, hms⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos a₀).ne' 3 (by norm_num)
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, mul_zero] at hms
    exact (orderOf_pos a₀).ne' hms
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hms
    exact hs3 (hms ▸ h3dvd)
  have hgcs : Nat.gcd (orderOf a₀) s = s := by
    rw [hms]
    exact Nat.gcd_eq_right (Dvd.intro (3 ^ k) (by rw [mul_comm]))
  let a : G := a₀ ^ s
  have haA : a ∈ A := A.pow_mem ha₀A s
  have haord : orderOf a = 3 ^ k := by
    rw [orderOf_pow' a₀ hs0, hgcs, hms, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]
  have hπa : π ⟨a, haA⟩ = (π ⟨a₀, ha₀A⟩) ^ s := by
    rw [← map_pow]
    rfl
  have ha_not_stab : a ∉ A ⊓ normalizer (D : Set G) := by
    intro hmem
    have hπ1 : π ⟨a, haA⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hmem)
    rw [hπa] at hπ1
    have hdvd : orderOf (π ⟨a₀, ha₀A⟩) ∣ s := orderOf_dvd_of_pow_eq_one hπ1
    rw [hπ3] at hdvd
    exact hs3 hdvd
  have ha2_not_stab : a ^ 2 ∉ A ⊓ normalizer (D : Set G) := by
    intro hmem
    have hπ1 : π ⟨a ^ 2, A.pow_mem haA 2⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hmem)
    have hpow : π ⟨a ^ 2, A.pow_mem haA 2⟩ = (π ⟨a₀, ha₀A⟩) ^ (2 * s) := by
      have h1 : (⟨a ^ 2, A.pow_mem haA 2⟩ : ↥A) = (⟨a, haA⟩ : ↥A) ^ 2 := rfl
      rw [h1, map_pow, hπa, ← pow_mul]
      ring_nf
    rw [hpow] at hπ1
    have hdvd : orderOf (π ⟨a₀, ha₀A⟩) ∣ 2 * s := orderOf_dvd_of_pow_eq_one hπ1
    rw [hπ3] at hdvd
    exact hs3 ((Nat.prime_three.dvd_mul.mp hdvd).resolve_left (by norm_num))
  have ha3_stab : a ^ 3 ∈ A ⊓ normalizer (D : Set G) := by
    refine ⟨A.pow_mem haA 3, ?_⟩
    change a ^ 3 ∈ normalizer (D : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hπ1 : π ⟨a ^ 3, A.pow_mem haA 3⟩ = 1 := by
      have h1 : (⟨a ^ 3, A.pow_mem haA 3⟩ : ↥A) = (⟨a, haA⟩ : ↥A) ^ 3 := rfl
      rw [h1, map_pow, hπa]
      have hpow : ((π ⟨a₀, ha₀A⟩) ^ s) ^ 3 = ((π ⟨a₀, ha₀A⟩) ^ 3) ^ s := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [hpow, ← hπ3, pow_orderOf_eq_one, one_pow]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hπ1)).2
  have ha_not_norm : a ∉ normalizer (D : Set G) := fun h => ha_not_stab ⟨haA, h⟩
  have ha2_not_norm : a ^ 2 ∉ normalizer (D : Set G) :=
    fun h => ha2_not_stab ⟨A.pow_mem haA 2, h⟩
  refine ⟨a, haA, k, hk1, haord, ?_, ?_, ?_⟩
  · intro h
    exact ha_not_norm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  · intro h
    have hmap : D.map (MulAut.conj (a ^ 2)).toMonoidHom = D := by
      have hmul : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
          (MulAut.conj (a ^ 2)).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show a ^ 2 = a * a by rw [pow_two]]
        group
      rw [← hmul, ← Subgroup.map_map]
      exact h
    exact ha2_not_norm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)
  · have hnorm : a ^ 3 ∈ normalizer (D : Set G) := ha3_stab.2
    have hthis := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm
    have hmul : ((MulAut.conj a).toMonoidHom.comp (MulAut.conj a).toMonoidHom).comp
        (MulAut.conj a).toMonoidHom = (MulAut.conj (a ^ 3)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show a ^ 3 = a * a * a by rw [pow_succ, pow_succ, pow_one]]
      group
    rw [Subgroup.map_map, Subgroup.map_map, hmul]
    exact hthis

end CFSG.GroupTheory
