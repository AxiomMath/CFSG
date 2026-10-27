module

import CFSG.GroupTheory.Frattini.PSubgroupLift
import TauCeti.GroupTheory.Sylow
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

variable {X G : Type*} [Group X] [Finite X] [Group G]

private theorem isPGroup_closure_pair_of_pow_three {a b : G} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : Commute a b) :
    IsPGroup 3 (Subgroup.closure ({a, b} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup G := Subgroup.closure ({a, b} : Set G)
  have haP : a ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbP : b ∈ P :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hpair : ({a, b} : Set G).Pairwise Commute := by
    rw [Set.pairwise_pair]
    exact fun _ => ⟨hab, hab.symm⟩
  haveI : IsMulCommutative P := Subgroup.isMulCommutative_closure hpair
  letI : CommGroup P := IsMulCommutative.instCommGroup
  let a' : P := ⟨a, haP⟩
  let b' : P := ⟨b, hbP⟩
  have ha' : a' ^ 3 = 1 := by ext; simpa using ha
  have hb' : b' ^ 3 = 1 := by ext; simpa using hb
  let Q : Subgroup P := Subgroup.closure ({a', b'} : Set P)
  have hQ : Q = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    simp [Q, a', b', MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype, P]
  intro z
  have hz3 : z ^ 3 = 1 := by
    have hzQ : z ∈ Q := by rw [hQ]; exact Subgroup.mem_top z
    obtain ⟨m, n, hmn⟩ := (Subgroup.mem_closure_pair (x := a') (y := b') (z := z)).mp hzQ
    have hma : (a' ^ m) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha', one_zpow]
    have hnb : (b' ^ n) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb', one_zpow]
    rw [← hmn, (Commute.all (a' ^ m) (b' ^ n)).mul_pow, hma, hnb, mul_one]
  refine ⟨1, ?_⟩
  simpa using hz3

private theorem pow_three_eq_one_of_mem_of_inf_ker_eq_bot {ψ : X →* G} {A : Subgroup X}
    (hdisj : A ⊓ ψ.ker = ⊥) {u : X} (hu : u ∈ A) (hu3 : ψ u ^ 3 = 1) : u ^ 3 = 1 := by
  have hmem : u ^ 3 ∈ A ⊓ ψ.ker := by
    refine Subgroup.mem_inf.mpr ⟨A.pow_mem hu 3, ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    exact hu3
  rw [hdisj, Subgroup.mem_bot] at hmem
  exact hmem

private theorem eq_of_mem_of_map_eq_of_inf_ker_eq_bot {ψ : X →* G} {A : Subgroup X}
    (hdisj : A ⊓ ψ.ker = ⊥) {u v : X} (hu : u ∈ A) (hv : v ∈ A) (h : ψ u = ψ v) : u = v := by
  have hmem : u * v⁻¹ ∈ A ⊓ ψ.ker := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem hu (A.inv_mem hv), ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [hdisj, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

private theorem eq_one_of_mem_ker_of_pow_three {ψ : X →* G}
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) {u : X} (hu : u ∈ ψ.ker) (hu3 : u ^ 3 = 1) : u = 1 := by
  have hcop : Nat.Coprime 3 (Nat.card ψ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have h2 : orderOf u ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard _ hu
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.of_dvd_left h1 hcop) h2)

private theorem emod_three_eq_one_of_zpow_eq {a : G} (ha : orderOf a = 3) {m : ℤ}
    (h : a ^ m = a) : m % (3 : ℤ) = 1 := by
  have h1 : a ^ (m % 3) = a := by
    have hmod : m % (3 : ℤ) = m % (orderOf a : ℤ) := by rw [ha]; norm_num
    rw [hmod, zpow_mod_orderOf, h]
  have h2 : a ^ (m % 3) = a ^ (1 : ℤ) := by simpa using h1
  have h3 := (zpow_eq_zpow_iff_modEq (x := a) (m := m % 3) (n := 1)).mp h2
  have h4 : (3 : ℤ) ∣ 1 - m % 3 := by
    have := Int.modEq_iff_dvd.mp h3
    simpa [ha] using this
  have hb1 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
  have hb2 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
  omega

private theorem zpow_eq_self_of_emod_three_eq_one {y : X} (hy : orderOf y = 3) {m : ℤ}
    (hm : m % (3 : ℤ) = 1) : y ^ m = y := by
  have h1 : y ^ (m % (3 : ℤ)) = y ^ m := by
    rw [show m % (3 : ℤ) = m % (orderOf y : ℤ) by rw [hy]; norm_num]
    exact zpow_mod_orderOf y m
  rw [← h1, hm]
  simp

private theorem isConj_of_map_eq_of_pow_three (ψ : X →* G) (hψ : Function.Surjective ψ)
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) {x y : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : ψ x = ψ y) : IsConj x y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite G := Finite.of_surjective ψ hψ
  by_cases ha1 : ψ x = 1
  · have hx1 : x = 1 :=
      eq_one_of_mem_ker_of_pow_three h3 (MonoidHom.mem_ker.mpr ha1) hx
    have hy1 : y = 1 :=
      eq_one_of_mem_ker_of_pow_three h3 (by rw [MonoidHom.mem_ker, ← hxy]; exact ha1) hy
    rw [hx1, hy1]
  · set a : G := ψ x with ha
    have hya : ψ y = a := hxy ▸ rfl
    have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hx, map_one]
    have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hxne : x ≠ 1 := fun h => ha1 (by rw [ha, h, map_one])
    have hyne : y ≠ 1 := fun h => ha1 (by rw [hxy, h, map_one])
    have hxord : orderOf x = 3 := orderOf_eq_prime hx hxne
    have hyord : orderOf y = 3 := orderOf_eq_prime hy hyne
    let M : Subgroup X := (Subgroup.zpowers a).comap ψ
    have hxM : x ∈ M := Subgroup.mem_comap.mpr (by rw [ha]; exact Subgroup.mem_zpowers a)
    have hyM : y ∈ M := Subgroup.mem_comap.mpr (by rw [hya]; exact Subgroup.mem_zpowers a)
    have hxMord : orderOf (⟨x, hxM⟩ : M) = 3 := by rw [Subgroup.orderOf_mk, hxord]
    have hyMord : orderOf (⟨y, hyM⟩ : M) = 3 := by rw [Subgroup.orderOf_mk, hyord]
    have hMcard : Nat.card M = Nat.card ψ.ker * 3 := by
      rw [CFSG.GroupTheory.card_comap_eq_card_ker_mul_card ψ hψ (Subgroup.zpowers a),
        Nat.card_zpowers, haord]
    have h9 : ¬ 3 ^ 2 ∣ Nat.card M := by
      rw [hMcard]
      intro h
      have h' : 3 * 3 ∣ 3 * Nat.card ψ.ker := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h
      exact h3 ((Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp h')
    obtain ⟨q, hq⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd
      (G := M) (p := 3) h9 hyMord hxMord
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hval : y ^ m = (q : X) * x * (q : X)⁻¹ := by
      simpa using congrArg Subtype.val hm
    have hqM : ψ (q : X) ∈ Subgroup.zpowers a := Subgroup.mem_comap.mp (q : M).2
    have hconj_a : ψ (q : X) * a * (ψ (q : X))⁻¹ = a := by
      obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hqM
      rw [← hr]
      have hcomm : Commute (a ^ r) a := (Commute.refl a).zpow_left r
      rw [hcomm.eq]
      group
    have hψval : a ^ m = a := by
      have h := congrArg ψ hval
      rw [map_zpow, hya, map_mul, map_mul, map_inv, hconj_a] at h
      exact h
    have hm1 : m % (3 : ℤ) = 1 := emod_three_eq_one_of_zpow_eq haord hψval
    have hy_m : y ^ m = y := zpow_eq_self_of_emod_three_eq_one hyord hm1
    exact isConj_iff.mpr ⟨(q : X), by rw [← hval, hy_m]⟩

theorem exists_lift_commute_of_pow_three (ψ : X →* G) (hψ : Function.Surjective ψ)
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Commute a b) :
    ∃ x y : X, ψ x = a ∧ ψ y = b ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute x y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite G := Finite.of_surjective ψ hψ
  set P : Subgroup G := Subgroup.closure ({a, b} : Set G)
  have haP : a ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbP : b ∈ P :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hP3 : IsPGroup 3 P := isPGroup_closure_pair_of_pow_three ha hb hab
  obtain ⟨A, -, -, hAmap, hAdisj⟩ :=
    CFSG.GroupTheory.exists_pSubgroup_map_eq_of_coprime_ker (p := 3) ψ hψ h3 hP3
  obtain ⟨x, hxA, hxa⟩ := Subgroup.mem_map.mp (hAmap ▸ haP)
  obtain ⟨y, hyA, hyb⟩ := Subgroup.mem_map.mp (hAmap ▸ hbP)
  have hx3 : x ^ 3 = 1 :=
    pow_three_eq_one_of_mem_of_inf_ker_eq_bot hAdisj hxA (by rw [hxa, ha])
  have hy3 : y ^ 3 = 1 :=
    pow_three_eq_one_of_mem_of_inf_ker_eq_bot hAdisj hyA (by rw [hyb, hb])
  have hxy : Commute x y := by
    show x * y = y * x
    refine eq_of_mem_of_map_eq_of_inf_ker_eq_bot hAdisj
      (A.mul_mem hxA hyA) (A.mul_mem hyA hxA) ?_
    rw [map_mul, map_mul, hxa, hyb, hab.eq]
  exact ⟨x, y, hxa, hyb, hx3, hy3, hxy⟩

theorem isConj_of_isConj_map_of_pow_three (ψ : X →* G) (hψ : Function.Surjective ψ)
    (h3 : ¬ 3 ∣ Nat.card ψ.ker) {x y : X} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : IsConj (ψ x) (ψ y)) : IsConj x y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite G := Finite.of_surjective ψ hψ
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  obtain ⟨k, hk⟩ := hψ g
  have hx'3 : (k * x * k⁻¹) ^ 3 = 1 := by
    rw [show k * x * k⁻¹ = (MulAut.conj k) x by rw [MulAut.conj_apply]]
    rw [← map_pow, hx, map_one]
  have hx'y : ψ (k * x * k⁻¹) = ψ y := by
    rw [map_mul, map_mul, map_inv, hk, hg]
  have hxx' : IsConj x (k * x * k⁻¹) := isConj_iff.mpr ⟨k, rfl⟩
  exact hxx'.trans
    (isConj_of_map_eq_of_pow_three ψ hψ h3 hx'3 hy hx'y)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin
