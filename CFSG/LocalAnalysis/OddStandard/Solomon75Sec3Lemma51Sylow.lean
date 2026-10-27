module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.SG_two_signalizer_completeness

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

section Sylow

theorem eq_one_of_pow_two_pow_of_mem_odd_subgroup {G : Type*} [Group G] {N : Subgroup G}
    (hN : Odd (Nat.card N)) {y : G} (hy : y ∈ N) {i : ℕ} (hyi : y ^ (2 ^ i) = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one hyi
  have h2 : orderOf y ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hy
  have hcop : Nat.Coprime (2 ^ i) (Nat.card N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hN)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem orderOf_dvd_of_inv_mul_mem_odd_normal {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) {u v : G} (huv : u⁻¹ * v ∈ N) {i : ℕ}
    (hu : u ^ (2 ^ i) = 1) : orderOf u ∣ orderOf v := by
  refine orderOf_dvd_of_pow_eq_one ?_
  have h1 : u ^ orderOf v ∈ N := by
    have h : (QuotientGroup.mk' N) u = (QuotientGroup.mk' N) v := QuotientGroup.eq.2 huv
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' N) (u ^ orderOf v) = 1
    rw [map_pow, h, ← map_pow, pow_orderOf_eq_one, map_one]
  refine eq_one_of_pow_two_pow_of_mem_odd_subgroup hN h1 (i := i) ?_
  rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]

theorem pow_two_pow_eq_one_of_mem_zpowers_aux {G : Type*} [Group G] {b y : G} {j : ℕ}
    (hb : b ^ (2 ^ j) = 1) (hy : y ∈ Subgroup.zpowers b) : y ^ (2 ^ j) = 1 := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem isPGroup_two_zpowers_aux {G : Type*} [Group G] {b : G} {j : ℕ}
    (hb : b ^ (2 ^ j) = 1) : IsPGroup 2 (Subgroup.zpowers b) := fun y =>
  ⟨j, Subtype.ext (pow_two_pow_eq_one_of_mem_zpowers_aux hb y.2)⟩

theorem mem_smul_sylow_iff_aux {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (g x : G) : x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : g⁻¹ * (MulAut.conj g • a) * g = a := by
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [h1]
    exact ha
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

open scoped Pointwise in
theorem exists_conj_of_isComplement_aux {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN : Odd (Nat.card N)) {a x : G} {j : ℕ} (ha : a ^ (2 ^ j) = 1)
    (hx : x ^ (2 ^ j) = 1) (hax : a⁻¹ * x ∈ N)
    (hG : ∀ g : G, ∃ n ∈ N, ∃ p ∈ Subgroup.zpowers a, g = n * p) :
    ∃ o ∈ N, x = o * a * o⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxa : x⁻¹ * a ∈ N := by simpa using N.inv_mem hax
  have hord : orderOf a = orderOf x :=
    Nat.dvd_antisymm (orderOf_dvd_of_inv_mul_mem_odd_normal hN hax ha)
      (orderOf_dvd_of_inv_mul_mem_odd_normal hN hxa hx)
  have hPp := isPGroup_two_zpowers_aux ha
  have hQp := isPGroup_two_zpowers_aux hx
  have hdisj : Disjoint N (Subgroup.zpowers a) := by
    rw [Subgroup.disjoint_def]
    intro y hyN hyP
    exact eq_one_of_pow_two_pow_of_mem_odd_subgroup hN hyN
      (pow_two_pow_eq_one_of_mem_zpowers_aux ha hyP)
  have hmul : (N : Set G) * (Subgroup.zpowers a : Set G) = Set.univ := by
    refine Set.eq_univ_iff_forall.2 fun g => ?_
    obtain ⟨n, hn, p, hp, rfl⟩ := hG g
    exact Set.mul_mem_mul hn hp
  have hcomp := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hPidx : (Subgroup.zpowers a).index = Nat.card N := hcomp.index_eq_card
  have hcard : Nat.card N * Nat.card (Subgroup.zpowers a) = Nat.card G := hcomp.card_mul_card
  have hQidx : (Subgroup.zpowers x).index = Nat.card N := by
    have h1 := (Subgroup.zpowers x).index_mul_card
    rw [Nat.card_zpowers, ← hord, ← Nat.card_zpowers, ← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hnd : ¬ 2 ∣ Nat.card N := fun h => (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h)
  let Ps : Sylow 2 G := hPp.toSylow (by rw [hPidx]; exact hnd)
  let Qs : Sylow 2 G := hQp.toSylow (by rw [hQidx]; exact hnd)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Ps Qs
  have hxQ : x ∈ (Qs : Subgroup G) := Subgroup.mem_zpowers x
  rw [← hg, mem_smul_sylow_iff_aux] at hxQ
  obtain ⟨n, hn, p, hp, hgnp⟩ := hG g
  have h1 : n⁻¹ * x * n ∈ Subgroup.zpowers a := by
    have h2 : g⁻¹ * x * g ∈ Subgroup.zpowers a := hxQ
    have h3 : n⁻¹ * x * n = p * (g⁻¹ * x * g) * p⁻¹ := by rw [hgnp]; group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hp h2) (Subgroup.inv_mem _ hp)
  have h4 : a⁻¹ * (n⁻¹ * x * n) ∈ N := by
    have h5 : a⁻¹ * (n⁻¹ * x * n) = (a⁻¹ * n⁻¹ * a) * (a⁻¹ * x) * n := by group
    rw [h5]
    refine N.mul_mem (N.mul_mem ?_ hax) hn
    have := (inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) a⁻¹
    simpa using this
  have h6 : a⁻¹ * (n⁻¹ * x * n) ∈ Subgroup.zpowers a :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h1
  have h7 : a⁻¹ * (n⁻¹ * x * n) = 1 := Subgroup.disjoint_def.1 hdisj h4 h6
  refine ⟨n, hn, ?_⟩
  have h8 : n⁻¹ * x * n = a := by
    have := congrArg (a * ·) h7
    simpa [mul_assoc] using this
  calc x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    _ = n * a * n⁻¹ := by rw [h8]

theorem exists_twoElt_mem_of_mem_sup_odd {D : Type*} [Group D] [Finite D] {A N : Subgroup D}
    [N.Normal] (hN : Odd (Nat.card N)) {x : D} (hx : x ∈ A ⊔ N) {j : ℕ} (hxj : x ^ (2 ^ j) = 1) :
    ∃ a ∈ A, a ^ (2 ^ j) = 1 ∧ a⁻¹ * x ∈ N := by
  obtain ⟨a', ha', ν, hν, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  have ht : a' ^ (2 ^ j) ∈ N := by
    have h0 : (QuotientGroup.mk' N) ν = 1 := (QuotientGroup.eq_one_iff ν).2 hν
    have h1 : (QuotientGroup.mk' N) (a' * ν) = (QuotientGroup.mk' N) a' := by
      rw [map_mul, h0, mul_one]
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' N) (a' ^ (2 ^ j)) = 1
    rw [map_pow, ← h1, ← map_pow, hxj, map_one]
  set t := a' ^ (2 ^ j) with htdef
  have htm : t ^ Nat.card N = 1 := by
    have := pow_card_eq_one' (G := N) (x := ⟨t, ht⟩)
    exact congrArg Subtype.val this
  have hcop : IsCoprime ((Nat.card N : ℕ) : ℤ) ((2 ^ j : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hN))
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨a' ^ (u * (Nat.card N : ℤ)), zpow_mem ha' _, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_mul]
    have h1 : u * (Nat.card N : ℤ) * ((2 ^ j : ℕ) : ℤ) = ((2 ^ j * Nat.card N : ℕ) : ℤ) * u := by
      push_cast; ring
    rw [h1, zpow_mul, zpow_natCast, pow_mul, htm, one_zpow]
  · have h1 : u * (Nat.card N : ℤ) = 1 - v * ((2 ^ j : ℕ) : ℤ) := by linarith
    have h3 : a' ^ (((2 ^ j : ℕ) : ℤ) * v) = t ^ v := by rw [zpow_mul, zpow_natCast]
    have h2 : (a' ^ (u * (Nat.card N : ℤ)))⁻¹ * (a' * ν) = t ^ v * ν := by
      rw [h1, zpow_sub, zpow_one, mul_comm v, h3]
      group
    rw [h2]
    exact N.mul_mem (zpow_mem ht v) hν

theorem exists_conj_twoElt_of_mem_sup_odd {D : Type*} [Group D] [Finite D] {A N : Subgroup D}
    [N.Normal] (hN : Odd (Nat.card N)) {x : D} (hx : x ∈ A ⊔ N) {j : ℕ} (hxj : x ^ (2 ^ j) = 1) :
    ∃ o ∈ N, ∃ a ∈ A, a ^ (2 ^ j) = 1 ∧ x = o * a * o⁻¹ := by
  obtain ⟨a, haA, ha2, hax⟩ := exists_twoElt_mem_of_mem_sup_odd hN hx hxj
  have hxH : x ∈ Subgroup.zpowers a ⊔ N := by
    have : x = a * (a⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) hax
  set H : Subgroup D := Subgroup.zpowers a ⊔ N with hH
  have hNH : N ≤ H := le_sup_right
  have haH : a ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hN' : Odd (Nat.card (N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hN
  have hG' : ∀ g : H, ∃ n ∈ N.subgroupOf H, ∃ p ∈ Subgroup.zpowers (⟨a, haH⟩ : H), g = n * p := by
    intro g
    have hg : (g : D) ∈ N ⊔ Subgroup.zpowers a := by rw [sup_comm]; exact g.2
    obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hp
    exact ⟨⟨n, hNH hn⟩, Subgroup.mem_subgroupOf.2 hn, ⟨p, Subgroup.mem_sup_left hp⟩,
      Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext hk⟩, Subtype.ext hnp.symm⟩
  obtain ⟨o, ho, hxo⟩ := exists_conj_of_isComplement_aux (G := H) (N := N.subgroupOf H)
    (a := ⟨a, haH⟩) (x := ⟨x, hxH⟩) (j := j) hN' (Subtype.ext ha2) (Subtype.ext hxj)
    (Subgroup.mem_subgroupOf.2 hax) hG'
  exact ⟨(o : D), Subgroup.mem_subgroupOf.1 ho, a, haA, ha2, congrArg Subtype.val hxo⟩

end Sylow

end CFSG.OddStandard.Solomon75
