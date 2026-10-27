module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63_exists_sylow_pair [Finite G] {X : Subgroup G} {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x * y = y * x) (hxX : x ∈ centralizer (X : Set G))
    (hyX : y ∈ centralizer (X : Set G)) :
    ∃ T : Subgroup G, IsSylow2Of T (centralizer (X : Set G)) ∧ x ∈ T ∧ y ∈ T := by
  have hx2 : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rwa [hx] at h
  have hy2 : y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy] at h
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute x y from hxy).zpow_zpow m n).eq
  have hElem : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (p := 2) hx2)
      (CFSG.Open.isElemAbelian_zpowers (p := 2) hy2) hcomm
  have hB : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
    CFSG.Open.IsElemAbelian.isPGroup hElem
  have hBle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ centralizer (X : Set G) :=
    sup_le ((Subgroup.zpowers_le (g := x)).mpr hxX)
      ((Subgroup.zpowers_le (g := y)).mpr hyX)
  obtain ⟨T, hT, hBT⟩ := sec68_exists_sylow_ge hB hBle
  exact ⟨T, hT, hBT (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)),
    hBT (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))⟩

theorem sec63_isCyclic_inf [Finite G] (h33 : Asc82Lemma33) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {Y T : Subgroup G} (hYC : InCStar Y) (hYF : InFStar Y)
    (hT : IsPGroup 2 T) : IsCyclic ↥(T ⊓ centralizer (Y : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 ↥(T ⊓ centralizer (Y : Set G)) := hT.to_le inf_le_left
  have hU' : IsPGroup 2 ↥((T ⊓ centralizer (Y : Set G)).subgroupOf (centralizer (Y : Set G))) :=
    hU.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨S, hU'S⟩ := hU'.exists_le_sylow
  have hScyc : IsCyclic ↥(S : Subgroup (centralizer (Y : Set G))) :=
    h33 G t L hS Y hYC hYF S
  haveI : IsCyclic ↥(S : Subgroup (centralizer (Y : Set G))) := hScyc
  have hU'cyc : IsCyclic
      ↥((T ⊓ centralizer (Y : Set G)).subgroupOf (centralizer (Y : Set G))) :=
    Subgroup.isCyclic_of_le hU'S
  exact (Subgroup.subgroupOfEquivOfLe inf_le_right).isCyclic.mp hU'cyc

theorem sec63_card_ge_four [Finite G] {U : Subgroup G} {y : G} (hU : IsPGroup 2 U)
    (hy : orderOf y = 2) (hyU : y ∈ U) (hne : Nat.card U ≠ 2) : 4 ≤ Nat.card U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hU.exists_card_eq
  have hdvd : 2 ∣ Nat.card U := by
    have h := Subgroup.orderOf_dvd_natCard U hyU
    rwa [hy] at h
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have h21 : 2 ∣ 1 := by rwa [hn] at hdvd
    exact absurd h21 (by norm_num)
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [pow_one] at hn
    exact hne hn
  have hge : 2 ≤ n := by omega
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge
    _ = Nat.card U := hn.symm

theorem sec63_card_four [Finite G] {R H : Subgroup G} {x : G} (hrel : H.relIndex R ≤ 2)
    (hU : Nat.card ↥(R ⊓ H) = 2) (hxR : x ∈ R) (hxH : x ∉ H) : Nat.card R = 4 := by
  have hcardA : Nat.card ↥(H.subgroupOf R) = 2 := by
    have h1 : Nat.card ↥((H.subgroupOf R).map R.subtype) = Nat.card ↥(H.subgroupOf R) :=
      Subgroup.card_map_of_injective (K := H.subgroupOf R) R.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at h1
    rw [inf_comm] at h1
    rw [← h1]
    exact hU
  have hidx0 : (H.subgroupOf R).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (G := ↥R) (H := H.subgroupOf R)
  have hidx1 : (H.subgroupOf R).index ≠ 1 := by
    intro h
    have hle : R ≤ H := Subgroup.relIndex_eq_one.mp h
    exact hxH (hle hxR)
  have hidx2 : (H.subgroupOf R).index = 2 := by
    have hrel' : (H.subgroupOf R).index ≤ 2 := hrel
    omega
  have hcardR : Nat.card R = Nat.card ↥(H.subgroupOf R) * (H.subgroupOf R).index := by
    rw [Subgroup.card_mul_index (H := H.subgroupOf R)]
  calc Nat.card R = Nat.card ↥(H.subgroupOf R) * (H.subgroupOf R).index := hcardR
    _ = 2 * 2 := by rw [hcardA, hidx2]
    _ = 4 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
