module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Core
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup CFSG.Open
open scoped commutatorElement

private theorem eq_of_orderOf_eq_two_of_isCyclic' {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {a b : Z} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite Z
  by_contra hab
  have h := IsCyclic.card_pow_eq_one_le (α := Z) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Z) ⊆ Finset.univ.filter (fun x : Z => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · rw [← ha]; exact pow_orderOf_eq_one x
    · rw [← hb]; exact pow_orderOf_eq_one x
  have ha1 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num at ha
  have hb1 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; norm_num at hb
  have hcard : ({1, a, b} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1⟩
  have := Finset.card_le_card hsub
  omega

theorem central_sq_of_twoCore {G : Type} [Group G] [Finite G] {z : G} {K : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K) (hz : orderOf z = 2) (hzK : z ∈ K)
    (hzc : K ≤ centralizer ({z} : Set G)) (hc : IsCyclic ↥(pCoreOf 2 K))
    (h4 : Nat.card ↥(pCoreOf 2 K) = 4) {u : G} (hu : u ∈ pCoreOf 2 K) (hu4 : orderOf u = 4) :
    u ^ 2 = z ∧ ∀ k ∈ K, k * u = u * k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpc_not_top : CFSG.pCore 2 ↥K ≠ ⊤ := by
    intro htop
    haveI : Finite ↥K := inferInstance
    have hPK : IsPGroup 2 ↥K := by
      have h' : IsPGroup 2 (⊤ : Subgroup ↥K) :=
        htop ▸ (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
      exact h'.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent ↥K := hPK.isNilpotent
    haveI : Group.IsPerfect ↥K := hq.1
    haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact Group.IsPerfect.not_isNilpotent ↥K inferInstance
  have hpc_le_center : CFSG.pCore 2 ↥K ≤ Subgroup.center ↥K :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hq (N := CFSG.pCore 2 ↥K)
      inferInstance).resolve_left hpc_not_top
  have hpc_le_cent : CFSG.Open.pCoreOf 2 K ≤ Subgroup.centralizer (K : Set G) := by
    intro w hw
    rw [CFSG.Open.pCoreOf] at hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp (hpc_le_center hx) ⟨k, hk⟩)
  have hz_pcoreOf : z ∈ CFSG.Open.pCoreOf 2 K := by
    have hz_center : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hzc y.2))
    have hZnormal : (Subgroup.zpowers (⟨z, hzK⟩ : ↥K)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz_center)
    have hZP : IsPGroup 2 (Subgroup.zpowers (⟨z, hzK⟩ : ↥K)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz, pow_one]
    have hle : Subgroup.zpowers (⟨z, hzK⟩ : ↥K) ≤ CFSG.pCore 2 ↥K :=
      le_sSup ⟨hZnormal, hZP⟩
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.mem_map_of_mem K.subtype (hle (Subgroup.mem_zpowers _))
  have hu_comm : ∀ k ∈ K, k * u = u * k :=
    fun k hk => Subgroup.mem_centralizer_iff.mp (hpc_le_cent hu) k hk
  refine ⟨?_, hu_comm⟩
  have hu' : orderOf (⟨u, hu⟩ : ↥(CFSG.Open.pCoreOf 2 K)) = 4 := by
    rw [Subgroup.orderOf_mk, hu4]
  have hsq_order : orderOf ((⟨u, hu⟩ : ↥(CFSG.Open.pCoreOf 2 K)) ^ 2) = 2 := by
    rw [orderOf_pow, hu']
    norm_num
  have hz_order : orderOf (⟨z, hz_pcoreOf⟩ : ↥(CFSG.Open.pCoreOf 2 K)) = 2 := by
    rw [Subgroup.orderOf_mk, hz]
  have hsq_eq : (⟨u, hu⟩ : ↥(CFSG.Open.pCoreOf 2 K)) ^ 2 = ⟨z, hz_pcoreOf⟩ :=
    eq_of_orderOf_eq_two_of_isCyclic' hsq_order hz_order
  simpa using congrArg Subtype.val hsq_eq

theorem mem_zpowers_of_central_two {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hc : IsCyclic ↥(pCoreOf 2 K)) (h4 : Nat.card ↥(pCoreOf 2 K) = 4) {u : G}
    (hu : u ∈ pCoreOf 2 K) (hu4 : orderOf u = 4) {c : G} (hcK : c ∈ K)
    (hcc : ∀ k ∈ K, k * c = c * k) (hc2 : IsPGroup 2 (zpowers c)) : c ∈ zpowers u := by
  let c' : ↥K := ⟨c, hcK⟩
  have hc'center : c' ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcc (y : G) y.2)
  have hZnormal : (Subgroup.zpowers c').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hc'center)
  have hmap : (Subgroup.zpowers c').map K.subtype = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hiso : ↥(Subgroup.zpowers c') ≃* ↥(Subgroup.zpowers c) :=
    (Subgroup.equivMapOfInjective (Subgroup.zpowers c') K.subtype
      K.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have hZP : IsPGroup 2 (Subgroup.zpowers c') := hc2.of_equiv hiso.symm
  have hZle : Subgroup.zpowers c' ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hZnormal, hZP⟩
  have hc'pcore : c' ∈ CFSG.pCore 2 ↥K := hZle (Subgroup.mem_zpowers c')
  have hc_pcoreOf : c ∈ CFSG.Open.pCoreOf 2 K := by
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.mem_map_of_mem K.subtype hc'pcore
  have hzp_le : Subgroup.zpowers u ≤ CFSG.Open.pCoreOf 2 K := Subgroup.zpowers_le.mpr hu
  have hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 K) ≤ Nat.card ↥(Subgroup.zpowers u) := by
    rw [Nat.card_zpowers, hu4, h4]
  have heq : Subgroup.zpowers u = CFSG.Open.pCoreOf 2 K :=
    Subgroup.eq_of_le_of_card_ge hzp_le hcard
  rw [heq]
  exact hc_pcoreOf

theorem exists_orderOf_four_of_twoCore {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hc : IsCyclic ↥(pCoreOf 2 K)) (h4 : Nat.card ↥(pCoreOf 2 K) = 4) :
    ∃ u : G, u ∈ pCoreOf 2 K ∧ orderOf u = 4 := by
  haveI := hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(CFSG.Open.pCoreOf 2 K))
  refine ⟨g, g.2, ?_⟩
  rw [Subgroup.orderOf_coe, hg, h4]

theorem Case3Core.exists_generator {G : Type} [Group G] [Finite G] {z : G} {K : Subgroup G}
    (h : Case3Core G z K) :
    ∃ u : G, u ∈ pCoreOf 2 K ∧ orderOf u = 4 ∧ u ^ 2 = z ∧ ∀ k ∈ K, k * u = u * k := by
  obtain ⟨u, hu, hu4⟩ := exists_orderOf_four_of_twoCore h.isCyclic_twoCore h.card_twoCore
  exact ⟨u, hu, hu4, central_sq_of_twoCore h.quasisimple h.orderOf_eq h.mem h.le_centralizer
    h.isCyclic_twoCore h.card_twoCore hu hu4⟩

end CFSG.OddStandard.HigherRank.G2Three
