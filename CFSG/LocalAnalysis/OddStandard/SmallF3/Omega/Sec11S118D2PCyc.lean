module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesSign

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11d2_eq_of_orderOf_eq_two {K : Subgroup G} [Finite K] (hK : IsCyclic K) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : x = y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : 2 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← hx2]
    exact Subgroup.orderOf_dvd_natCard K hx
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h2
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : (⟨x, hx⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  have hya : (⟨y, hy⟩ : K) ∈ ({a} : Finset K) :=
    ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Subgroup.orderOf_mk]⟩
  rw [Finset.mem_singleton] at hxa hya
  exact congrArg Subtype.val (hxa.trans hya.symm)

theorem sec11d2_eq_one_or_eq_of_sq [Finite G] {K : Subgroup G} (hK : IsCyclic K) {t x : G}
    (ht : t ∈ K) (ht2 : orderOf t = 2) (hx : x ∈ K) (hx2 : x * x = 1) : x = 1 ∨ x = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : x = 1
  · exact Or.inl h1
  · exact Or.inr
      (sec11d2_eq_of_orderOf_eq_two hK hx ht (orderOf_eq_prime (by rw [pow_two]; exact hx2) h1)
        ht2)

theorem sec11d2_mul_comm_of_isCyclic {K : Subgroup G} (hK : IsCyclic K) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) : x * y = y * x := by
  haveI := hK
  have h := (IsCyclic.isMulCommutative (α := K)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val h

theorem sec11d2_exists_orderOf_eq_four [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    (hK2 : IsPGroup 2 K) (hcard : 2 < Nat.card K) : ∃ a ∈ K, orderOf a = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hK
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK2
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have h4 : 4 ∣ Nat.card K := by
    rw [hn]
    have h2n : 2 ≤ n := by
      by_contra h
      have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> rw [hn] at hcard <;> norm_num at hcard
    exact (pow_dvd_pow 2 h2n : 2 ^ 2 ∣ 2 ^ n)
  refine ⟨((γ ^ (orderOf γ / 4) : K) : G), (γ ^ (orderOf γ / 4)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (by rw [hγ]; exact Nat.card_pos.ne') (by rw [hγ]; exact h4)

theorem sec11d2_eq_or_eq_inv_of_orderOf_eq_four [Finite G] {K : Subgroup G} (hK : IsCyclic K)
    {a x : G} (ha : a ∈ K) (hx : x ∈ K) (ha4 : orderOf a = 4) (hx4 : orderOf x = 4) :
    x = a ∨ x = a⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h4 : 4 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← ha4]
    exact Subgroup.orderOf_dvd_natCard K ha
  have h := IsCyclic.card_orderOf_eq_totient (α := K) h4
  rw [show Nat.totient 4 = 2 by decide] at h
  have hne : (⟨a, ha⟩ : K) ≠ ⟨a⁻¹, K.inv_mem ha⟩ := by
    intro he
    have h1 : a * a = 1 := by
      have h' : a = a⁻¹ := congrArg Subtype.val he
      calc a * a = a * a⁻¹ := by rw [← h']
        _ = 1 := mul_inv_cancel a
    have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h1])
    rw [ha4] at h2
    exact absurd h2 (by decide)
  have hsub : ({⟨a, ha⟩, ⟨a⁻¹, K.inv_mem ha⟩} : Finset K) ⊆
      Finset.univ.filter fun y : K => orderOf y = 4 := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Finset.mem_filter]
    rcases hy with rfl | rfl
    · exact ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, ha4]⟩
    · exact ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, orderOf_inv, ha4]⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h, Finset.card_pair hne])
  have hxm : (⟨x, hx⟩ : K) ∈ Finset.univ.filter fun y : K => orderOf y = 4 :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Subgroup.orderOf_mk, hx4]⟩
  rw [← heq, Finset.mem_insert, Finset.mem_singleton] at hxm
  rcases hxm with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

theorem sec11d2_cyc_conj [Finite G] {Y : Subgroup G} (hY : IsCyclic Y) (hY2 : IsPGroup 2 Y)
    {a c : G} (haa : a * a = 1) (haY : ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (hcY : c ∈ Y)
    (hc4 : orderOf c = 4) (hac : a * c = c * a) {y : G} (hy : y ∈ Y) :
    a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = c * c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hwY : a * y * a⁻¹ * y⁻¹ ∈ Y := Y.mul_mem (haY y hy) (Y.inv_mem hy)
  generalize hw : a * y * a⁻¹ * y⁻¹ = w at hwY
  have hconj : a * w * a⁻¹ = w⁻¹ := by
    have e1 : a * w * a⁻¹ = (a * a) * y * a⁻¹ * y⁻¹ * a⁻¹ := by rw [← hw]; group
    have e2 : w⁻¹ = y * a * y⁻¹ * a⁻¹ := by rw [← hw]; group
    rw [e1, e2, haa, one_mul, hainv]
  have hpow : ∀ n : ℕ, a * w ^ n * a⁻¹ = (w ^ n)⁻¹ := by
    intro n
    rw [← conj_pow, hconj, inv_pow]
  have hcc2 : orderOf (c * c) = 2 := by
    rw [← pow_two, orderOf_pow, hc4]
    norm_num
  have hccY : c * c ∈ Y := Y.mul_mem hcY hcY
  have hsq : w * w = 1 := by
    by_contra hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hY2 ⟨w, hwY⟩
    have hk' : orderOf w = 2 ^ k := by rw [← Subgroup.orderOf_mk w hwY]; exact hk
    have hk2 : 2 ≤ k := by
      by_contra hlt
      apply hne
      have h2 : w ^ 2 = 1 := by
        have h0 := pow_orderOf_eq_one w
        rw [hk'] at h0
        interval_cases k
        · have h1 : w = 1 := by simpa using h0
          rw [h1]
          simp
        · exact h0
      simpa [pow_two] using h2
    have hdvd : 4 ∣ orderOf w := by
      rw [hk']
      exact Dvd.dvd.trans (by norm_num : (4 : ℕ) ∣ 2 ^ 2) (pow_dvd_pow 2 hk2)
    have hw'o : orderOf (w ^ (orderOf w / 4)) = 4 :=
      orderOf_pow_orderOf_div (by rw [hk']; positivity) hdvd
    have hw'Y : w ^ (orderOf w / 4) ∈ Y := Y.pow_mem hwY _
    have hfix : a * (w ^ (orderOf w / 4)) * a⁻¹ = w ^ (orderOf w / 4) := by
      rcases sec11d2_eq_or_eq_inv_of_orderOf_eq_four hY hcY hw'Y hc4 hw'o with h | h
      · rw [h, hac]
        group
      · rw [h]
        have e : a * c⁻¹ * a⁻¹ = (a * c * a⁻¹)⁻¹ := by group
        rw [e, hac]
        group
    have hinvq := hpow (orderOf w / 4)
    rw [hfix] at hinvq
    have h22 : (w ^ (orderOf w / 4)) * (w ^ (orderOf w / 4)) = 1 := by
      calc (w ^ (orderOf w / 4)) * (w ^ (orderOf w / 4))
          = (w ^ (orderOf w / 4)) * ((w ^ (orderOf w / 4)))⁻¹⁻¹ := by rw [inv_inv]
        _ = 1 := by rw [← hinvq]; exact mul_inv_cancel _
    have hdvd2 : orderOf (w ^ (orderOf w / 4)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [sq, h22])
    rw [hw'o] at hdvd2
    exact absurd hdvd2 (by decide)
  exact sec11d2_eq_one_or_eq_of_sq hY hccY hcc2 hwY hsq

theorem sec11d2_mul_mem_of_nmem {D Y : Subgroup G} (hYi : Y.relIndex D = 2) {x y : G}
    (hxD : x ∈ D) (hyD : y ∈ D) (hx : x ∉ Y) (hy : y ∉ Y) : x * y ∈ Y := by
  have hi : (Y.subgroupOf D).index = 2 := hYi
  have hx' : (⟨x, hxD⟩ : D) ∉ Y.subgroupOf D := fun h => hx (Subgroup.mem_subgroupOf.mp h)
  have hy' : (⟨y, hyD⟩ : D) ∉ Y.subgroupOf D := fun h => hy (Subgroup.mem_subgroupOf.mp h)
  exact Subgroup.mem_subgroupOf.mp
    ((Subgroup.mul_mem_iff_of_index_two hi (a := ⟨x, hxD⟩) (b := ⟨y, hyD⟩)).2
      (iff_of_false hx' hy'))

theorem sec11d2_conj_mem {D Y : Subgroup G} (hYD : Y ≤ D) (hYi : Y.relIndex D = 2) {x y : G}
    (hxD : x ∈ D) (hy : y ∈ Y) : x * y * x⁻¹ ∈ Y := by
  have hi : (Y.subgroupOf D).index = 2 := hYi
  haveI := Subgroup.normal_of_index_eq_two hi
  have h := (inferInstance : (Y.subgroupOf D).Normal).conj_mem ⟨y, hYD hy⟩
    (Subgroup.mem_subgroupOf.mpr hy) ⟨x, hxD⟩
  exact Subgroup.mem_subgroupOf.mp h

end CFSG.OddStandard.SmallF3.Omega
