module

public import CFSG.GF2Type.Aschbacher1976Common.DihedralEvenRank

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem m6e8_cyclic_unique_involution {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {x y : H} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hle := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by norm_num)
  by_contra hne
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  have hsub : ({1, x, y} : Finset H) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [← hx]; exact pow_orderOf_eq_one _
    · rw [← hy]; exact pow_orderOf_eq_one _
  have hcard : ({1, x, y} : Finset H).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, x, y, hx1.symm, hy1.symm, hne, rfl⟩
  have h2 := Finset.card_le_card hsub
  omega

private theorem m6e8_unique_involution {A : Subgroup G} (hAcyc : IsCyclic A) {u v : G}
    (hu : u ∈ A) (hv : v ∈ A) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) : u = v := by
  haveI : IsCyclic ↥A := hAcyc
  have hu2' : orderOf (⟨u, hu⟩ : ↥A) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨u, hu⟩ : ↥A)]; exact hu2
  have hv2' : orderOf (⟨v, hv⟩ : ↥A) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨v, hv⟩ : ↥A)]; exact hv2
  have h : (⟨u, hu⟩ : ↥A) = ⟨v, hv⟩ :=
    m6e8_cyclic_unique_involution (H := ↥A) hu2' hv2'
  exact Subtype.ext_iff.mp h

private theorem m6e8_exists_orderOf_four {A : Subgroup G} (hAcyc : IsCyclic A)
    (h4 : 4 ∣ Nat.card A) : ∃ ζ ∈ A, orderOf ζ = 4 := by
  haveI : IsCyclic ↥A := hAcyc
  haveI : Fintype ↥A := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
  have h4' : 4 ∣ orderOf x := by rw [hx]; exact h4
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨((x ^ (orderOf x / 4) : ↥A) : G), (x ^ (orderOf x / 4)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div hx0 h4'

private theorem m6e8_normalizer_of_index_two {C K : Subgroup G} (hKC : K ≤ C)
    (hKi : K.relIndex C = 2) {c : G} (hcC : c ∈ C) : c ∈ normalizer (K : Set G) := by
  have hKi' : (K.subgroupOf C).index = 2 := hKi
  haveI : (K.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hKi'
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp inferInstance hcC

theorem m6e8_central_mem {K A : Subgroup G} {r : G} (hAK : A ≤ K) (hAcyc : IsCyclic A)
    (hAord : ∀ k ∈ K, k ∉ A → orderOf k < Nat.card A)
    (hrK : r ∈ K) (hr2 : orderOf r = 2) (hrZ : ∀ k ∈ K, k * r = r * k) : r ∈ A := by
  classical
  by_contra hrA
  haveI : IsCyclic ↥A := hAcyc
  obtain ⟨ρ, hρgen⟩ := IsCyclic.exists_generator (α := ↥A)
  have hρA : (ρ : G) ∈ A := ρ.2
  have hordρ : orderOf (ρ : G) = Nat.card A := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hρgen]
  have hρrK : (ρ : G) * r ∈ K := K.mul_mem (hAK hρA) hrK
  have hρrA : (ρ : G) * r ∉ A := by
    intro h
    refine hrA ?_
    have := A.mul_mem (A.inv_mem hρA) h
    simpa using this
  have hlt : orderOf ((ρ : G) * r) < Nat.card A := hAord _ hρrK hρrA
  have hcomm : Commute (ρ : G) r := hrZ (ρ : G) (hAK hρA)
  set m : ℕ := orderOf ((ρ : G) * r) with hm
  have hsplit : ((ρ : G) * r) ^ m = (ρ : G) ^ m * r ^ m := hcomm.mul_pow m
  have hpow : ((ρ : G) * r) ^ m = 1 := pow_orderOf_eq_one _
  have h1 : (ρ : G) ^ m * r ^ m = 1 := by rw [← hsplit, hpow]
  have h2 : (ρ : G) ^ m = (r ^ m)⁻¹ := by
    calc (ρ : G) ^ m = (ρ : G) ^ m * r ^ m * (r ^ m)⁻¹ := by group
      _ = 1 * (r ^ m)⁻¹ := by rw [h1]
      _ = (r ^ m)⁻¹ := one_mul _
  have hrm_inv : (r ^ m)⁻¹ = r ^ m := by
    rw [← inv_pow, inv_eq_self_of_orderOf_eq_two hr2]
  have hρm : (ρ : G) ^ m = r ^ m := by rw [h2, hrm_inv]
  rcases Nat.even_or_odd m with heven | hodd
  · have hm2 : m % 2 = 0 := Nat.not_odd_iff.mp (Nat.not_odd_iff_even.mpr heven)
    have hrm : r ^ m = 1 := by rw [← pow_mod_orderOf r m, hr2, hm2, pow_zero]
    have hρm1 : (ρ : G) ^ m = 1 := by rw [hρm, hrm]
    have hdvd : orderOf (ρ : G) ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hρm1
    rw [hordρ] at hdvd
    have hmpos' : 0 < m := by rw [hm]; exact orderOf_pos _
    have hge : Nat.card A ≤ m := Nat.le_of_dvd hmpos' hdvd
    have hltm : m < Nat.card A := by rw [hm]; exact hlt
    omega
  · have hm2 : m % 2 = 1 := Nat.odd_iff.mp hodd
    have hrm : r ^ m = r := by rw [← pow_mod_orderOf r m, hr2, hm2, pow_one]
    have hmem : (ρ : G) ^ m ∈ A := A.pow_mem hρA m
    rw [hρm, hrm] at hmem
    exact hrA hmem

theorem m6e8_normalizer_mem {K A : Subgroup G} {c : G} (hAK : A ≤ K) (hAcyc : IsCyclic A)
    (hAord : ∀ k ∈ K, k ∉ A → orderOf k < Nat.card A) (hcK : c ∈ normalizer (K : Set G)) :
    c ∈ normalizer (A : Set G) := by
  classical
  haveI : IsCyclic ↥A := hAcyc
  obtain ⟨ρ, hρgen⟩ := IsCyclic.exists_generator (α := ↥A)
  have hρA : (ρ : G) ∈ A := ρ.2
  have hordρ : orderOf (ρ : G) = Nat.card A := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hρgen]
  have hconj : ∀ d ∈ normalizer (K : Set G), ∀ a ∈ A, d * a * d⁻¹ ∈ A := by
    intro d hd a ha
    have hdρK : d * (ρ : G) * d⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hd (ρ : G)).mp (hAK hρA)
    have hdρA : d * (ρ : G) * d⁻¹ ∈ A := by
      by_contra hnot
      have hlt := hAord _ hdρK hnot
      have heq : orderOf (d * (ρ : G) * d⁻¹) = Nat.card A := by
        simpa only [MulAut.conj_apply, hordρ] using
          MulEquiv.orderOf_eq (MulAut.conj d) (ρ : G)
      omega
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hρgen ⟨a, ha⟩)
    have hna : a = (ρ : G) ^ n := by
      have := congrArg Subtype.val hn
      simpa using this.symm
    rw [hna]
    have hconjzpow : d * (ρ : G) ^ n * d⁻¹ = (d * (ρ : G) * d⁻¹) ^ n := by
      simpa only [MulAut.conj_apply] using map_zpow (MulAut.conj d) (ρ : G) n
    rw [hconjzpow]
    exact A.zpow_mem hdρA n
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hconj c hcK h hh
  · intro hh
    have hcinv : c⁻¹ ∈ normalizer (K : Set G) := inv_mem hcK
    have hmem := hconj c⁻¹ hcinv (c * h * c⁻¹) hh
    have heq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
    rwa [heq] at hmem

theorem m6e8_sq_mem {C K A : Subgroup G} {c : G} (hKC : K ≤ C) (hKi : K.relIndex C = 2)
    (hAK : A ≤ K) (hAi : A.relIndex K = 2) (hcC : c ∈ C) (hcK : c ∉ K) (hc2 : c * c = 1)
    (hcKn : c ∈ normalizer (K : Set G)) (hcAn : c ∈ normalizer (A : Set G)) :
    ∀ x ∈ C, x ^ 2 ∈ A := by
  intro x hxC
  have hKi' : (K.subgroupOf C).index = 2 := hKi
  haveI : (K.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hKi'
  have hAi' : (A.subgroupOf K).index = 2 := hAi
  haveI : (A.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hAi'
  by_cases hxK : x ∈ K
  · have h := Subgroup.pow_index_mem (A.subgroupOf K) (⟨x, hxK⟩ : ↥K)
    rw [hAi'] at h
    simpa using (Subgroup.mem_subgroupOf.mp h)
  · have hcxK : c * x ∈ K := by
      have h := CFSG.GF2Type.Aschbacher1976Common.mul_mem_of_notMem_of_index_two
        (X := ↥C) (H := K.subgroupOf C) hKi'
        (x := (⟨c, hcC⟩ : ↥C)) (y := (⟨x, hxC⟩ : ↥C))
        (by simpa only [Subgroup.mem_subgroupOf] using hcK)
        (by simpa only [Subgroup.mem_subgroupOf] using hxK)
      simpa using (Subgroup.mem_subgroupOf.mp h)
    set k : G := c * x with hk
    have hkK : k ∈ K := hcxK
    have hxk : x = c * k := by
      rw [hk, ← mul_assoc, hc2, one_mul]
    have hdK : c * k * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hcKn k).mp hkK
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_left hc2
    have hx2 : x ^ 2 = (c * k * c⁻¹) * k := by
      rw [hxk, pow_two, hcinv]
      group
    have hdA_iff : c * k * c⁻¹ ∈ A ↔ k ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hcAn k).symm
    by_cases hkA : k ∈ A
    · have hdA : c * k * c⁻¹ ∈ A := hdA_iff.mpr hkA
      rw [hx2]
      exact A.mul_mem hdA hkA
    · have hdA : c * k * c⁻¹ ∉ A := fun hd => hkA (hdA_iff.mp hd)
      have h := CFSG.GF2Type.Aschbacher1976Common.mul_mem_of_notMem_of_index_two
        (X := ↥K) (H := A.subgroupOf K) hAi'
        (x := (⟨c * k * c⁻¹, hdK⟩ : ↥K)) (y := (⟨k, hkK⟩ : ↥K))
        (by simpa only [Subgroup.mem_subgroupOf] using hdA)
        (by simpa only [Subgroup.mem_subgroupOf] using hkA)
      rw [hx2]
      simpa using (Subgroup.mem_subgroupOf.mp h)

theorem m6e8_normalizer_fixes {C K A : Subgroup G} {r c g : G} (hKC : K ≤ C)
    (hKi : K.relIndex C = 2) (hAK : A ≤ K) (hAcyc : IsCyclic A) (hAi : A.relIndex K = 2)
    (h4 : 4 ∣ Nat.card A) (hAord : ∀ k ∈ K, k ∉ A → orderOf k < Nat.card A)
    (hrK : r ∈ K) (hr2 : orderOf r = 2) (hrZ : ∀ k ∈ K, k * r = r * k)
    (hcC : c ∈ C) (hcK : c ∉ K) (hc2 : c * c = 1) (hg : g ∈ normalizer (C : Set G)) :
    g * r = r * g := by
  classical
  have hcKn : c ∈ normalizer (K : Set G) := m6e8_normalizer_of_index_two hKC hKi hcC
  have hcAn : c ∈ normalizer (A : Set G) := m6e8_normalizer_mem hAK hAcyc hAord hcKn
  have hsq : ∀ x ∈ C, x ^ 2 ∈ A := m6e8_sq_mem hKC hKi hAK hAi hcC hcK hc2 hcKn hcAn
  have hrA : r ∈ A := m6e8_central_mem hAK hAcyc hAord hrK hr2 hrZ
  obtain ⟨ζ, hζA, hζord⟩ := m6e8_exists_orderOf_four hAcyc h4
  have hζ2sq : (ζ ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, ← hζord]
    exact pow_orderOf_eq_one ζ
  have hζ2ne : ζ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hζord] at hdvd
    omega
  have hζ2ord : orderOf (ζ ^ 2) = 2 := orderOf_eq_prime hζ2sq hζ2ne
  have hζ2A : ζ ^ 2 ∈ A := A.pow_mem hζA 2
  have hζ2eq : r = ζ ^ 2 := m6e8_unique_involution hAcyc hrA hζ2A hr2 hζ2ord
  have hζC : ζ ∈ C := hKC (hAK hζA)
  have hgζC : g * ζ * g⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hg ζ).mp hζC
  have hgrgA : g * r * g⁻¹ ∈ A := by
    have h := hsq (g * ζ * g⁻¹) hgζC
    have h2 : (g * ζ * g⁻¹) ^ 2 = g * r * g⁻¹ := by
      rw [hζ2eq, pow_two, pow_two]
      group
    rwa [h2] at h
  have hgrg2 : orderOf (g * r * g⁻¹) = 2 := by
    simpa only [MulAut.conj_apply, hr2] using MulEquiv.orderOf_eq (MulAut.conj g) r
  have hgrge : g * r * g⁻¹ = r := m6e8_unique_involution hAcyc hgrgA hrA hgrg2 hr2
  calc g * r = (g * r * g⁻¹) * g := by group
    _ = r * g := by rw [hgrge]

end CFSG.OddStandard.SmallF3.Omega
