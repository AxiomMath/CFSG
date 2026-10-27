module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L218

open Subgroup

theorem mem_of_odd_orderOf {H : Type} [Group H] (K : Subgroup H) [K.Normal] (hK : K.index = 2)
    (q : H) (hq : Odd (orderOf q)) : q ∈ K := by
  obtain ⟨m, hm⟩ := hq
  have h1 : q ^ 2 ∈ K := hK ▸ Subgroup.pow_index_mem K q
  have h2 : q = (q ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    have h3 : 2 * (m + 1) = orderOf q + 1 := by omega
    rw [h3, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [h2]
  exact pow_mem h1 _

theorem sylow3_card {G : Type} [Group G] [Finite G] (P : Sylow 3 G)
    (h : Nat.card G = 9 ∨ Nat.card G = 36 ∨ Nat.card G = 45 ∨ Nat.card G = 180) :
    Nat.card P = 9 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  have hidx := Subgroup.card_mul_index (P : Subgroup G)
  have hnd := P.not_dvd_index
  rw [hk] at hidx
  have hk3 : k ≤ 2 := by
    by_contra hlt
    have hlt' : 3 ≤ k := by omega
    have h27 : 27 ∣ 3 ^ k := by
      have := pow_dvd_pow 3 hlt'
      simpa using this
    have h27' : 27 ∣ Nat.card G := by
      rw [← hidx]
      exact Dvd.dvd.mul_right h27 _
    omega
  interval_cases k
  · omega
  · omega
  · simpa using hk

theorem subsingleton_sylow3 {H : Type} [Group H] [Finite H]
    (hH : Nat.card H = 9 ∨ Nat.card H = 45) : Subsingleton (Sylow 3 H) := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hP : Nat.card P = 9 := sylow3_card P (by omega)
  have hmod := card_sylow_modEq_one 3 H
  have hdvd := P.card_dvd_index
  have hidx := Subgroup.card_mul_index (P : Subgroup H)
  rw [hP] at hidx
  have hn : Nat.card (Sylow 3 H) = 1 := by
    rcases hH with h | h
    · have : (P : Subgroup H).index = 1 := by omega
      rw [this] at hdvd
      exact Nat.dvd_one.mp hdvd
    · have : (P : Subgroup H).index = 5 := by omega
      rw [this] at hdvd
      have h5 : Nat.card (Sylow 3 H) ∈ Nat.divisors 5 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have h5' : Nat.divisors 5 = {1, 5} := by decide
      rw [h5'] at h5
      simp only [Finset.mem_insert, Finset.mem_singleton] at h5
      rcases h5 with h5 | h5
      · exact h5
      · rw [h5] at hmod
        exact absurd hmod (by decide)
  exact (Nat.card_eq_one_iff_unique.mp hn).1

theorem endgame {G : Type} [Group G] [Finite G] (u t z : G) (hu : orderOf u = 3)
    (htu : t * u * t⁻¹ = u⁻¹) (hz : orderOf z = 2) (hzu : z * u = u * z)
    (hC2 : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 T →
      Nat.card T ≤ 2)
    (hcard : Nat.card G = 36 ∨ Nat.card G = 180) :
    Nat.card (Sylow 3 G) = 1 := by
  classical
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG4 : Nat.card G = 9 ∨ Nat.card G = 36 ∨ Nat.card G = 45 ∨ Nat.card G = 180 := by omega
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  have hmemC : ∀ g : G, g ∈ C ↔ g * u = u * g := fun g => Subgroup.mem_centralizer_singleton_iff
  have hzC : z ∈ C := (hmemC z).mpr hzu
  have hzp : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have huP : u ∈ (P : Subgroup G) := hP (Subgroup.mem_zpowers u)
  have hPC : ∀ Q : Sylow 3 G, u ∈ (Q : Subgroup G) → (Q : Subgroup G) ≤ C := by
    intro Q hQ q hq
    have hQ9 := sylow3_card Q hG4
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (G := (Q : Subgroup G)) (by rw [hQ9]; norm_num)
    rw [hmemC]
    have := hcomm.is_comm.comm (⟨q, hq⟩ : (Q : Subgroup G)) ⟨u, hQ⟩
    exact congrArg Subtype.val this
  let z' : C := ⟨z, hzC⟩
  have hz'ord : orderOf z' = 2 := by rw [← hz]; exact (Subgroup.orderOf_coe z').symm
  have hz2 : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'ord]; norm_num)
  obtain ⟨T, hT⟩ := hz2.exists_le_sylow
  have hTcard : Nat.card T = 2 := by
    have hge : 2 ≤ Nat.card T := by
      have := Subgroup.card_le_of_le hT
      rwa [Nat.card_zpowers, hz'ord] at this
    have hle : Nat.card T ≤ 2 := by
      obtain ⟨k, hk⟩ := T.2.exists_card_eq
      have hmap : IsPGroup 2 ((T : Subgroup C).map C.subtype) :=
        IsPGroup.of_card (n := k) (by
          rw [Subgroup.card_map_of_injective C.subtype_injective]; exact hk)
      have := hC2 ((T : Subgroup C).map C.subtype) (by rintro _ ⟨c, _, rfl⟩; exact c.2) hmap
      rwa [Subgroup.card_map_of_injective C.subtype_injective] at this
    omega
  have hmin : (Nat.card C).minFac = 2 := by
    rw [Nat.minFac_eq_two_iff]
    have := orderOf_dvd_natCard z'
    rwa [hz'ord] at this
  have hcyc : IsCyclic T := isCyclic_of_prime_card (p := 2) hTcard
  have hNC : Subgroup.normalizer (T : Set C) ≤ Subgroup.centralizer (T : Set C) :=
    IsCyclic.normalizer_le_centralizer hmin hcyc
  let K : Subgroup C := (MonoidHom.transferSylow T hNC).ker
  have hKn : K.Normal := MonoidHom.normal_ker _
  have hcompl := MonoidHom.ker_transferSylow_isComplement' T hNC
  have hCK : Nat.card K * 2 = Nat.card C := by
    have := hcompl.card_mul_card
    rwa [hTcard] at this
  have hKodd : ¬ 2 ∣ Nat.card K := MonoidHom.not_dvd_card_ker_transferSylow T hNC
  have hKidx : K.index = 2 := by
    have h1 := Subgroup.card_mul_index K
    have hpos : 0 < Nat.card K := Nat.card_pos
    rw [← hCK] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  let M : Subgroup G := K.map C.subtype
  have hMcard : Nat.card M = Nat.card K := Subgroup.card_map_of_injective C.subtype_injective
  have hPM : ∀ Q : Sylow 3 G, u ∈ (Q : Subgroup G) → (Q : Subgroup G) ≤ M := by
    intro Q hQ q hq
    have hqC : q ∈ C := hPC Q hQ hq
    have hodd : Odd (orderOf (⟨q, hqC⟩ : C)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp Q.2 ⟨q, hq⟩
      rw [Subgroup.orderOf_mk]
      have hk' : orderOf q = 3 ^ k := by rw [← hk, Subgroup.orderOf_mk]
      rw [hk']
      exact Odd.pow (by decide)
    have hqK : (⟨q, hqC⟩ : C) ∈ K := mem_of_odd_orderOf K hKidx _ hodd
    exact ⟨⟨q, hqC⟩, hqK, rfl⟩
  have hP9 : Nat.card P = 9 := sylow3_card P hG4
  have h9M : 9 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (hPM P huP)
    rw [hP9, hMcard] at this
    exact this
  have hCG : Nat.card C ∣ Nat.card G := Subgroup.card_subgroup_dvd_card C
  have hM945 : Nat.card M = 9 ∨ Nat.card M = 45 := by
    rw [hMcard]
    obtain ⟨k, hk⟩ := h9M
    rw [← hCK, hk] at hCG
    rcases hcard with hc | hc
    · rw [hc] at hCG
      have hle := Nat.le_of_dvd (by norm_num) hCG
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> omega
    · rw [hc] at hCG
      have hle := Nat.le_of_dvd (by norm_num) hCG
      have hk10 : k ≤ 10 := by omega
      interval_cases k <;> omega
  have hsub : Subsingleton (Sylow 3 M) := subsingleton_sylow3 hM945
  have hunique : ∀ Q₂ Q₃ : Sylow 3 G, u ∈ (Q₂ : Subgroup G) → u ∈ (Q₃ : Subgroup G) → Q₂ = Q₃ :=
    fun Q₂ Q₃ h₂ h₃ =>
      Sylow.subtype_injective (hP := hPM Q₂ h₂) (hQ := hPM Q₃ h₃) (Subsingleton.elim _ _)
  have hnorm : ∀ g : G, g⁻¹ * u * g ∈ (P : Subgroup G) →
      g ∈ Subgroup.normalizer (P : Set G) := by
    intro g hg
    rw [← Sylow.smul_eq_iff_mem_normalizer]
    apply hunique
    · rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, map_inv] using hg
    · exact huP
  have hCP : C ≤ Subgroup.normalizer (P : Set G) := by
    intro c hc
    apply hnorm
    have : c⁻¹ * u * c = u := by
      have hcu : c * u = u * c := (hmemC c).mp hc
      rw [mul_assoc, ← hcu, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact huP
  have htinv : t⁻¹ * u * t = u⁻¹ := by
    have h1 : t * u⁻¹ * t⁻¹ = u := by
      have := congrArg (fun a => a⁻¹) htu
      simpa [mul_assoc] using this
    calc t⁻¹ * u * t = t⁻¹ * (t * u⁻¹ * t⁻¹) * t := by rw [h1]
      _ = u⁻¹ := by group
  have htP : t ∈ Subgroup.normalizer (P : Set G) := by
    apply hnorm
    rw [htinv]
    exact inv_mem huP
  let N : Subgroup G := C ⊔ Subgroup.zpowers t
  have hNP : N ≤ Subgroup.normalizer (P : Set G) :=
    sup_le hCP (Subgroup.zpowers_le.mpr htP)
  have htC : t ∉ C := by
    intro htC
    have hcu : t * u = u * t := (hmemC t).mp htC
    have h1 : u = u⁻¹ := by
      calc u = t * u * t⁻¹ := by rw [hcu]; group
        _ = u⁻¹ := htu
    have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h1
    have := orderOf_dvd_of_pow_eq_one hu2
    rw [hu] at this
    omega
  have htN : t ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hCN : C < N := lt_of_le_of_ne le_sup_left (fun h => htC (h ▸ htN))
  have hNC2 : 2 * Nat.card C ≤ Nat.card N := by
    obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le (le_of_lt hCN)
    have hd1 : d ≠ 1 := by
      intro hd1
      rw [hd1, mul_one] at hd
      exact (ne_of_lt hCN) (Subgroup.eq_of_le_of_card_ge (le_of_lt hCN) (by rw [hd]))
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hd
      exact (Nat.card_pos (α := N)).ne' hd
    calc 2 * Nat.card C ≤ d * Nat.card C := Nat.mul_le_mul_right _ (by omega)
      _ = Nat.card C * d := by ring
      _ = Nat.card N := hd.symm
  have hn := Sylow.card_eq_index_normalizer P
  have hdvd := Subgroup.index_dvd_of_le hNP
  have hmod := card_sylow_modEq_one 3 G
  have hNidx := Subgroup.index_mul_card N
  have hK9 : 9 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos h9M
  have hN36 : 36 ≤ Nat.card N := by omega
  have hNi0 : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hidx5 : N.index ≤ 5 := by
    have h1 : N.index * 36 ≤ 180 :=
      le_trans (Nat.mul_le_mul_left _ hN36) (by rw [hNidx]; omega)
    omega
  have hnN : Nat.card (Sylow 3 G) ∣ N.index := by rw [hn]; exact hdvd
  have hn5 : Nat.card (Sylow 3 G) ≤ 5 := le_trans (Nat.le_of_dvd hNi0 hnN) hidx5
  have hnpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have hCev : 2 ∣ Nat.card C := ⟨Nat.card K, by omega⟩
  have hCNd : Nat.card C ∣ Nat.card N := Subgroup.card_dvd_of_le (le_of_lt hCN)
  have hNev : 2 ∣ Nat.card N := dvd_trans hCev hCNd
  have hmod' : Nat.card (Sylow 3 G) % 3 = 1 := hmod
  have hn14 : Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by omega
  rcases hn14 with h | h
  · exact h
  · exfalso
    rw [h] at hnN
    have h4 : N.index = 4 := by omega
    rw [h4] at hNidx
    omega

end L218

end CFSG.GH74.GLS.Bg.TwoGroups
