module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LieType.BorelTits.HeringCharTwoGeneral

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem false_of_sylow_of_conj_eq_mul (S : Sylow 2 G) {t z : G} (htS : t ∈ (S : Subgroup G))
    (htc : ∀ s ∈ (S : Subgroup G), s * t = t * s) (hzS : z ∈ (S : Subgroup G))
    (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s) (ht : orderOf t = 2) (hz : orderOf z = 2)
    (hzt : z ≠ t)
    (hZ : ∀ w ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), s * w = w * s) → orderOf w = 2 →
      w = z ∨ w = t ∨ w = z * t)
    (hnot : ∀ g : G, g⁻¹ * t * g ≠ z) {g : G} (hg : g⁻¹ * t * g = z * t) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by
    have h := ((orderOf_eq_prime_iff (p := 2)).1 ht).1
    rwa [pow_two] at h
  have hz2 : z * z = 1 := by
    have h := ((orderOf_eq_prime_iff (p := 2)).1 hz).1
    rwa [pow_two] at h
  have hztc : z * t = t * z := (hzc t htS).symm
  have hzt2sq : (z * t) * (z * t) = 1 := by
    have h1 : (z * t) * (z * t) = z * (t * z) * t := by group
    rw [h1, ← hztc]
    calc z * (z * t) * t = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, mul_one]
  have hztne : z * t ≠ 1 := by
    intro h
    apply hzt
    calc z = z * (t * t) := by rw [ht2, mul_one]
      _ = (z * t) * t := by group
      _ = 1 * t := by rw [h]
      _ = t := one_mul t
  have hztord : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime ?_ hztne
    rwa [pow_two]
  have hztcent : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := by
    intro s hs
    have h1 := hzc s hs
    have h2 := htc s hs
    calc s * (z * t) = (s * z) * t := by group
      _ = (z * s) * t := by rw [h1]
      _ = z * (s * t) := by rw [mul_assoc]
      _ = z * (t * s) := by rw [h2]
      _ = (z * t) * s := by group
  have hcommg : ∀ y ∈ (S : Subgroup G), y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y := by
    intro y hy
    rw [hg]
    exact hztcent y hy
  obtain ⟨n, hnN, hnconj⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer S t g
    (Subgroup.mem_centralizer_iff.mpr htc) (Subgroup.mem_centralizer_iff.mpr hcommg)
  have hnt : n⁻¹ * t * n = z * t := by rw [← hnconj]; exact hg
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 (S : Subgroup G)
      (normalizer ((S : Subgroup G) : Set G)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨Subgroup.le_normalizer, S.isPGroup', ?_⟩
    intro hdvd
    exact Sylow.not_dvd_index S
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
  obtain ⟨k, m, hmodd, hmord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp (orderOf_pos n))
  have hmne : m ≠ 0 := by rintro rfl; simp [Odd] at hmodd
  have hmdvd : m ∣ orderOf n := by rw [hmord]; exact dvd_mul_left m (2 ^ k)
  have hordnm : orderOf (n ^ m) = 2 ^ k := by
    rw [orderOf_pow_of_dvd hmne hmdvd, hmord, mul_comm (2 ^ k) m,
      Nat.mul_div_right (2 ^ k) (Nat.pos_of_ne_zero hmne)]
  have hzpg : IsPGroup 2 ↥(Subgroup.zpowers (n ^ m)) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hordnm])
  have hNB : Subgroup.zpowers (n ^ m) ≤ normalizer ((S : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hnN m)
  have hsup2 : IsPGroup 2 ↥((S : Subgroup G) ⊔ Subgroup.zpowers (n ^ m)) :=
    IsPGroup.to_sup_of_normal_left' S.isPGroup' hzpg hNB
  have hsup_le : (S : Subgroup G) ⊔ Subgroup.zpowers (n ^ m) ≤
      normalizer ((S : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hNB
  have hnmS : n ^ m ∈ (S : Subgroup G) := by
    have heq := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hSylN le_sup_left hsup_le hsup2
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (n ^ m))
  have hnm_zt : (n ^ m)⁻¹ * (z * t) * (n ^ m) = z * t := by
    have h := hztcent (n ^ m) hnmS
    calc (n ^ m)⁻¹ * (z * t) * (n ^ m) = (n ^ m)⁻¹ * ((z * t) * (n ^ m)) := by rw [mul_assoc]
      _ = (n ^ m)⁻¹ * ((n ^ m) * (z * t)) := by rw [← h]
      _ = z * t := by rw [inv_mul_cancel_left]
  have hφz_mem : n⁻¹ * z * n ∈ (S : Subgroup G) :=
    (Subgroup.mem_normalizer_iff''.mp hnN z).mp hzS
  have hφz_cent : ∀ s ∈ (S : Subgroup G), s * (n⁻¹ * z * n) = (n⁻¹ * z * n) * s := by
    intro s hs
    have hs' : n * s * n⁻¹ ∈ (S : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hnN s).mp hs
    have h := hzc (n * s * n⁻¹) hs'
    calc s * (n⁻¹ * z * n) = n⁻¹ * ((n * s * n⁻¹) * z) * n := by group
      _ = n⁻¹ * (z * (n * s * n⁻¹)) * n := by rw [h]
      _ = (n⁻¹ * z * n) * s := by group
  have hφz_ord : orderOf (n⁻¹ * z * n) = 2 := by
    rw [show n⁻¹ * z * n = (MulAut.conj n⁻¹) z by simp,
      MulEquiv.orderOf_eq, hz]
  rcases hZ (n⁻¹ * z * n) hφz_mem hφz_cent hφz_ord with hz' | ht' | hzt'
  ·
    have hφzt : n⁻¹ * (z * t) * n = t := by
      have h2 : n⁻¹ * (z * t) * n = (n⁻¹ * z * n) * (n⁻¹ * t * n) := by group
      rw [h2, hz', hnt]
      calc z * (z * t) = (z * z) * t := by group
        _ = t := by rw [hz2, one_mul]
    have hnz : n * z = z * n := by
      have h := congrArg (fun y => n * y) hz'
      rw [show n * (n⁻¹ * z * n) = z * n from by group] at h
      exact h.symm
    have hn2z : n ^ 2 * z = z * n ^ 2 := by
      rw [pow_two]
      calc n * n * z = n * (n * z) := by rw [mul_assoc]
        _ = n * (z * n) := by rw [hnz]
        _ = z * (n * n) := by
            have h1 : n * (z * n) = n * z * n := by rw [mul_assoc]
            rw [h1, hnz, mul_assoc]
    have hφ2t : (n ^ 2)⁻¹ * t * (n ^ 2) = t := by
      have h1 : (n ^ 2)⁻¹ * t * (n ^ 2) = n⁻¹ * (n⁻¹ * t * n) * n := by
        rw [pow_two, mul_inv_rev]
        group
      rw [h1, hnt, hφzt]
    have hn2t : n ^ 2 * t = t * n ^ 2 := by
      have hφ2t' : n⁻¹ * n⁻¹ * t * (n * n) = t := by
        have h := hφ2t
        rwa [pow_two, mul_inv_rev] at h
      have h5 : t * (n * n) = (n * n) * t := by
        calc t * (n * n) = n * n * (n⁻¹ * n⁻¹ * t * (n * n)) := by group
          _ = n * n * t := by rw [hφ2t']
          _ = (n * n) * t := by rw [mul_assoc]
      rw [pow_two]
      exact h5.symm
    obtain ⟨j, hj⟩ := hmodd
    have hone : n ^ m = (n ^ 2) ^ j * n := by rw [hj, pow_add, pow_one, pow_mul]
    have hcz : (n ^ 2) ^ j * z = z * (n ^ 2) ^ j :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.pow_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr hn2z) j)
    have hct : (n ^ 2) ^ j * t = t * (n ^ 2) ^ j :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.pow_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr hn2t) j)
    have hczt : (n ^ 2) ^ j * (z * t) = (z * t) * (n ^ 2) ^ j := by
      calc (n ^ 2) ^ j * (z * t) = ((n ^ 2) ^ j * z) * t := by rw [mul_assoc]
        _ = (z * (n ^ 2) ^ j) * t := by rw [hcz]
        _ = z * ((n ^ 2) ^ j * t) := by rw [mul_assoc]
        _ = z * (t * (n ^ 2) ^ j) := by rw [hct]
        _ = (z * t) * (n ^ 2) ^ j := by rw [← mul_assoc]
    have hconj : ((n ^ 2) ^ j)⁻¹ * (z * t) * ((n ^ 2) ^ j) = z * t := by
      calc ((n ^ 2) ^ j)⁻¹ * (z * t) * ((n ^ 2) ^ j)
          = ((n ^ 2) ^ j)⁻¹ * ((z * t) * ((n ^ 2) ^ j)) := by rw [mul_assoc]
        _ = ((n ^ 2) ^ j)⁻¹ * (((n ^ 2) ^ j) * (z * t)) := by rw [← hczt]
        _ = z * t := by rw [inv_mul_cancel_left]
    have hpow : (n ^ m)⁻¹ * (z * t) * (n ^ m) = t := by
      rw [hone]
      calc ((n ^ 2) ^ j * n)⁻¹ * (z * t) * ((n ^ 2) ^ j * n)
          = n⁻¹ * (((n ^ 2) ^ j)⁻¹ * (z * t) * ((n ^ 2) ^ j)) * n := by
            rw [mul_inv_rev]; group
        _ = n⁻¹ * (z * t) * n := by rw [hconj]
        _ = t := hφzt
    have hzt_eq : z * t = t := hnm_zt.symm.trans hpow
    have hz1 : z = 1 := by
      calc z = z * (t * t) := by rw [ht2, mul_one]
        _ = (z * t) * t := by group
        _ = t * t := by rw [hzt_eq]
        _ = 1 := ht2
    rw [hz1] at hz
    simp at hz
  ·
    have hφ2t : (n ^ 2)⁻¹ * t * (n ^ 2) = z := by
      have h1 : (n ^ 2)⁻¹ * t * (n ^ 2) = n⁻¹ * (n⁻¹ * t * n) * n := by
        rw [pow_two, mul_inv_rev]
        group
      rw [h1, hnt]
      have h2 : n⁻¹ * (z * t) * n = (n⁻¹ * z * n) * (n⁻¹ * t * n) := by group
      rw [h2, ht', hnt]
      calc t * (z * t) = (t * z) * t := by group
        _ = (z * t) * t := by rw [← hztc]
        _ = z * (t * t) := by group
        _ = z := by rw [ht2, mul_one]
    exact hnot (n ^ 2) hφ2t
  ·
    have h1 : n⁻¹ * (z * t) * n = 1 := by
      have h2 : n⁻¹ * (z * t) * n = (n⁻¹ * z * n) * (n⁻¹ * t * n) := by group
      rw [h2, hzt', hnt]
      exact hzt2sq
    have h3 : orderOf (n⁻¹ * (z * t) * n) = 2 := by
      rw [show n⁻¹ * (z * t) * n = (MulAut.conj n⁻¹) (z * t) by simp,
        MulEquiv.orderOf_eq, hztord]
    rw [h1] at h3
    exact absurd h3 (by simp)

theorem exists_shear_of_lt {t z : G} (ht : orderOf t = 2) {S P : Subgroup G}
    (hS : IsSylowTwoIn S (centralizer ({t} : Set G))) (hP : IsPGroup 2 P) (hSP : S < P)
    (hzS : z ∈ S) (hzc : ∀ s ∈ S, s * z = z * s) (hz : orderOf z = 2) (hzt : z ≠ t)
    (hZ : ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z ∨ w = t ∨ w = z * t)
    (hnot : ∀ g : G, g⁻¹ * t * g ≠ z) :
    ∃ x ∈ P, x ∈ normalizer (S : Set G) ∧ x⁻¹ * t * x = z * t ∧ x⁻¹ * z * x = z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC : S ≤ centralizer ({t} : Set G) := hS.1
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({t} : Set G)) := by
    obtain ⟨-, Q, hQ⟩ := hS
    exact ⟨Q, by rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSC]⟩
  have ht2 : t * t = 1 := by
    have h := ((orderOf_eq_prime_iff (p := 2)).1 ht).1
    rwa [pow_two] at h
  have htc : ∀ s ∈ S, s * t = t * s := by
    intro s hs
    exact (Subgroup.mem_centralizer_iff.mp (hSC hs) t (Set.mem_singleton t)).symm
  have htS : t ∈ S := by
    have hztg : IsPGroup 2 ↥(Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
    have htN : t ∈ normalizer (S : Set G) :=
      Subgroup.centralizer_le_normalizer (S : Set G)
        (Subgroup.mem_centralizer_iff.mpr (fun s hs => htc s hs))
    have hsup2 : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers t) :=
      IsPGroup.to_sup_of_normal_left' hSyl.isPGroup hztg (Subgroup.zpowers_le.mpr htN)
    have hsup_le : S ⊔ Subgroup.zpowers t ≤ centralizer ({t} : Set G) :=
      sup_le hSC (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    have heq := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hSyl le_sup_left hsup_le hsup2
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨x, hxP, hxS, hxN⟩ :=
    CFSG.LieType.BorelTits.exists_mem_normalizer_of_lt_pGroup' (p := 2) hP hSP
  have hx_nc : x ∉ centralizer ({t} : Set G) := by
    intro hxC
    have hx2g : IsPGroup 2 ↥(Subgroup.zpowers x) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨x, hxP⟩
      rw [Subgroup.orderOf_mk] at hk
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hsup2 : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers x) :=
      IsPGroup.to_sup_of_normal_left' hSyl.isPGroup hx2g (Subgroup.zpowers_le.mpr hxN)
    have hsup_le : S ⊔ Subgroup.zpowers x ≤ centralizer ({t} : Set G) :=
      sup_le hSC (Subgroup.zpowers_le.mpr hxC)
    have heq := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hSyl le_sup_left hsup_le hsup2
    exact hxS (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hz2 : z * z = 1 := by
    have h := ((orderOf_eq_prime_iff (p := 2)).1 hz).1
    rwa [pow_two] at h
  have hztc : z * t = t * z := (hzc t htS).symm
  have hzt2sq : (z * t) * (z * t) = 1 := by
    have h1 : (z * t) * (z * t) = z * (t * z) * t := by group
    rw [h1, ← hztc]
    calc z * (z * t) * t = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, mul_one]
  have hztne : z * t ≠ 1 := by
    intro h
    apply hzt
    calc z = z * (t * t) := by rw [ht2, mul_one]
      _ = (z * t) * t := by group
      _ = 1 * t := by rw [h]
      _ = t := one_mul t
  have hztord : orderOf (z * t) = 2 := by
    refine orderOf_eq_prime ?_ hztne
    rwa [pow_two]
  have hxt_mem : x⁻¹ * t * x ∈ S := (Subgroup.mem_normalizer_iff''.mp hxN t).mp htS
  have hxt_cent : ∀ s ∈ S, s * (x⁻¹ * t * x) = (x⁻¹ * t * x) * s := by
    intro s hs
    have hs' : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxN s).mp hs
    have h := htc (x * s * x⁻¹) hs'
    calc s * (x⁻¹ * t * x) = x⁻¹ * ((x * s * x⁻¹) * t) * x := by group
      _ = x⁻¹ * (t * (x * s * x⁻¹)) * x := by rw [h]
      _ = (x⁻¹ * t * x) * s := by group
  have hxt_ord : orderOf (x⁻¹ * t * x) = 2 := by
    rw [show x⁻¹ * t * x = (MulAut.conj x⁻¹) t by simp,
      MulEquiv.orderOf_eq, ht]
  have hxnt : x⁻¹ * t * x ≠ t := by
    intro h
    apply hx_nc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : x * t * x⁻¹ = t := by
      calc x * t * x⁻¹ = x * (x⁻¹ * t * x) * x⁻¹ := by rw [h]
        _ = t := by group
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [h']
  have hxt_eq : x⁻¹ * t * x = z * t := by
    rcases hZ (x⁻¹ * t * x) hxt_mem hxt_cent hxt_ord with h | h | h
    · exact absurd h (hnot x)
    · exact absurd h hxnt
    · exact h
  have hxz_mem : x⁻¹ * z * x ∈ S := (Subgroup.mem_normalizer_iff''.mp hxN z).mp hzS
  have hxz_cent : ∀ s ∈ S, s * (x⁻¹ * z * x) = (x⁻¹ * z * x) * s := by
    intro s hs
    have hs' : x * s * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hxN s).mp hs
    have h := hzc (x * s * x⁻¹) hs'
    calc s * (x⁻¹ * z * x) = x⁻¹ * ((x * s * x⁻¹) * z) * x := by group
      _ = x⁻¹ * (z * (x * s * x⁻¹)) * x := by rw [h]
      _ = (x⁻¹ * z * x) * s := by group
  have hxz_ord : orderOf (x⁻¹ * z * x) = 2 := by
    rw [show x⁻¹ * z * x = (MulAut.conj x⁻¹) z by simp,
      MulEquiv.orderOf_eq, hz]
  have hxz_eq : x⁻¹ * z * x = z := by
    rcases hZ (x⁻¹ * z * x) hxz_mem hxz_cent hxz_ord with h | h | h
    · exact h
    · have h1 : x * t * x⁻¹ = z := by
        calc x * t * x⁻¹ = x * (x⁻¹ * z * x) * x⁻¹ := by rw [h]
          _ = z := by group
      exact absurd (by simpa using h1) (hnot x⁻¹)
    · have h1 : x⁻¹ * (z * t) * x = 1 := by
        have h2 : x⁻¹ * (z * t) * x = (x⁻¹ * z * x) * (x⁻¹ * t * x) := by group
        rw [h2, h, hxt_eq]
        exact hzt2sq
      have h3 : orderOf (x⁻¹ * (z * t) * x) = 2 := by
        rw [show x⁻¹ * (z * t) * x = (MulAut.conj x⁻¹) (z * t) by simp,
          MulEquiv.orderOf_eq, hztord]
      rw [h1] at h3
      exact absurd h3 (by simp)
  exact ⟨x, hxP, hxN, hxt_eq, hxz_eq⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
