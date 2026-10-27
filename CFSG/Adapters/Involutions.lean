module

public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Adapters

theorem odd_orderOf_of_mem_oddCore {G : Type*} [Group G] [Finite G] {m : G}
    (hm : m ∈ oddCore G) : Odd (orderOf m) := by
  have hle : oddCore G ≤ CFSG.pPrimeCore 2 G :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hdvd : orderOf m ∣ Nat.card (CFSG.pPrimeCore 2 G) := by
    have := orderOf_dvd_natCard (⟨m, hle hm⟩ : CFSG.pPrimeCore 2 G)
    rwa [Subgroup.orderOf_mk] at this
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := G)))

theorem not_mem_oddCore_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) : t ∉ oddCore G := fun h => by
  have := odd_orderOf_of_mem_oddCore h
  rw [ht] at this
  exact (Nat.not_odd_iff_even.mpr even_two) this

theorem eq_centralizer_mul_oddCore {G : Type*} [Group G] [Finite G] {z : G}
    (hz : z * z = 1)
    (hcen : (QuotientGroup.mk z : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G))
    (g : G) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), ∃ k ∈ oddCore G, g = c * k := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  set w := g⁻¹ * z * g with hw_def
  have hwz : (QuotientGroup.mk w : G ⧸ oddCore G) = QuotientGroup.mk z := by
    have h := Subgroup.mem_center_iff.mp hcen (QuotientGroup.mk g)
    rw [hw_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc, ← h,
      ← mul_assoc, inv_mul_cancel, one_mul]
  set m := z⁻¹ * w with hm_def
  have hmK : m ∈ oddCore G := QuotientGroup.eq.mp hwz.symm
  have hwm : w = z * m := by rw [hm_def, ← mul_assoc, mul_inv_cancel, one_mul]
  have hww : w * w = 1 := by
    rw [hw_def]
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz]; group
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hzm : z * m * z⁻¹ = m⁻¹ := by
    rw [hm_def, mul_inv_rev, inv_inv, hwinv, hzinv]
    calc z * (z * w) * z = (z * z) * w * z := by group
      _ = w * z := by rw [hz, one_mul]
  obtain ⟨k, hk⟩ := odd_orderOf_of_mem_oddCore hmK
  set n := m ^ (k + 1) with hn_def
  have hnK : n ∈ oddCore G := Subgroup.pow_mem _ hmK _
  have hnn : n * n = m := by
    rw [hn_def, ← pow_add, show k + 1 + (k + 1) = orderOf m + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hzn : z * n * z⁻¹ = n⁻¹ := by
    rw [hn_def, ← conj_pow, hzm, inv_pow]
  have hzn' : z * n = n⁻¹ * z := by
    rw [← hzn, hzinv, mul_assoc, mul_assoc, hz, mul_one]
  refine ⟨g * n⁻¹, ?_, n, hnK, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have key : n * w * n⁻¹ = z := by
    rw [hwm, ← hnn]
    calc n * (z * (n * n)) * n⁻¹ = n * (z * n) := by group
      _ = z := by rw [hzn']; group
  rw [hw_def] at key
  have hz' : z = (g * n⁻¹) * z * (g * n⁻¹)⁻¹ := by
    calc z = g * (n⁻¹ * (n * (g⁻¹ * z * g) * n⁻¹) * n) * g⁻¹ := by group
      _ = (g * n⁻¹) * z * (g * n⁻¹)⁻¹ := by rw [key]; group
  nth_rewrite 2 [hz']
  group

theorem isolated_of_weakClosure {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {z : G}
    (hzZ : z ∈ Subgroup.centralizer (S : Set G)) (hz : z * z = 1)
    (hwc : ∀ g : G, g⁻¹ * z * g ∈ (S : Subgroup G) → g⁻¹ * z * g = z) (g : G)
    (hcomm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) : g * z * g⁻¹ = z := by
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hSC : (S : Subgroup G) ≤ C := fun s hs => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hzZ s hs
  have hyC : g * z * g⁻¹ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm
  set Y : C := ⟨g * z * g⁻¹, hyC⟩
  have hY2 : Y ^ 2 = 1 := by
    rw [sq]
    ext
    change g * z * g⁻¹ * (g * z * g⁻¹) = 1
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hYp : IsPGroup 2 (Subgroup.zpowers Y) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by simpa using hY2) : orderOf Y ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hYp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q (S.subtype hSC)
  have hmem : MulAut.conj c • Y ∈ ((c • Q : Sylow 2 C) : Subgroup C) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ (Subgroup.mem_zpowers Y))
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  have hcz : (c : G) * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hmem' : ((c : G) * g)⁻¹⁻¹ * z * ((c : G) * g)⁻¹ ∈ (S : Subgroup G) := by
    simpa [Y, MulAut.smul_def, mul_assoc] using hmem
  have key := hwc _ hmem'
  simp only [inv_inv, mul_inv_rev] at key
  calc g * z * g⁻¹ = (c : G)⁻¹ * ((c : G) * g * z * (g⁻¹ * (c : G)⁻¹)) * c := by group
    _ = (c : G)⁻¹ * z * c := by rw [key]
    _ = z := by rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]

theorem brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ≠ 1 ∧
      (QuotientGroup.mk t : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) :=
  ⟨fun h => not_mem_oddCore_of_orderOf_eq_two ht_ord ((QuotientGroup.eq_one_iff t).mp h),
    CFSG.BrauerSuzuki.brauer_suzuki n hn P hquat t ht_mem ht_ord⟩

theorem glauberman_zStar {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (z : (S : Subgroup G)) (hzZ : z ∈ Subgroup.center (S : Subgroup G)) (hz : orderOf z = 2)
    (hwc : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z) :
    (∀ g : G, ∃ c ∈ Subgroup.centralizer ({(z : G)} : Set G), ∃ k ∈ oddCore G, g = c * k) ∧
      (QuotientGroup.mk (z : G) : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) := by
  let : Fintype G := Fintype.ofFinite G
  have hzord : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hzz : (z : G) * z = 1 := by
    have := pow_orderOf_eq_one (z : G)
    rwa [hzord, sq] at this
  have hzC : (z : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := Subgroup.mem_center_iff.mp hzZ ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hz1 : (z : G) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G z hz1 hzz
    (fun g hcomm => isolated_of_weakClosure S hzC hzz hwc g hcomm)
  have hNK : N ≤ oddCore G := le_sSup ⟨hNn, hNodd⟩
  have hcen : (QuotientGroup.mk (z : G) : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := hNK (hN g⁻¹)
    rw [inv_inv, ← QuotientGroup.eq_one_iff] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one] at h1
    calc (QuotientGroup.mk g : G ⧸ oddCore G) * QuotientGroup.mk (z : G)
        = QuotientGroup.mk g * ((QuotientGroup.mk g)⁻¹ * QuotientGroup.mk (z : G) *
            QuotientGroup.mk g) := by rw [h1]
      _ = QuotientGroup.mk (z : G) * QuotientGroup.mk g := by group
  exact ⟨eq_centralizer_mul_oddCore hzz hcen, hcen⟩

end CFSG.Adapters
