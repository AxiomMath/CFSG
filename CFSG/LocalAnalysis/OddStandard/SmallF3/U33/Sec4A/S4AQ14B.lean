module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem q14_card_pCore {M : Subgroup G} {e : ℕ} (hM : Nat.card M = 2 ^ e * 3) :
    Nat.card M = 3 * Nat.card (CFSG.Open.pCoreOf 2 M) ∨
      Nat.card M = 6 * Nat.card (CFSG.Open.pCoreOf 2 M) := by
  let P : Sylow 2 ↥M := Classical.arbitrary _
  have hPcard : Nat.card P = 2 ^ e := by
    rw [Sylow.card_eq_multiplicity P]
    congr 1
    rw [hM, Nat.factorization_mul_apply_of_coprime
        ((by norm_num : Nat.Coprime 2 3).pow_left e),
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
  have hPindex : (P : Subgroup ↥M).index = 3 := by
    have hcard := Subgroup.card_mul_index (P : Subgroup ↥M)
    rw [hPcard, hM] at hcard
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) e) hcard
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  have hQM : Q ≤ M := pCoreOf_two_le M
  let Qm : Subgroup ↥M := Q.subgroupOf M
  have hcardQm : Nat.card Qm = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hQp : IsPGroup 2 Q := pCoreOf_two_isPGroup M
  have hQm_dvd6 : Qm.index ∣ 6 := by
    have hdvd : (P : Subgroup ↥M).normalCore.index ∣ ((P : Subgroup ↥M).index).factorial :=
      Subgroup.index_normalCore_dvd_factorial_index _
    rw [hPindex] at hdvd
    norm_num at hdvd
    have hle : (P : Subgroup ↥M).normalCore ≤ Qm := by
      intro y hy
      have hQ'le : ((P : Subgroup ↥M).normalCore).map M.subtype ≤ Q := by
        refine le_pCoreOf_two (Subgroup.map_subtype_le _) ?_ ?_
        · intro n hn q hq
          obtain ⟨y', hy', rfl⟩ := hq
          refine Subgroup.mem_map.mpr ⟨⟨n, hn⟩ * y' * ⟨n, hn⟩⁻¹,
            (Subgroup.normalCore_normal ((P : Subgroup ↥M))).conj_mem y' hy' ⟨n, hn⟩, ?_⟩
          simp
        · exact ((P.isPGroup' : IsPGroup 2 (P : Subgroup ↥M)).map M.subtype).to_le
            (Subgroup.map_mono (Subgroup.normalCore_le ((P : Subgroup ↥M))))
      exact hQ'le (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    exact (Subgroup.index_dvd_of_le hle).trans hdvd
  have h3dvd : 3 ∣ Qm.index := by
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hcard' : Nat.card Qm * Qm.index = Nat.card ↥M := Subgroup.card_mul_index Qm
    have h3M : 3 ∣ Nat.card Qm * Qm.index := by
      rw [hcard', hM]
      exact dvd_mul_left 3 (2 ^ e)
    have h3' : 3 ∣ 2 ^ k * Qm.index := by
      rwa [hcardQm, hk] at h3M
    rcases (Nat.prime_three.dvd_mul.mp h3') with h | h
    · exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
    · exact h
  have hidx : Qm.index = 3 ∨ Qm.index = 6 := by
    obtain ⟨b, hb⟩ := h3dvd
    obtain ⟨c, hc⟩ := hQm_dvd6
    have hbc : b * c = 2 := by
      have h : 3 * (b * c) = 3 * 2 := by
        calc 3 * (b * c) = (3 * b) * c := by ring
          _ = Qm.index * c := by rw [← hb]
          _ = 6 := hc.symm
          _ = 3 * 2 := by norm_num
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
    rcases Nat.prime_two.eq_one_or_self_of_dvd b ⟨c, hbc.symm⟩ with hb1 | hb2
    · left; rw [hb, hb1, mul_one]
    · right; rw [hb, hb2]
  have hcard' : Nat.card Qm * Qm.index = Nat.card ↥M := Subgroup.card_mul_index Qm
  rcases hidx with hidx | hidx
  · left
    rw [← hcard', hidx, hcardQm]
    exact Nat.mul_comm _ _
  · right
    rw [← hcard', hidx, hcardQm]
    exact Nat.mul_comm _ _

private lemma zpowers_eq_one_or_self {t : G} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
  intro x hx
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  have hord : orderOf t = 2 := orderOf_eq_prime (by simpa [pow_two] using ht2) ht1
  rw [← zpow_mod_orderOf t k, hord, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem q14_eq_zpowers_of_cent {P : Subgroup G} (hP : IsPGroup 2 P) {t : G} (htP : t ∈ P)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) (hc : ∀ x ∈ P, x * t = t * x → x ∈ zpowers t) :
    P = zpowers t := by
  haveI : Nontrivial ↥P :=
    ⟨⟨t, htP⟩, 1, fun h => ht1 (by simpa using congrArg Subtype.val h)⟩
  haveI hZnt : Nontrivial (Subgroup.center ↥P) := IsPGroup.center_nontrivial hP
  obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center ↥P)
  have hz_mem : (z : ↥P) ∈ Subgroup.center ↥P := z.2
  have hz_ne' : (z : ↥P) ≠ 1 := fun h => hz_ne (Subtype.ext h)
  have hcomm' : t * ((z : ↥P) : G) = ((z : ↥P) : G) * t := by
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz_mem (⟨t, htP⟩ : ↥P))
    simpa using this
  have hzG : ((z : ↥P) : G) ∈ zpowers t := hc _ (z : ↥P).2 hcomm'.symm
  have hzG_ne : ((z : ↥P) : G) ≠ 1 := fun h => hz_ne' (Subtype.coe_injective h)
  have hzt : (⟨t, htP⟩ : ↥P) = (z : ↥P) := by
    rcases zpowers_eq_one_or_self ht2 ht1 ((z : ↥P) : G) hzG with h | h
    · exact absurd h hzG_ne
    · exact Subtype.ext h.symm
  have ht_center : (⟨t, htP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [hzt]; exact hz_mem
  apply le_antisymm
  · intro x hx
    exact hc x hx (by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp ht_center (⟨x, hx⟩ : ↥P))
      simpa using this)
  · exact Subgroup.zpowers_le.mpr htP

theorem q14_inf_eq_bot_of_sigma3 {K D : Subgroup G} (e : ↥K ≃* Equiv.Perm (Fin 3))
    (hD : IsPGroup 2 D) (hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D) : D ⊓ K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxD, hxK⟩ := Subgroup.mem_inf.mp hx
  have hfin : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 2 = 1 →
      ∃ π : Equiv.Perm (Fin 3), π ^ 3 = 1 ∧ π ≠ 1 ∧
        (π * σ * π⁻¹ * σ⁻¹) ^ 3 = 1 ∧ π * σ * π⁻¹ * σ⁻¹ ≠ 1 := by decide +kernel
  obtain ⟨k, hk⟩ := hD.exists_pow_pow_eq_one (⟨x, hxD⟩ : ↥D)
  have hxg : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  set σ : Equiv.Perm (Fin 3) := e ⟨x, hxK⟩ with hσdef
  have hσpow : σ ^ (2 ^ k) = 1 := by
    rw [hσdef]
    have hK : (⟨x, hxK⟩ : ↥K) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxg)
    rw [← map_pow, hK, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hx1
    have h1 : e ⟨x, hxK⟩ = e 1 := by rw [← hσdef, h, map_one]
    have hsub : (⟨x, hxK⟩ : ↥K) = 1 := e.injective h1
    simpa using congrArg Subtype.val hsub
  have hσ2 : σ ^ 2 = 1 := by
    have hord2 : orderOf σ ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hσpow
    have hord6 : orderOf σ ∣ 6 := by
      simpa [Fintype.card_perm, Fintype.card_fin, Nat.factorial] using
        (orderOf_dvd_card : orderOf σ ∣ Fintype.card (Equiv.Perm (Fin 3)))
    have hcop : (orderOf σ).Coprime 3 :=
      ((by norm_num : Nat.Coprime 2 3).pow_left k).coprime_dvd_left hord2
    exact orderOf_dvd_iff_pow_eq_one.mp
      (hcop.dvd_of_dvd_mul_left (by simpa using hord6))
  obtain ⟨π, hπ3, hπ1, hπc3, hπc1⟩ := hfin σ hσ1 hσ2
  obtain ⟨kK, hkK⟩ := e.surjective π
  set kg : G := (kK : G) with hkgdef
  have hkgK : kg ∈ K := by simpa [hkgdef] using kK.2
  set c : G := kg * x * kg⁻¹ * x⁻¹ with hcdef
  have hcD : c ∈ D := by
    rw [hcdef]
    exact Subgroup.mul_mem _ (hKD kg hkgK x hxD) (Subgroup.inv_mem _ hxD)
  have hcK : c ∈ K := by
    rw [hcdef]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hkgK hxK) (Subgroup.inv_mem _ hkgK))
      (Subgroup.inv_mem _ hxK)
  have hec : e ⟨c, hcK⟩ = π * σ * π⁻¹ * σ⁻¹ := by
    have hsub : (⟨c, hcK⟩ : ↥K) = kK * ⟨x, hxK⟩ * kK⁻¹ * ⟨x, hxK⟩⁻¹ := by
      ext; simp [hcdef, hkgdef]
    rw [hsub]
    simp only [map_mul, map_inv, hkK, ← hσdef]
  have hc3K : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, hec, hπc3, map_one]
  have hcG3 : c ^ 3 = 1 := by simpa using congrArg Subtype.val hc3K
  have hcG1 : c ≠ 1 := by
    intro h
    apply hπc1
    have hsub : (⟨c, hcK⟩ : ↥K) = 1 := Subtype.ext (by simpa using h)
    rw [← hec, hsub, map_one]
  have h2dvd : 2 ∣ orderOf c := by
    have hne : (⟨c, hcD⟩ : ↥D) ≠ 1 := fun h =>
      hcG1 (by simpa using congrArg Subtype.val h)
    have := hD.dvd_orderOf (g := (⟨c, hcD⟩ : ↥D)) hne
    simpa [Subgroup.orderOf_mk] using this
  exact absurd (h2dvd.trans (orderOf_dvd_iff_pow_eq_one.mpr hcG3)) (by norm_num)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
