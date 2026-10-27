module

public import CFSG.GH74.GLS.TwoThin.Central
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GH74.GLS.Bg.Iii2.L41

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Stage1.Thm3.Sec4

theorem exists_pow_conj_commute_aux {H : Type*} [Group H] {z s c : H} (hz : z * z = 1) (hs : s * s = 1)
    (hc : c = z * s * z⁻¹ * s⁻¹) (hodd : Odd (orderOf c)) :
    ∃ k : ℕ, ((c ^ k) * z * (c ^ k)⁻¹) * s = s * ((c ^ k) * z * (c ^ k)⁻¹) := by
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hc' : c = z * s * z * s := by rw [hc, hz', hs']
  have h1 : z * c * z⁻¹ = c⁻¹ := by
    rw [hc', hz']
    have : (z * s * z * s)⁻¹ = s * z * s * z := by
      simp only [mul_inv_rev, hz', hs']
      group
    rw [this]
    calc z * (z * s * z * s) * z = (z * z) * s * z * s * z := by group
      _ = s * z * s * z := by rw [hz, one_mul]
  have h2 : s * c * s⁻¹ = c⁻¹ := by
    rw [hc', hs']
    have : (z * s * z * s)⁻¹ = s * z * s * z := by
      simp only [mul_inv_rev, hz', hs']
      group
    rw [this]
    calc s * (z * s * z * s) * s = s * z * s * z * (s * s) := by group
      _ = s * z * s * z := by rw [hs, mul_one]
  have h3 : s * z * s⁻¹ = z * c := by
    rw [hc', hs']
    calc s * z * s = z * z * s * z * s := by rw [hz, one_mul]
      _ = z * (z * s * z * s) := by group
  obtain ⟨r, hr⟩ := hodd
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = 2 * r * (r + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : H, e = c ^ k := ⟨_, rfl⟩
  refine ⟨k, ?_⟩
  rw [← he]
  have hez : z * e * z⁻¹ = e⁻¹ := by
    rw [he, ← conj_pow, h1, inv_pow]
  have hes : s * e * s⁻¹ = e⁻¹ := by
    rw [he, ← conj_pow, h2, inv_pow]
  have hce : c * e = e * c := by
    rw [he, ← pow_succ, ← pow_succ']
  have hpow : c ^ (4 * k + 1) = 1 := by
    have : 4 * k + 1 = (2 * r + 1) * (4 * r ^ 2 + 6 * r + 1) := by
      rw [hk]; ring
    rw [this, pow_mul, ← hr, pow_orderOf_eq_one, one_pow]
  have h4 : c * e * e * e * e = 1 := by
    have h7 : c * e * e * e * e = c ^ (4 * k + 1) := by
      have : c ^ (4 * k + 1) = c * (c ^ k * c ^ k * c ^ k * c ^ k) := by
        rw [pow_succ', show 4 * k = k + k + k + k by ring, pow_add, pow_add, pow_add]
      rw [this, he]
      group
    rw [h7, hpow]
  have hez' : z * e * z = e⁻¹ := by
    have := hez
    rwa [hz'] at this
  have hezz : e * z = z * e⁻¹ := by
    calc e * z = (z * z) * e * z := by rw [hz, one_mul]
      _ = z * (z * e * z) := by group
      _ = z * e⁻¹ := by rw [hez']
  have hezz' : e⁻¹ * z = z * e := by
    calc e⁻¹ * z = z * e * z * z := by rw [hez']
      _ = z * e := by rw [mul_assoc, hz, mul_one]
  have hes' : s * e * s = e⁻¹ := by
    have := hes
    rwa [hs'] at this
  have hse : s * e = e⁻¹ * s := by
    calc s * e = s * e * (s * s) := by rw [hs, mul_one]
      _ = (s * e * s) * s := by group
      _ = e⁻¹ * s := by rw [hes']
  have hsei : s * e⁻¹ = e * s := by
    have h6 : s * e⁻¹ * s = e := by
      calc s * e⁻¹ * s = (s * e * s)⁻¹ := by simp only [mul_inv_rev, hs', mul_assoc]
        _ = e := by rw [hes', inv_inv]
    calc s * e⁻¹ = s * e⁻¹ * (s * s) := by rw [hs, mul_one]
      _ = (s * e⁻¹ * s) * s := by group
      _ = e * s := by rw [h6]
  have hsz : s * z = z * c * s := by
    have h8 : s * z * s = z * c := by
      have := h3
      rwa [hs'] at this
    calc s * z = s * z * (s * s) := by rw [hs, mul_one]
      _ = (s * z * s) * s := by group
      _ = z * c * s := by rw [h8]
  have key : e⁻¹ * e⁻¹ = e * c * e := by
    have h9 : c * e * e = e⁻¹ * e⁻¹ := by
      have h10 : (c * e * e) * (e * e) = 1 := by simpa only [mul_assoc] using h4
      rw [← mul_inv_rev]
      exact eq_inv_of_mul_eq_one_left h10
    rw [← h9, hce]
  show (e * z * e⁻¹) * s = s * (e * z * e⁻¹)
  calc (e * z * e⁻¹) * s = (e * z) * e⁻¹ * s := by group
    _ = (z * e⁻¹) * e⁻¹ * s := by rw [hezz]
    _ = z * (e⁻¹ * e⁻¹) * s := by group
    _ = z * (e * c * e) * s := by rw [key]
    _ = (z * e) * c * (e * s) := by group
    _ = (e⁻¹ * z) * c * (s * e⁻¹) := by rw [← hezz', hsei]
    _ = e⁻¹ * (z * c * s) * e⁻¹ := by group
    _ = e⁻¹ * (s * z) * e⁻¹ := by rw [← hsz]
    _ = (e⁻¹ * s) * z * e⁻¹ := by group
    _ = (s * e) * z * e⁻¹ := by rw [← hse]
    _ = s * (e * z * e⁻¹) := by group

theorem exists_pow_conj_commute {H : Type*} [Group H] {z s : H} (hz : z * z = 1) (hs : s * s = 1)
    (hodd : Odd (orderOf (z * s * z⁻¹ * s⁻¹))) :
    ∃ k : ℕ, ((z * s * z⁻¹ * s⁻¹) ^ k * z * ((z * s * z⁻¹ * s⁻¹) ^ k)⁻¹) * s =
      s * ((z * s * z⁻¹ * s⁻¹) ^ k * z * ((z * s * z⁻¹ * s⁻¹) ^ k)⁻¹) :=
  exists_pow_conj_commute_aux hz hs rfl hodd


variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_sylow {H Q : Subgroup G} (hQ : IsSylowOf 2 Q H) {t : G} (htH : t ∈ H)
    (ht : orderOf t = 2) : ∃ g ∈ H, g * t * g⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : IsPGroup 2 ↥(zpowers (⟨t, htH⟩ : ↥H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht]; norm_num)
  obtain ⟨S, hS⟩ := hW.exists_le_sylow
  have hS' : IsSylowOf 2 ((S : Subgroup ↥H).map H.subtype) H := ⟨S, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQ.exists_mem_conj hS'
  refine ⟨k⁻¹, H.inv_mem hk, ?_⟩
  have hmem : t ∈ (S : Subgroup ↥H).map H.subtype :=
    ⟨⟨t, htH⟩, hS (Subgroup.mem_zpowers _), rfl⟩
  have := (hconj t).1 hmem
  simpa [mul_assoc] using this

theorem exists_sylow_central_lift' {x : G} {K : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hZ : center (↥K ⧸ pPrimeCore 2 ↥K) ≠ ⊥) :
    ∃ Q : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 Q (CxK x K) ∧ ∃ u : G, u ∈ Q ∧
      (∀ q ∈ Q, u * q = q * u) ∧ u ∈ centralLift K ∧ orderOf u = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzc, hz2⟩ : ∃ z ∈ center (↥K ⧸ pPrimeCore 2 ↥K), orderOf z = 2 := by
    have hne : center (↥K ⧸ pPrimeCore 2 ↥K) ≠ ⊥ := hZ
    have heven : 2 ∣ Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) := by
      by_contra hn
      have hodd : Odd (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) := by
        rw [← Nat.not_even_iff_odd]
        exact fun h => hn (even_iff_two_dvd.mp h)
      have hle : center (↥K ⧸ pPrimeCore 2 ↥K) ≤ pPrimeCore 2 (↥K ⧸ pPrimeCore 2 ↥K) :=
        le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
      rw [pPrimeCore_quotient_eq_bot] at hle
      exact hne (le_bot_iff.mp hle)
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 heven
    exact ⟨c, c.2, by rw [orderOf_coe]; exact hc⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) z
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  set k₂ : ↥K := k ^ b with hk₂
  have hk₂2 : k₂ ^ (2 ^ a) = 1 := by
    rw [hk₂, ← pow_mul, mul_comm, ← hab]
    exact pow_orderOf_eq_one k
  have hz2' : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hmk₂ : QuotientGroup.mk' (pPrimeCore 2 ↥K) k₂ = z := by
    rw [hk₂, map_pow, hk]
    obtain ⟨m, rfl⟩ := hb
    rw [pow_succ, pow_mul, hz2', one_pow, one_mul]
  have hu₀c : (k₂ : G) ∈ centralLift K := by
    refine mem_centralLift.mpr ⟨k₂.2, ?_⟩
    rw [hmk₂]
    exact hzc
  have hu₀D : (k₂ : G) ∈ CxK x K :=
    Subgroup.mem_inf.mpr ⟨by simpa using hK.1 k₂.2, centralLift_le_centralizerSection K hu₀c⟩
  let u₀D : ↥(CxK x K) := ⟨k₂, hu₀D⟩
  have h2G : (k₂ : G) ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val hk₂2
    simpa using this
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers u₀D) :=
    isPGroup_zpowers_of_pow_eq_one (n := a) (Subtype.ext (by simpa using h2G))
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP2
  set Q : Subgroup G := (S : Subgroup ↥(CxK x K)).map (CxK x K).subtype with hQdef
  have hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (CxK x K) := ⟨S, rfl⟩
  have hu₀Q : (k₂ : G) ∈ Q := ⟨u₀D, hS (Subgroup.mem_zpowers u₀D), rfl⟩
  have hQp : IsPGroup 2 ↥Q := hQ.isPGroup
  have hnil : Group.IsNilpotent ↥Q := hQp.isNilpotent
  let N₀ : Subgroup ↥Q := (centralLift K).subgroupOf Q
  have hN₀ : N₀.Normal := ⟨fun n hn g => by
    have hqs : (g : G) ∈ centralizerSection K (pPrimeCoreOf 2 K) := (hQ.le g.2).2
    exact Subgroup.mem_subgroupOf.mpr (by
      simpa using conj_mem_centralLift (Subgroup.mem_subgroupOf.mp hn) hqs)⟩
  have hN₀ne : N₀ ≠ ⊥ := by
    intro h
    have hmem : (⟨k₂, hu₀Q⟩ : ↥Q) ∈ N₀ := Subgroup.mem_subgroupOf.mpr hu₀c
    rw [h, Subgroup.mem_bot] at hmem
    have hk21 : k₂ = 1 := Subtype.ext (by simpa using congrArg Subtype.val hmem)
    rw [hk21, map_one] at hmk₂
    have : orderOf z = 1 := by rw [← hmk₂]; exact orderOf_one
    omega
  have hX := Group.IsNilpotent.inf_center_ne_bot_of_normal hN₀ne
  obtain ⟨w, hw, hwo⟩ := CFSG.ABGLocalTools.exists_mem_orderOf_eq_two
    (hQp.to_subgroup (N₀ ⊓ center ↥Q)) hX
  refine ⟨Q, hQ, (w : G), w.2, fun q hq => ?_,
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1, ?_⟩
  · have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨q, hq⟩
    exact (congrArg Subtype.val this).symm
  · rw [Subgroup.orderOf_coe]
    exact hwo

end CFSG.GH74.GLS.Bg.Iii2.L41
