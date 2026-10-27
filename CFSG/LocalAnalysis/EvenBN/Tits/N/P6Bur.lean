module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime {K : Subgroup G} {x : G} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ K) (hb : x ^ b ∈ K) : x ∈ K := by
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime hab
  have h1 : (x ^ a) ^ u * (x ^ b) ^ v = x := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (a : ℤ) * u + b * v = 1 := by linarith [huv]
    rw [this, zpow_one]
  rw [← h1]
  exact mul_mem (zpow_mem ha u) (zpow_mem hb v)

theorem pow_relIndex_mem_of_normal {K H : Subgroup G} [(K.subgroupOf H).Normal] {x : G}
    (hx : x ∈ H) : x ^ K.relIndex H ∈ K := by
  have h := Subgroup.pow_index_mem (K.subgroupOf H) ⟨x, hx⟩
  exact (Subgroup.mem_subgroupOf.1 h)

theorem exists_isPGroup_three_not_mem [Finite G] {K H : Subgroup G} [(K.subgroupOf H).Normal]
    {y j : G} (hyH : y ∈ H) (hKH : K ≤ H) (hjK : j ∈ K) (hy3 : IsPGroup 3 (zpowers y))
    (hyK : y ∉ K) :
    ∃ m : ℕ, ∃ e : ℕ, ¬ 3 ∣ m ∧ (j⁻¹ * y) ^ (m * 3 ^ e) = 1 ∧ (j⁻¹ * y) ^ m ∉ K := by
  have hcH : j⁻¹ * y ∈ H := mul_mem (inv_mem (hKH hjK)) hyH
  have hn0 : orderOf (j⁻¹ * y) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨e, m, hm3, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 3 (by norm_num)
  refine ⟨m, e, hm3, ?_, ?_⟩
  · rw [mul_comm, ← hnm]
    exact pow_orderOf_eq_one _
  · intro hmem
    let K' := K.subgroupOf H
    have hjK' : (⟨j, hKH hjK⟩ : H) ∈ K' := hjK
    have hym : y ^ m ∈ K := by
      have h1 : (⟨j⁻¹ * y, hcH⟩ : H) ^ m ∈ K' := hmem
      have h2 : QuotientGroup.mk (s := K') (⟨j⁻¹ * y, hcH⟩ : H) = QuotientGroup.mk ⟨y, hyH⟩ := by
        rw [QuotientGroup.eq_iff_div_mem]
        have : (⟨j⁻¹ * y, hcH⟩ : H) / ⟨y, hyH⟩ = ⟨j, hKH hjK⟩⁻¹ := Subtype.ext (by simp)
        rw [this]
        exact K'.inv_mem hjK'
      have h3 : QuotientGroup.mk (s := K') ((⟨y, hyH⟩ : H) ^ m) = 1 := by
        rw [QuotientGroup.mk_pow, ← h2, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact h1
      rw [QuotientGroup.eq_one_iff] at h3
      exact h3
    obtain ⟨b, hb⟩ := hy3 ⟨y, mem_zpowers y⟩
    have hyb : y ^ (3 ^ b) = 1 := congrArg Subtype.val hb
    have hcop : m.Coprime (3 ^ b) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3)))
    exact hyK (mem_of_pow_mem_of_coprime hcop hym (by rw [hyb]; exact K.one_mem))

theorem exists_isSylowOf_ge [Finite G] {p : ℕ} [Fact p.Prime] {Q K : Subgroup G} (hQ : IsPGroup p Q)
    (hQK : Q ≤ K) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQK hq⟩, hS (Subgroup.mem_subgroupOf.2 hq), rfl⟩

theorem mem_of_isPGroup_three_of_card [Finite G] {I Λ : Subgroup G} (hΛI : Λ ≤ I)
    (hΛn : ∀ i ∈ I, ∀ l ∈ Λ, i * l * i⁻¹ ∈ Λ) (h9 : 9 ∣ Nat.card Λ)
    (hI : Nat.card I ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2) {g : G} (hg : g ∈ I) (hg3 : IsPGroup 3 (zpowers g)) :
    g ∈ Λ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, hgP⟩ := exists_isSylowOf_ge hg3 (zpowers_le.2 hg)
  have hnorm : I ≤ normalizer (Λ : Set G) := fun i hi =>
    mem_normalizer_iff.2 fun l => ⟨fun hl => hΛn i hi l hl, fun hl => by
      have := hΛn i⁻¹ (inv_mem hi) _ hl
      simpa [mul_assoc] using this⟩
  have hPΛ := isSylowOf_of_fusionIsSylowIn
    (fusionIsSylowIn_inf_of_normal (fusionIsSylowIn_of_isSylowOf hP) hΛI hnorm)
  have hcΛ := hPΛ.card_eq
  have hcP := hP.card_eq
  have hΛpos : 0 < Nat.card Λ := Nat.card_pos
  have hPdvd : Nat.card P ∣ Nat.card I := Subgroup.card_dvd_of_le hP.le
  have hP9 : Nat.card P ≤ 9 := by
    rw [hcP]
    set v := (Nat.card I).factorization 3 with hv
    by_contra hlt
    push Not at hlt
    have hv3 : 3 ≤ v := by
      by_contra h
      have h2 : v ≤ 2 := by omega
      have h3 : 3 ^ v ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      omega
    have h27 : 3 ^ 3 ∣ 3 ^ v := pow_dvd_pow 3 hv3
    have hPdvd' : 3 ^ v ∣ Nat.card I := by rw [← hcP]; exact hPdvd
    have := (h27.trans hPdvd').trans hI
    norm_num at this
  have hΛ9 : 9 ≤ Nat.card ↥(P ⊓ Λ) := by
    rw [hcΛ]
    have : 3 ^ 2 ∣ Nat.card Λ := by norm_num; exact h9
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hΛpos.ne').1 this
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (Nat.card Λ).factorization 3 := Nat.pow_le_pow_right (by norm_num) h2
  have hPeq : P ⊓ Λ = P :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (hP9.trans hΛ9)
  have hPle : P ≤ Λ := hPeq ▸ inf_le_right
  exact hPle (hgP (mem_zpowers g))

theorem exists_normal_odd_subgroup [Finite G] {Hh C Wst : Subgroup G} (hCH : C ≤ Hh)
    (hCn : ∀ h ∈ Hh, ∀ c ∈ C, h * c * h⁻¹ ∈ C) (hW : fusionIsSylowIn 2 Wst C)
    (hcent : ∀ c ∈ C, ∀ w ∈ Wst, c * w = w * c) :
    ∃ N : Subgroup G, N ≤ C ∧ Odd (Nat.card N) ∧ (∀ h ∈ Hh, ∀ n ∈ N, h * n * h⁻¹ ∈ N) ∧
      ∀ o ∈ C, Odd (orderOf o) → o ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := isSylowOf_of_fusionIsSylowIn hW
  have hPc : normalizer ((P : Subgroup ↥C) : Set ↥C) ≤ centralizer ((P : Subgroup ↥C) : Set ↥C) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpW : (p : G) ∈ Wst := by
      rw [← hP]
      exact ⟨p, hp, rfl⟩
    exact Subtype.ext (hcent x.1 x.2 p.1 hpW).symm
  let τ : ↥C →* ↥(P : Subgroup ↥C) := MonoidHom.transferSylow P hPc
  have hnd : ¬ 2 ∣ Nat.card τ.ker := MonoidHom.not_dvd_card_ker_transferSylow P hPc
  let N : Subgroup G := τ.ker.map C.subtype
  have hNodd : Odd (Nat.card N) := by
    have : Nat.card N = Nat.card τ.ker :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [this]
    exact Nat.odd_iff.2 (by omega)
  have hodd_mem : ∀ o ∈ C, Odd (orderOf o) → o ∈ N := by
    intro o hoC hoodd
    have h1 : orderOf (τ ⟨o, hoC⟩) ∣ orderOf (⟨o, hoC⟩ : ↥C) := orderOf_map_dvd τ _
    have h2 : orderOf (⟨o, hoC⟩ : ↥C) = orderOf o := Subgroup.orderOf_mk o hoC
    obtain ⟨k, hk⟩ := P.isPGroup' (τ ⟨o, hoC⟩)
    have h3 : orderOf (τ ⟨o, hoC⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime (2 ^ k) (orderOf o) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hoodd)
    have h4 : orderOf (τ ⟨o, hoC⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h3) (h2 ▸ h1)
    have h5 : τ ⟨o, hoC⟩ = 1 := orderOf_eq_one_iff.1 h4
    exact ⟨⟨o, hoC⟩, h5, rfl⟩
  refine ⟨N, Subgroup.map_subtype_le _, hNodd, fun h hh n hn => ?_, hodd_mem⟩
  obtain ⟨m, hmK, rfl⟩ := hn
  have hmC : (m : G) ∈ C := m.2
  have hconj : h * (m : G) * h⁻¹ ∈ C := hCn h hh _ hmC
  refine hodd_mem _ hconj ?_
  change Odd (orderOf (h * (m : G) * h⁻¹))
  have h1 : orderOf (h * (m : G) * h⁻¹) = orderOf (m : G) := by
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective (m : G)
    simpa [MulAut.conj_apply] using this
  rw [h1, Subgroup.orderOf_coe]
  have hdvd : orderOf m ∣ Nat.card τ.ker := Subgroup.orderOf_dvd_natCard τ.ker hmK
  exact (Nat.odd_iff.2 (by omega) : Odd (Nat.card τ.ker)).of_dvd_nat hdvd

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
