module

public import CFSG.GH74.Uniqueness.Section15HeringEnd2
public import CFSG.Assembly.OddCoreElimination.TwoGroups
public import CFSG.GH74.Uniqueness.Section15HeringEnd3
public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω] {p : ℕ} {ω : Ω} {K P : Subgroup G}

theorem EndHyp.three_dvd_card_of_normal_four [Finite G] (h : EndHyp G Ω p ω K P)
    (S : Sylow 2 G) (huniq : ∀ R : Sylow 2 G, AtMostOneCentralInvolution (R : Subgroup G))
    {V : Subgroup G} (hVS : V ≤ S) (hSV : (S : Subgroup G) ≤ normalizer (V : Set G))
    (hV2 : ∀ x ∈ V, x ^ 2 = 1) (hV4 : Nat.card V = 4) : 3 ∣ Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVne : V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV4
    omega
  obtain ⟨z, hzV, hz2⟩ :=
    CFSG.Assembly.Dichotomy.exists_involution_inf_subgroupCenter S.isPGroup' hVS hSV hVne
  have hzVV : z ∈ V := hzV.1
  have hzS : z ∈ (S : Subgroup G) := hzV.2.1
  have hzc : ∀ s ∈ (S : Subgroup G), z * s = s * z := fun s hs =>
    (mem_centralizer_iff.mp hzV.2.2 s hs).symm
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  obtain ⟨u, huV, huz⟩ : ∃ u ∈ V, u ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show V ≤ zpowers z from hcon)
    rw [hV4, Nat.card_zpowers, hz2] at this
    omega
  have hu1 : u ≠ 1 := fun h1 => huz (h1 ▸ one_mem _)
  have huz' : u ≠ z := fun h1 => huz (h1 ▸ mem_zpowers z)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (hV2 u huV) hu1
  have huu : u * u = 1 := by rw [← pow_two, hV2 u huV]
  have hzz : z * z = 1 := by rw [← pow_two, hV2 z hzVV]
  have huS : u ∈ (S : Subgroup G) := hVS huV
  have hcases4 := fun x (hx : x ∈ V) => mem_four_cases hV4 hzVV huV hz1 hu1 huz' hV2 hx
  have hconjV : ∀ s ∈ (S : Subgroup G), s * u * s⁻¹ ∈ V := fun s hs =>
    (mem_normalizer_iff.mp (hSV hs) u).mp huV
  have hzconj : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := fun s hs => by
    rw [← hzc s hs, mul_inv_cancel_right]
  have hcases : ∀ s ∈ (S : Subgroup G), s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z := by
    intro s hs
    rcases hcases4 _ (hconjV s hs) with h1 | h1 | h1 | h1
    · exfalso
      apply hu1
      calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply huz'
      calc u = s⁻¹ * (s * u * s⁻¹) * s := by group
        _ = s⁻¹ * z * s := by rw [h1]
        _ = z := by simpa using hzconj s⁻¹ ((S : Subgroup G).inv_mem hs)
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨a, haS, hau1⟩ : ∃ a ∈ (S : Subgroup G), a * u * a⁻¹ ≠ u := by
    by_contra hcon
    push Not at hcon
    apply huz'
    refine huniq S u huS z hzS hu2 hz2 (fun s hs => ?_) hzc
    calc u * s = s * u * s⁻¹ * s := by rw [hcon s hs]
      _ = s * u := by group
  have hau : a * u * a⁻¹ = u * z := (hcases a haS).resolve_left hau1
  set Q := (S : Subgroup G) ⊓ centralizer ({u} : Set G) with hQ
  have hmemQ : ∀ q, q ∈ Q ↔ q ∈ (S : Subgroup G) ∧ q * u = u * q := fun q => by
    rw [hQ, mem_inf, mem_centralizer_singleton_iff]
  have haQ : a ∉ Q := fun ha => hau1 (by rw [((hmemQ a).mp ha).2]; group)
  have hQidx : (Q.subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haS⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    rcases hcases b b.2 with hb | hb
    · have hbQ : (b : G) ∈ Q := (hmemQ b).mpr ⟨b.2, by
        calc (b : G) * u = (b : G) * u * (b : G)⁻¹ * b := by group
          _ = u * b := by rw [hb]⟩
      refine Or.inr ⟨hbQ, fun hba => haQ ?_⟩
      have : a = (b : G)⁻¹ * ((b : G) * a) := by group
      rw [this]
      exact Q.mul_mem (Q.inv_mem hbQ) hba
    · have hbQ : (b : G) ∉ Q := fun hbQ => by
        have := ((hmemQ b).mp hbQ).2
        rw [show (b : G) * u * (b : G)⁻¹ = u by rw [this]; group] at hb
        apply hz1
        calc z = u⁻¹ * (u * z) := by group
          _ = 1 := by rw [← hb]; group
      refine Or.inl ⟨(hmemQ _).mpr ⟨(S : Subgroup G).mul_mem b.2 haS, ?_⟩, hbQ⟩
      have : ((b : G) * a) * u * ((b : G) * a)⁻¹ = u := by
        calc ((b : G) * a) * u * ((b : G) * a)⁻¹ = (b : G) * (a * u * a⁻¹) * (b : G)⁻¹ := by
              group
          _ = ((b : G) * u * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by rw [hau]; group
          _ = (u * z) * z := by rw [hb, hzconj b b.2]
          _ = u := by rw [mul_assoc, hzz, mul_one]
      calc (b : G) * a * u = ((b : G) * a) * u * ((b : G) * a)⁻¹ * ((b : G) * a) := by group
        _ = u * ((b : G) * a) := by rw [this]
  have hcardS := h.card_sylow S
  have hcardQ : Nat.card Q * 2 = 2 ^ p := by
    have := (Q.subgroupOf S).card_mul_index
    rwa [hQidx, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, hcardS] at this
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_of_orderOf_eq_two hz2 hu2)
  set C := centralizer ({u} : Set G) with hC
  have hTC : ((c • S : Sylow 2 G) : Subgroup G) ≤ C := by
    intro x hx
    rw [mem_smul_sylow_iff] at hx
    rw [hC, mem_centralizer_singleton_iff, ← hc]
    have := hzc _ hx
    calc x * (c * z * c⁻¹) = c * ((c⁻¹ * x * c) * z) * c⁻¹ := by group
      _ = c * (z * (c⁻¹ * x * c)) * c⁻¹ := by rw [this]
      _ = c * z * c⁻¹ * x := by group
  have hQC : Q ≤ C := inf_le_right
  have hQp : IsPGroup 2 (Q.subgroupOf C) := by
    rintro ⟨⟨x, hxC⟩, hxQ⟩
    have hxS : x ∈ (S : Subgroup G) := ((hmemQ x).mp (mem_subgroupOf.mp hxQ)).1
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨x, hxS⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  obtain ⟨Q₁, hQ₁⟩ := hQp.exists_le_sylow
  set R : Subgroup G := (Q₁ : Subgroup C).map C.subtype with hR
  have hRp : IsPGroup 2 R := Q₁.isPGroup'.map _
  have hRcard : Nat.card R = 2 ^ p := by
    rw [hR, card_map_of_injective C.subtype_injective, Q₁.card_eq_multiplicity,
      ← ((c • S : Sylow 2 G).subtype hTC).card_eq_multiplicity, Sylow.coe_subtype,
      Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, h.card_sylow]
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hQR : Q ≤ R := fun x hx => ⟨⟨x, hQC hx⟩, hQ₁ (mem_subgroupOf.mpr hx), rfl⟩
  have hRidx : ¬ 2 ∣ R.index := by
    have h1 := R.card_mul_index
    rw [hRcard, h.card_group] at h1
    have h2 : R.index = (2 ^ p - 1) * p := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    exact (Nat.not_even_iff_odd.mpr h.odd_card_stab) ∘ even_iff_two_dvd.mpr
  set RS := hRp.toSylow hRidx with hRSdef
  have hRS : (RS : Subgroup G) = R := IsPGroup.toSylow_coe _ _
  have hQRidx : (Q.subgroupOf R).index = 2 := by
    have h1 := (Q.subgroupOf R).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hQR).toEquiv, hRcard, ← hcardQ] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hQRn : ∀ b ∈ R, ∀ q ∈ Q, b * q * b⁻¹ ∈ Q := by
    have hn := Subgroup.normal_of_index_eq_two hQRidx
    intro b hb q hq
    exact (Subgroup.normal_subgroupOf_iff hQR).mp hn q b hq hb
  have hzQ : z ∈ Q := (hmemQ z).mpr ⟨hzS, hzc u huS⟩
  have huQ : u ∈ Q := (hmemQ u).mpr ⟨huS, rfl⟩
  have huRc : ∀ b ∈ R, b * u = u * b := fun b hb => mem_centralizer_singleton_iff.mp (hRC hb)
  obtain ⟨b, hbR, hbz⟩ : ∃ b ∈ R, b * z * b⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    apply huz'
    refine (huniq RS z (hRS ▸ hQR hzQ) u (hRS ▸ hQR huQ) hz2 hu2 (fun s hs => ?_)
      (fun s hs => (huRc s (hRS ▸ hs)).symm)).symm
    calc z * s = s * (s⁻¹ * z * s) := by group
      _ = s * z := by
        rw [show s⁻¹ * z * s = z by
          simpa using hcon s⁻¹ (R.inv_mem (hRS ▸ hs))]
  have hbzQ : b * z * b⁻¹ ∈ Q := hQRn b hbR z hzQ
  have hbzc : ∀ q ∈ Q, (b * z * b⁻¹) * q = q * (b * z * b⁻¹) := by
    intro q hq
    have hq' : b⁻¹ * q * b ∈ Q := by
      simpa using hQRn b⁻¹ (R.inv_mem hbR) q hq
    have := hzc _ ((hmemQ _).mp hq').1
    calc b * z * b⁻¹ * q = b * (z * (b⁻¹ * q * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * q * b) * z) * b⁻¹ := by rw [this]
      _ = q * (b * z * b⁻¹) := by group
  have hbz2 : (b * z * b⁻¹) ^ 2 = 1 := by rw [conj_pow, hV2 z hzVV]; group
  have hbzuz : b * z * b⁻¹ = u * z := by
    rcases thompson_omega (huniq S) hzS hz2 hzc huS (hV2 u huV) haS hau hcases hbzQ hbzc hbz2
      with h1 | h1 | h1 | h1
    · exfalso
      apply hz1
      calc z = b⁻¹ * (b * z * b⁻¹) * b := by group
        _ = 1 := by rw [h1]; group
    · exact absurd h1 hbz
    · exfalso
      apply huz'
      have hbu : b * u * b⁻¹ = u := by rw [huRc b hbR]; group
      calc u = b⁻¹ * (b * u * b⁻¹) * b := by group
        _ = b⁻¹ * (b * z * b⁻¹) * b := by rw [hbu, h1]
        _ = z := by group
    · exact h1
  have hcyc := three_dvd_orderOf_of_cycle (w := a * b) (z := z) (u := u)
    (by
      calc a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
        _ = (a * u * a⁻¹) * (a * z * a⁻¹) := by rw [hbzuz]; group
        _ = u := by rw [hau, hzconj a haS, mul_assoc, hzz, mul_one])
    (by
      calc a * b * u * (a * b)⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by group
        _ = u * z := by rw [huRc b hbR, mul_inv_cancel_right, hau])
    (hzc u huS) huu huz' (fun h1 => hu1 (by simpa using h1))
  exact hcyc.trans (orderOf_dvd_natCard _)

theorem EndHyp.not_exists_normal_two_complement [Finite G] (h : EndHyp G Ω p ω K P) :
    ¬ ∃ N : Subgroup G, CFSG.GroupTheory.IsNormalPComplement 2 N := by
  rintro ⟨N, hNn, hNc, k, hk⟩
  have := h.faithful
  by_cases hN : N = ⊥
  · rw [hN, Subgroup.index_bot, h.card_group] at hk
    have hpk : p ∣ 2 ^ k := hk ▸ dvd_mul_of_dvd_right (dvd_mul_left p _) _
    have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp (h.prime.dvd_of_dvd_pow hpk)
    have := h.three_le
    omega
  · have hpre := isPretransitive_of_normal h.twoTrans N hN
    have hdvd : Nat.card Ω ∣ Nat.card N := by
      have h1 := (stabilizer N ω).index_dvd_card
      rwa [index_stabilizer, orbit_eq_univ, Set.ncard_univ] at h1
    rw [h.card] at hdvd
    have h2 : 2 ∣ Nat.card N := (dvd_pow_self 2 h.prime.ne_zero).trans hdvd
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two h2 (dvd_refl 2) hNc

theorem EndHyp.exists_odd_normalizer [Finite G] (h : EndHyp G Ω p ω K P) :
    ∃ Q : Subgroup G, IsPGroup 2 Q ∧ Q ≠ ⊥ ∧ ∃ g ∈ normalizer (Q : Set G), ∃ r : ℕ,
      r.Prime ∧ r ≠ 2 ∧ orderOf g = r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := (CFSG.GroupTheory.frobenius_normal_p_complement (G := G) 2).1
  have hnot : ¬ ∀ Q : Subgroup G, IsPGroup 2 Q → IsPGroup 2 (normalizer (Q : Set G) ⧸
      (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) :=
    fun hall => h.not_exists_normal_two_complement (hF.mpr hall)
  push Not at hnot
  obtain ⟨Q, hQ, hA⟩ := hnot
  refine ⟨Q, hQ, ?_, ?_⟩
  · rintro rfl
    apply hA
    have htop : (centralizer ((⊥ : Subgroup G) : Set G)).subgroupOf
        (normalizer ((⊥ : Subgroup G) : Set G)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [mem_subgroupOf, mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, mem_bot] at hy
      rw [hy, one_mul, mul_one]
    exact IsPGroup.of_card (n := 0)
      (by rw [pow_zero, ← Subgroup.index_eq_card, Subgroup.index_eq_one.mpr htop])
  · obtain ⟨r, hr, hr2, hrA⟩ : ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card (normalizer (Q : Set G) ⧸
        (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) := by
      by_contra hcon
      push Not at hcon
      apply hA
      have h0 : Nat.card (normalizer (Q : Set G) ⧸
          (centralizer (Q : Set G)).subgroupOf (normalizer (Q : Set G))) ≠ 0 := Nat.card_pos.ne'
      exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd h0 (fun {d} hd hdvd =>
        by_contra fun hne => hcon d hd hne hdvd))
    have hrN : r ∣ Nat.card (normalizer (Q : Set G)) :=
      hrA.trans (Subgroup.card_quotient_dvd_card _)
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrN
    exact ⟨g, g.2, r, hr, hr2, by rw [Subgroup.orderOf_coe, hg]⟩

theorem EndHyp.exists_two_central_involutions [Finite G] (h : EndHyp G Ω p ω K P) (h5 : 5 ≤ p)
    (S : Sylow 2 G) :
    ∃ z₁ ∈ (S : Subgroup G), ∃ z₂ ∈ (S : Subgroup G), z₁ ≠ z₂ ∧ orderOf z₁ = 2 ∧
      orderOf z₂ = 2 ∧ ∀ s ∈ (S : Subgroup G), z₁ * s = s * z₁ ∧ z₂ * s = s * z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hS : AtMostOneCentralInvolution (S : Subgroup G) := by
    intro z₁ hz₁ z₂ hz₂ ho₁ ho₂ hc₁ hc₂
    by_contra hne
    exact hcon ⟨z₁, hz₁, z₂, hz₂, hne, ho₁, ho₂, fun s hs => ⟨hc₁ s hs, hc₂ s hs⟩⟩
  have huniq : ∀ R : Sylow 2 G, AtMostOneCentralInvolution (R : Subgroup G) :=
    fun R => atMostOneCentralInvolution_of_sylow hS R
  have h3 : ¬ 3 ∣ Nat.card G := by
    rw [h.card_group]
    intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h1)
      omega
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
      · exact three_not_dvd_two_pow_sub_one (h.prime.odd_of_ne_two (by omega)) h2
      · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h.prime).mp h2
        omega
  obtain ⟨Q, hQ2, hQ1, g, hgN, r, hr, hr2, hgr⟩ := h.exists_odd_normalizer
  have : Fact r.Prime := ⟨hr⟩
  set E := centralInvolutions Q with hEdef
  have hEQ : E ≤ Q := fun x hx => hx.1
  have hE2 : IsPGroup 2 E := hQ2.to_le hEQ
  have hEne : E ≠ ⊥ := by
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    have := hQ2.center_nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : center Q)
    set y : G := ((x : Q) : G) with hy
    have hy1 : y ≠ 1 := fun h1 => hx (Subtype.ext (Subtype.ext h1))
    have hyQ : y ∈ Q := (x : Q).2
    have hyc : ∀ s ∈ Q, y * s = s * y := fun s hs => by
      have := (Subgroup.mem_center_iff.mp x.2) ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    obtain ⟨n, hn⟩ := hQ2 ⟨y, hyQ⟩
    have hn' : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have ht := orderOf_pow_orderOf_div_two hy1 hn'
    intro hbot
    have htE : y ^ (orderOf y / 2) ∈ E :=
      ⟨Q.pow_mem hyQ _, fun s hs => (Commute.pow_left (hyc s hs) _).eq,
        by have := pow_orderOf_eq_one (y ^ (orderOf y / 2)); rwa [ht] at this⟩
    rw [hbot, mem_bot] at htE
    rw [htE, orderOf_one] at ht
    omega
  have hgE : g ∈ normalizer (E : Set G) :=
    mem_normalizer_of_conj_mem (fun x hx => conj_mem_centralInvolutions hgN hx)
  have hE1 : Nat.card E ≡ 1 [MOD r] := by
    by_contra hmod
    obtain ⟨e, heE, he1, hge⟩ := exists_ne_one_commute_of_normalizes E hgE hgr hmod
    exact h.mul_ne_of_orderOf_eq_two (orderOf_eq_prime heE.2.2 he1) hr hr2 hgr hge.symm
  obtain ⟨s, hs⟩ := hE2.exists_card_eq
  obtain ⟨S', hES'⟩ := hE2.exists_le_sylow
  have hsp : s ≤ p := by
    have := Subgroup.card_dvd_of_le hES'
    rw [hs, h.card_sylow S'] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hrdvd : r ∣ 2 ^ s - 1 :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp (hs ▸ hE1).symm
  have hrG : r ∣ 2 ^ p * ((2 ^ p - 1) * p) := h.card_group ▸ (hgr ▸ orderOf_dvd_natCard g)
  by_cases hrp : r = p
  ·
    subst hrp
    have hs3 : 3 ≤ s := by
      by_contra hs3
      push Not at hs3
      interval_cases s
      · exact hEne (Subgroup.eq_bot_of_card_eq E (by rw [hs, pow_zero]))
      · rw [pow_one] at hrdvd
        exact hr.one_lt.ne' (Nat.dvd_one.mp hrdvd)
      · have := Nat.le_of_dvd (by norm_num) hrdvd
        omega
    have hEel : CFSG.Assembly.IsElemAbelian 2 E :=
      ⟨⟨⟨fun a b => Subtype.ext (a.2.2.1 b (hEQ b.2))⟩⟩, fun x hx => hx.2.2⟩
    have hrank : 3 ≤ CFSG.Assembly.pRank 2 (S' : Subgroup G) :=
      le_trans hs3 (le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 2
        Nat.prime_two (S' : Subgroup G)) ⟨E, hES', hEel, hs⟩)
    obtain ⟨V, hVS', hS'V, hVel, hV4⟩ :=
      CFSG.Assembly.Dichotomy.exists_normal_four_of_three_le_pRank S'.isPGroup' hrank
    exact h3 (h.three_dvd_card_of_normal_four S' huniq hVS' hS'V hVel.2 hV4)
  ·
    have hrp' : r ∣ 2 ^ p - 1 := by
      rcases (Nat.Prime.dvd_mul hr).mp hrG with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
          hr2
      · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
        · exact h2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr h.prime).mp h2) hrp
    have hsp' : s = p := by
      by_contra hne
      have hlt : s < p := lt_of_le_of_ne hsp hne
      have hs0 : 0 < s := by
        by_contra hs0
        push Not at hs0
        have : s = 0 := by omega
        exact hEne (Subgroup.eq_bot_of_card_eq E (by rw [hs, this, pow_zero]))
      have hgcd : Nat.gcd s p = 1 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd h.prime).mpr
          (Nat.not_dvd_of_pos_of_lt hs0 hlt))
      have hr1 : r ∣ Nat.gcd (2 ^ s - 1) (2 ^ p - 1) := Nat.dvd_gcd hrdvd hrp'
      rw [Nat.pow_sub_one_gcd_pow_sub_one, hgcd, pow_one] at hr1
      exact hr.one_lt.ne' (Nat.dvd_one.mp hr1)
    have hES : E = S' := Subgroup.eq_of_le_of_card_ge hES' (by rw [hs, hsp', h.card_sylow S'])
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEne
    obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ zpowers (x : G) := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show E ≤ zpowers (x : G) from hcon)
      have hx2 : orderOf (x : G) = 2 := orderOf_eq_prime x.2.2.2 (fun h1 => hx1 (Subtype.ext h1))
      rw [hs, hsp', Nat.card_zpowers, hx2] at h1
      have : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ one_mem _)
    have hcentral : ∀ w ∈ E, ∀ t ∈ (S' : Subgroup G), w * t = t * w := by
      intro w hw t ht
      rw [← hES] at ht
      exact hw.2.1 t (hEQ ht)
    have := huniq S' (x : G) (hES ▸ x.2) y (hES ▸ hyE)
      (orderOf_eq_prime x.2.2.2 (fun h1 => hx1 (Subtype.ext h1))) (orderOf_eq_prime hyE.2.2 hy1)
      (hcentral _ x.2) (hcentral _ hyE)
    exact hyx (this ▸ mem_zpowers _)

theorem EndHyp.false_of_five_le [Finite G] (h : EndHyp G Ω p ω K P) (h5 : 5 ≤ p) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  exact h.false_of_central_involutions S (h.exists_two_central_involutions h5 S)

end CFSG.GH74.Uniqueness.Hering
