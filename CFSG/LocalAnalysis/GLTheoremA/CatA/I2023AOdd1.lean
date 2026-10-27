module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ACtx
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ABs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_into_sylow [Fact (Nat.Prime 2)] {N : Subgroup G} (P : Sylow 2 ↥N)
    {U : Subgroup G} (hUN : U ≤ N) (hU : IsPGroup 2 U) :
    ∃ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ (P : Subgroup ↥N).map N.subtype := by
  classical
  have hU' : IsPGroup 2 (U.subgroupOf N) := hU.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm
  obtain ⟨Q, hQ⟩ := hU'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq ↥N Q P
  refine ⟨(n : G), n.2, fun u hu => ?_⟩
  have huQ : (⟨u, hUN hu⟩ : ↥N) ∈ (Q : Subgroup ↥N) := hQ hu
  have h1 : (MulAut.conj n) • (⟨u, hUN hu⟩ : ↥N) ∈ (MulAut.conj n) • (Q : Subgroup ↥N) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ huQ
  have h2 : ((n • Q : Sylow 2 ↥N) : Subgroup ↥N) = (MulAut.conj n) • (Q : Subgroup ↥N) := rfl
  rw [hn] at h2
  have h3 : n * ⟨u, hUN hu⟩ * n⁻¹ ∈ (P : Subgroup ↥N) := by
    rw [h2]
    exact h1
  exact ⟨_, h3, rfl⟩

theorem mem_normalizer_of_conj_le {T : Subgroup G} {a : G} (h : ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    a ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h y, fun hy => ?_⟩
  let f : ↥T → ↥T := fun t => ⟨a * t * a⁻¹, h t t.2⟩
  have hinj : Function.Injective f := fun s t hst => by
    have := congrArg Subtype.val hst
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨a * y * a⁻¹, hy⟩
  have := congrArg Subtype.val ht
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact t.2

theorem exists_mul_mem_normalizer [Fact (Nat.Prime 2)] {X N : Subgroup G}
    (hXN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (P : Sylow 2 ↥N) {g : G} (hg : g ∈ X) :
    ∃ n ∈ N, n * g ∈ Subgroup.normalizer
      (((P : Subgroup ↥N).map N.subtype : Subgroup G) : Set G) := by
  set T : Subgroup G := (P : Subgroup ↥N).map N.subtype with hT
  have hTN : T ≤ N := Subgroup.map_subtype_le _
  set U : Subgroup G := T.map (MulAut.conj g).toMonoidHom with hU
  have hUN : U ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    exact hXN g hg t (hTN ht)
  have hU2 : IsPGroup 2 U := (P.2.map N.subtype).map _
  obtain ⟨n, hn, hconj⟩ := exists_conj_into_sylow P hUN hU2
  refine ⟨n, hn, mem_normalizer_of_conj_le fun t ht => ?_⟩
  have h := hconj (g * t * g⁻¹) ⟨t, ht, rfl⟩
  have e : (n * g) * t * (n * g)⁻¹ = n * (g * t * g⁻¹) * n⁻¹ := by group
  rw [e]
  exact h

theorem centralizes_of_cyclic_two {g b : G} {k : ℕ} (hg : g ^ (2 ^ k) = 1) (hb : b ^ 3 = 1)
    (hbg : b * g * b⁻¹ ∈ Subgroup.zpowers g) : b * g * b⁻¹ = g := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hbg
  set c : G →* G := (MulAut.conj b).toMonoidHom with hc
  have hcg : c g = g ^ j := by
    rw [hj]
    simp [hc, MulAut.conj_apply]
  have hc3 : ∀ y, c (c (c y)) = y := by
    intro y
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : b * (b * (b * y * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * y * (b * b * b)⁻¹ := by group
    have hb3 : b * b * b = 1 := by rw [← pow_three']; exact hb
    rw [this, hb3]
    simp
  have h3 : g ^ (j ^ 3) = g := by
    have h1 : c (c (c g)) = g ^ (j ^ 3) := by
      rw [hcg, map_zpow, hcg, ← zpow_mul, map_zpow, hcg, ← zpow_mul]
      ring_nf
    rw [← h1, hc3]
  have hdvd : (orderOf g : ℤ) ∣ j ^ 3 - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, h3, zpow_one, mul_inv_cancel]
  obtain ⟨m, hm, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg)
  have hodd : IsCoprime (2 : ℤ) (j ^ 2 + j + 1) := by
    have : Odd (j ^ 2 + j + 1) := by
      rcases Int.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨2 * r ^ 2 + r, by rw [hr]; ring⟩
      · exact ⟨2 * r ^ 2 + 3 * r + 1, by rw [hr]; ring⟩
    obtain ⟨d, hd⟩ := this
    exact ⟨-d, 1, by rw [hd]; ring⟩
  have hcop : IsCoprime (orderOf g : ℤ) (j ^ 2 + j + 1) := by
    rw [hord]
    push_cast
    exact hodd.pow_left
  have hfac : j ^ 3 - 1 = (j - 1) * (j ^ 2 + j + 1) := by ring
  rw [hfac] at hdvd
  have hdvd' : (orderOf g : ℤ) ∣ j - 1 := hcop.dvd_of_dvd_mul_right hdvd
  rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, mul_inv_eq_one] at hdvd'
  rw [← hj, hdvd']

theorem centralized_of_embed_quaternion {T : Subgroup G}
    (hT : IsEmpty (T ≃* QuaternionGroup 2)) (e : ↥T →* QuaternionGroup 2)
    (he : Function.Injective e) {b : G} (hb3 : b ^ 3 = 1)
    (hbT : b ∈ Subgroup.normalizer (T : Set G)) : ∀ t ∈ T, b * t * b⁻¹ = t := by
  classical
  have hQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card]
    exact QuaternionGroup.card
  have hle : Nat.card T ≤ 8 := hQ ▸ Nat.card_le_card_of_injective e he
  have hne : Nat.card T ≠ 8 := by
    intro h8
    have hbij : Function.Bijective e := he.bijective_of_nat_card_le (by rw [hQ, h8])
    exact hT.false (MulEquiv.ofBijective e hbij)
  have hdvd : Nat.card T ∣ 8 := by
    have h1 : Nat.card T = Nat.card e.range :=
      Nat.card_congr (MonoidHom.ofInjective he).toEquiv
    rw [h1, ← hQ]
    exact Subgroup.card_subgroup_dvd_card _
  have hcyc : IsCyclic T := by
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.card T ∣ 2 ^ 3 from hdvd)
    interval_cases m
    · have hsub : Subsingleton T := (Nat.card_eq_one_iff_unique.1 (by simpa using hmc)).1
      infer_instance
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card (by simpa using hmc)
    ·
      have h4 : Nat.card T = 4 := by simpa using hmc
      have hsq : ∀ y : QuaternionGroup 2, y ^ 2 = 1 → y = 1 ∨ y = QuaternionGroup.a 2 := by decide
      have hex : ∃ t : ↥T, t ^ 2 ≠ 1 := by
        by_contra hall
        push Not at hall
        let f : ↥T → {y : QuaternionGroup 2 // y = 1 ∨ y = QuaternionGroup.a 2} :=
          fun t => ⟨e t, hsq _ (by rw [← map_pow, hall t, map_one])⟩
        have hfi : Function.Injective f := fun s t hst => he (congrArg Subtype.val hst)
        have hcard := Nat.card_le_card_of_injective f hfi
        have h2 : Nat.card {y : QuaternionGroup 2 // y = 1 ∨ y = QuaternionGroup.a 2} = 2 := by
          rw [Nat.card_eq_fintype_card]
          decide
        omega
      obtain ⟨t₀, ht₀⟩ := hex
      have h44 : t₀ ^ 4 = 1 := by
        rw [← h4]
        exact pow_card_eq_one'
      have hord : orderOf t₀ = 4 := by
        have hd : orderOf t₀ ∣ 4 := orderOf_dvd_of_pow_eq_one h44
        have h1 : orderOf t₀ ≠ 1 := fun h => ht₀ (by
          have := pow_orderOf_eq_one t₀
          rw [h] at this
          rw [orderOf_eq_one_iff.1 h]
          simp)
        have h2 : orderOf t₀ ≠ 2 := fun h => ht₀ (by
          have := pow_orderOf_eq_one t₀
          rwa [h] at this)
        have hmem : orderOf t₀ ∈ Nat.divisors 4 := by simpa using hd
        have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
        rw [hdiv] at hmem
        rcases Finset.mem_insert.1 hmem with h | hmem
        · exact absurd h h1
        rcases Finset.mem_insert.1 hmem with h | hmem
        · exact absurd h h2
        exact Finset.mem_singleton.1 hmem
      exact isCyclic_of_orderOf_eq_card t₀ (by rw [hord, h4])
    · exact absurd (by simpa using hmc) hne
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg8 : (g : G) ^ (2 ^ 3) = 1 := by
    have h1 : g ^ Nat.card T = 1 := pow_card_eq_one'
    obtain ⟨c, hc⟩ := hdvd
    have h2 : g ^ 8 = 1 := by rw [hc, pow_mul, h1, one_pow]
    have := congrArg Subtype.val h2
    simpa using this
  have hbg : b * (g : G) * b⁻¹ ∈ Subgroup.zpowers (g : G) := by
    have hmem : b * (g : G) * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hbT (g : G)).1 g.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨_, hmem⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hfix := centralizes_of_cyclic_two hg8 hb3 hbg
  intro t ht
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨t, ht⟩)
  have hti : (g : G) ^ i = t := by simpa using congrArg Subtype.val hi
  rw [← hti]
  have : b * (g : G) ^ i * b⁻¹ = (b * (g : G) * b⁻¹) ^ i := by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rw [this, hfix]

theorem essential_le_core {q : TauCeti.PrimePower} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hc : Ctx B x L) (F : TD4Facts (PQuot 3 L) q) (hodd : Odd q.exponent)
    {T : Subgroup G} (hTx : T ≤ cx x) (hT2 : IsPGroup 2 T)
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    (⁅T, B⁆ : Subgroup G) ≠ ⊥ → T ≤ GLAPPrimeCoreOf 3 (cx x) := by
  intro hTc
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun t ht => hc.hXN (hTx ht)
  set Tt : Subgroup (MulAut (PQuot 3 L)) := (rhoSub L T hTL).range with hTt
  have hTt2 : IsPGroup 2 Tt :=
    hT2.of_surjective (rhoSub L T hTL).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  set E : Subgroup (MulAut (PQuot 3 L)) := (rhoSub L B hc.hBL).range with hE
  have hEel : IsElemAbelian 3 E := isElemAbelian_range hc.hBel _
  have hE27 : Nat.card E = 27 := (hc.rank_eq F.toTD4Rank).1
  have hconj : ∀ b ∈ B, ∀ hb : b ∈ Subgroup.normalizer (L : Set G), ∀ φ ∈ Tt,
      rho L ⟨b, hb⟩ * φ * (rho L ⟨b, hb⟩)⁻¹ ∈ Tt := by
    intro b hb hbN φ hφ
    obtain ⟨⟨t, ht⟩, rfl⟩ := hφ
    have hbt : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht
    refine ⟨⟨b * t * b⁻¹, hbt⟩, ?_⟩
    rw [rhoSub_apply, rhoSub_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hEN : E ≤ Subgroup.normalizer (Tt : Set (MulAut (PQuot 3 L))) := by
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro φ
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := hc.hBL hb
    refine ⟨fun hφ => hconj b hb hbN φ hφ, fun hφ => ?_⟩
    have h2 := hconj b⁻¹ (B.inv_mem hb) (Subgroup.inv_mem _ hbN) _ hφ
    have e : rho L ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩ = (rho L ⟨b, hbN⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e, inv_inv] at h2
    have e2 : (rho L ⟨b, hbN⟩)⁻¹ * (rhoSub L B hc.hBL ⟨b, hb⟩ * φ * (rhoSub L B hc.hBL ⟨b, hb⟩)⁻¹) *
        rho L ⟨b, hbN⟩ = φ := by
      rw [rhoSub_apply]
      group
    rwa [e2] at h2
  have hTbot : Tt = ⊥ := by
    by_contra hne
    have := F.D hodd E Tt hEel hTt2 hne hEN
    omega
  intro t ht
  have hρt : rho L ⟨t, hTL ht⟩ = 1 := by
    have h1 : rhoSub L T hTL ⟨t, ht⟩ ∈ Tt := ⟨⟨t, ht⟩, rfl⟩
    rw [hTbot] at h1
    exact h1
  have htc : t ∈ centModSubgroup 3 L := (rho_eq_one_iff L (hTL ht)).1 hρt
  have hinvc : t⁻¹ ∈ centModSubgroup 3 L := (centModSubgroup 3 L).inv_mem htc
  have hcond : ∀ l ∈ L, l⁻¹ * (t⁻¹ * l * t) ∈ GLAPPrimeCoreOf 3 (cx x) := by
    intro l hl
    have h := hinvc.2 l⁻¹ (L.inv_mem hl)
    have e : ⁅l⁻¹, t⁻¹⁆ = l⁻¹ * (t⁻¹ * l * t) := by
      rw [commutatorElement_def]
      group
    rw [e] at h
    exact hc.hOL h
  obtain ⟨n, hn⟩ := hc.hC3 t (hTx ht) hcond
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact mem_of_pow_coprime (a := 2 ^ k) (b := 3 ^ n) (Nat.Coprime.pow k n (by norm_num)) hk' hn

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
