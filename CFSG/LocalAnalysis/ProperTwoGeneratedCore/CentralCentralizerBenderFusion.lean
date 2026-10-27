module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderQuotient

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

section Invariant

omit [Finite G] in
theorem card_pow_eq_conj_of_mem_normalizer (C : Subgroup G) {n : G}
    (hn : n ∈ Subgroup.normalizer (C : Set G)) (k : ℕ) (a : G) :
    Nat.card {w : G // w ∈ C ∧ w ^ k = n⁻¹ * a * n} = Nat.card {w : G // w ∈ C ∧ w ^ k = a} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj n).toEquiv fun w => ?_)
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply,
    ← Subgroup.mem_normalizer_iff.mp hn w, conj_pow]
  constructor
  · rintro ⟨hw, hwk⟩
    exact ⟨hw, by rw [hwk]; group⟩
  · rintro ⟨hw, hwk⟩
    exact ⟨hw, by rw [← hwk]; group⟩

omit [Finite G] in
theorem normalizer_le_normalizer_of_characteristic {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have hmaps : ∀ n ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    intro n hn c hc
    have hfix := (Subgroup.characteristic_iff_map_eq.mp hchar)
      (S.normalizerMonoidHom ⟨n, hn⟩)
    have hmem : (S.normalizerMonoidHom ⟨n, hn⟩) ⟨c, hCS hc⟩ ∈ C.subgroupOf S := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc)
    exact Subgroup.mem_subgroupOf.mp hmem
  intro n hn
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨hmaps n hn c, fun hc => ?_⟩
  have h := hmaps n⁻¹ (Subgroup.inv_mem _ hn) _ hc
  rwa [show n⁻¹ * (n * c * n⁻¹) * n⁻¹⁻¹ = c by group] at h

theorem card_conjClass_carrier_mul_card_centralizer {K : Type} [Group K] [Finite K] (x : K) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (Subgroup.centralizer ({x} : Set K)) =
      Nat.card K := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

theorem sylow_normalizer_class_card_odd (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hz : ∀ s ∈ (S : Subgroup G), s * z = z * s) :
    Odd (Nat.card {w : G // ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
      n⁻¹ * z * n = w}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  set z' : N := ⟨z, Subgroup.le_normalizer hzS⟩
  have hequiv : (ConjClasses.mk z').carrier ≃
      {w : G // ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * z * n = w} :=
    { toFun := fun g => ⟨((g.1 : N) : G), by
        obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
          (ConjClasses.mem_carrier_iff_mk_eq.mp g.2)).symm
        refine ⟨((c⁻¹ : N) : G), (c⁻¹ : N).2, ?_⟩
        rw [← hc]
        simp [z']⟩
      invFun := fun w => ⟨⟨w.1, by
          obtain ⟨n, hn, hw⟩ := w.2
          rw [← hw]
          exact N.mul_mem (N.mul_mem (N.inv_mem hn) (Subgroup.le_normalizer hzS)) hn⟩, by
        obtain ⟨n, hn, hw⟩ := w.2
        refine ConjClasses.mem_carrier_iff_mk_eq.mpr (ConjClasses.mk_eq_mk_iff_isConj.mpr ?_)
        refine isConj_iff.mpr ⟨⟨n, hn⟩, Subtype.ext ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, z']
        rw [← hw]
        group⟩
      left_inv := fun g => rfl
      right_inv := fun w => rfl }
  rw [← Nat.card_congr hequiv]
  set C := Subgroup.centralizer ({z'} : Set N)
  have hcard := card_conjClass_carrier_mul_card_centralizer z'
  have hindex := Subgroup.card_mul_index C
  have hclass : Nat.card (ConjClasses.mk z').carrier = C.index :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [hcard, mul_comm, hindex])
  set T : Sylow 2 N := S.subtype (Subgroup.le_normalizer)
  have hTC : (T : Subgroup N) ≤ C := by
    intro s hs
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (hz _ hs))
  have hodd : Odd (T : Subgroup N).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)
  rw [hclass]
  exact Odd.of_dvd_nat hodd (Subgroup.index_dvd_of_le hTC)

end Invariant

section Fused

variable {x : G}

theorem escapingMk_injOn_twoGroup {P : Subgroup G} (hP : IsPGroup 2 P)
    {a b : Subgroup.centralizer ({x} : Set G)} (ha : (a : G) ∈ P) (hb : (b : G) ∈ P)
    (hab : escapingMk x a = escapingMk x b) : a = b := by
  have hO : a⁻¹ * b ∈ pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) := QuotientGroup.eq.mp hab
  have hPab : ((a⁻¹ * b : Subgroup.centralizer ({x} : Set G)) : G) ∈ P := by
    simpa using P.mul_mem (P.inv_mem ha) hb
  obtain ⟨k, hk⟩ := hP ⟨_, hPab⟩
  have hk' : (a⁻¹ * b) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h1 := eq_one_of_pow_two_pow_eq_one_of_odd (escaping_oddCore_odd x) hO hk'
  rwa [inv_mul_eq_one] at h1

theorem exists_involution_mem_inf_center {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {R : Subgroup P} [R.Normal] (hR : R ≠ ⊥) :
    ∃ r ∈ R, r ∈ Subgroup.center P ∧ orderOf r = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hR
  have h2 : IsPGroup 2 (R ⊓ Subgroup.center P : Subgroup P) := hP.to_subgroup _
  have hnt : Nontrivial (R ⊓ Subgroup.center P : Subgroup P) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hn
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  exact ⟨r, r.2.1, r.2.2, by rwa [Subgroup.orderOf_coe]⟩

variable {S : Sylow 2 G} {H : Subgroup G} {z : G} (hset : CoreSetting G S H)
  (hz : IsCentralInvolution (S : Subgroup G) z) (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H)
  {J : Subgroup (EscapingQuotient z)} (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
include hset hz hesc hJ hzJ

theorem coreSetting_exists_central_involution_mem_component :
    ∃ r : Subgroup.centralizer ({z} : Set G), IsCentralInvolution (S : Subgroup G) (r : G) ∧
      escapingMk z r ∈ J := by
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  have := hq.component_normal hJ hzJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.centralizer ({z} : Set G)
  set Sbar : Sylow 2 (EscapingQuotient z) :=
    (S.subtype hz.le_centralizer).mapSurjective (QuotientGroup.mk'_surjective _)
  have hSbar : (Sbar : Subgroup (EscapingQuotient z)) =
      ((S : Subgroup G).subgroupOf M).map (escapingMk z) := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  obtain ⟨t, htJ, -, ht⟩ := hq.component_exists_involution_mem_image hJ hzJ
  have hJeven : 2 ∣ Nat.card J := by
    have h := orderOf_dvd_natCard (⟨t, htJ⟩ : J)
    rwa [Subgroup.orderOf_mk, ht] at h
  have hT := CFSG.ProperTwoGeneratedCore.normal_sylow_intersection_eq Sbar J
  have hTne := (CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal Sbar J).ne_bot_of_dvd_card
    hJeven
  have hR : J.subgroupOf (Sbar : Subgroup (EscapingQuotient z)) ≠ ⊥ := by
    intro h
    apply hTne
    apply (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp
    rw [hT, inf_comm, ← Subgroup.subgroupOf_map_subtype, h, Subgroup.map_bot]
  obtain ⟨rb, hrbJ, hrbZ, hrb2⟩ := exists_involution_mem_inf_center Sbar.isPGroup' hR
  have hrbS : (rb : EscapingQuotient z) ∈ ((S : Subgroup G).subgroupOf M).map (escapingMk z) :=
    hSbar ▸ rb.property
  obtain ⟨r, hrS, hrmk⟩ := Subgroup.mem_map.mp hrbS
  rw [Subgroup.mem_subgroupOf] at hrS
  have hinj := fun {a b : M} (ha : (a : G) ∈ (S : Subgroup G)) (hb : (b : G) ∈ (S : Subgroup G))
    (hab : escapingMk z a = escapingMk z b) => escapingMk_injOn_twoGroup S.isPGroup' ha hb hab
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [map_one] at hrmk
    rw [← Subgroup.orderOf_coe, ← hrmk, orderOf_one] at hrb2
    exact absurd hrb2 (by decide)
  have hrr : r ^ 2 = 1 := hinj (by simpa using (S : Subgroup G).pow_mem hrS 2)
    (by simp) (by rw [map_pow, hrmk, map_one, ← Subgroup.coe_pow,
      show rb ^ 2 = 1 by rw [pow_two]; exact mul_self_eq_one_of_orderOf_eq_two hrb2,
      Subgroup.coe_one])
  refine ⟨r, ⟨hrS, by rw [Subgroup.orderOf_coe]; exact orderOf_eq_prime hrr hr1, fun s hs => ?_⟩,
    hrmk ▸ hrbJ⟩
  have hsM : s ∈ M := hz.le_centralizer hs
  have hsbar : escapingMk z ⟨s, hsM⟩ ∈ (Sbar : Subgroup (EscapingQuotient z)) :=
    hSbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  have hcomm := Subgroup.mem_center_iff.mp hrbZ ⟨_, hsbar⟩
  have h := hinj (a := ⟨s, hsM⟩ * r) (b := r * ⟨s, hsM⟩)
    (by simpa using (S : Subgroup G).mul_mem hs hrS)
    (by simpa using (S : Subgroup G).mul_mem hrS hs)
    (by rw [map_mul, map_mul, hrmk]; exact congrArg Subtype.val hcomm)
  exact congrArg Subtype.val h

theorem coreSetting_component_fused_class :
    ∃ r : Subgroup.centralizer ({z} : Set G), IsCentralInvolution (S : Subgroup G) (r : G) ∧
      (r : G) ≠ z ∧ escapingMk z r ∈ J ∧
      ∃ a : G, (a = r ∨ a = r * z) ∧ IsCentralInvolution (S : Subgroup G) a ∧ a ≠ z ∧
        ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n ∈ H ∧ n⁻¹ * z * n = a := by
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  obtain ⟨r, hr, hrJ⟩ := coreSetting_exists_central_involution_mem_component hset hz hesc hJ hzJ
  have hrz : (r : G) ≠ z := fun h => hzJ (by rwa [eq_escapingSelf h] at hrJ)
  have hr2 : orderOf r = 2 := by rw [← Subgroup.orderOf_coe]; exact hr.2.1
  have hrzc : Commute (r : G) z := hz.2.2 r hr.1
  obtain ⟨v, hzv, hv2, hvbar⟩ := exists_isConj_mk_ne_bar hset.simple hset.nonabelian hz.2.1
  have hv2' : orderOf v = 2 := by rwa [← Subgroup.orderOf_coe]
  have hzr : IsCentralInvolution (S : Subgroup G) (r * z) := by
    refine ⟨(S : Subgroup G).mul_mem hr.1 hz.1,
      orderOf_mul_eq_two_of_commute hr.2.1 hz.2.1 hrzc hrz, fun s hs => ?_⟩
    rw [← mul_assoc, hr.2.2 s hs, mul_assoc, hz.2.2 s hs, mul_assoc]
  have hrzz : r * z ≠ z := fun h => by
    rw [mul_eq_right] at h
    have h2 := hr.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2.symm (by decide)
  rcases hq.involution_mem_component_or hJ hzJ (escaping_orderOf_mk z hv2') with hvJ | hvJ
  ·
    obtain ⟨c, -, hc⟩ := hq.component_conj hJ hzJ hrJ hvJ (escaping_orderOf_mk z hr2)
      (escaping_orderOf_mk z hv2')
    have hrv : IsConj (r : G) v := (Subgroup.centralizer ({z} : Set G)).subtype.map_isConj
      (escaping_isConj_of_isConj_mk z hr2 hv2' (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hc⟩))
    obtain ⟨n, hn, hnH, hnz⟩ := coreSetting_centralInvolution_fusion hset hz hr
      (hzv.trans hrv.symm)
    exact ⟨r, hr, hrz, hrJ, r, Or.inl rfl, hr, hrz, n, hn, hnH, hnz⟩
  ·
    obtain ⟨c, -, hc⟩ := hq.component_conj hJ hzJ hrJ hvJ (escaping_orderOf_mk z hr2)
      (orderOf_bar_mul_mk hz.2.1 hv2' (fun h => hvbar (by rw [eq_escapingSelf h])))
    have hzr2 : orderOf (escapingSelf z * r) = 2 := orderOf_mul_eq_two_of_commute
      (orderOf_escapingSelf hz.2.1) hr2 (Subtype.ext hrzc.symm)
      (fun h => hrz (congrArg Subtype.val h.symm))
    have hconj : IsConj (escapingMk z (escapingSelf z * r)) (escapingMk z v) := by
      refine isConj_iff.mpr ⟨c⁻¹, ?_⟩
      have hzc : c⁻¹ * escapingBar z = escapingBar z * c⁻¹ := (commute_escapingBar c⁻¹).eq
      rw [map_mul]
      calc c⁻¹ * (escapingBar z * escapingMk z r) * c⁻¹⁻¹
          = c⁻¹ * escapingBar z * escapingMk z r * c := by group
        _ = escapingBar z * (c⁻¹ * escapingMk z r * c) := by rw [hzc]; group
        _ = escapingMk z v := by
          rw [hc, ← mul_assoc, escapingBar_mul_self hz.2.1, one_mul]
    have hrv : IsConj (r * z) (v : G) := by
      have h := (Subgroup.centralizer ({z} : Set G)).subtype.map_isConj
        (escaping_isConj_of_isConj_mk z hzr2 hv2' hconj)
      simpa [hrzc.eq] using h
    obtain ⟨n, hn, hnH, hnz⟩ := coreSetting_centralInvolution_fusion hset hz hzr
      (hzv.trans hrv.symm)
    exact ⟨r, hr, hrz, hrJ, r * z, Or.inr rfl, hzr, hrzz, n, hn, hnH, hnz⟩

theorem coreSetting_component_fused_class_roots :
    ∃ r : Subgroup.centralizer ({z} : Set G), IsCentralInvolution (S : Subgroup G) (r : G) ∧
      (r : G) ≠ z ∧ escapingMk z r ∈ J ∧
      ∃ a : G, (a = r ∨ a = r * z) ∧ IsCentralInvolution (S : Subgroup G) a ∧ a ≠ z ∧
        ∀ C : Subgroup G, Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer (C : Set G) → ∀ k : ℕ,
            Nat.card {w : G // w ∈ C ∧ w ^ k = z} = Nat.card {w : G // w ∈ C ∧ w ^ k = a} := by
  obtain ⟨r, hr, hrz, hrJ, a, ha, haS, haz, n, hn, -, hna⟩ :=
    coreSetting_component_fused_class hset hz hesc hJ hzJ
  refine ⟨r, hr, hrz, hrJ, a, ha, haS, haz, fun C hC k => ?_⟩
  rw [← hna, card_pow_eq_conj_of_mem_normalizer C (hC hn)]

end Fused

end CFSG.ProperTwoGeneratedCore.Assembly
