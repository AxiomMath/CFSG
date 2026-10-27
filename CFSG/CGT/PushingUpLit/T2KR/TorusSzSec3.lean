module

public import CFSG.CGT.PushingUpLit.T2KR.TorusSzData
public import CFSG.CGT.PushingUpLit.T2KR.TorusSec3
public import CFSG.CGT.PushingUpLit.T2KR.TorusAbs
public import CFSG.CGT.T75M.SzData

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.CGT.Timmesfeld75 CFSG.Open

section Zof

variable {K : Type*} [Group K]

@[expose] def zOf (Q : Subgroup K) : Subgroup K := (Subgroup.center ↥Q).map Q.subtype

theorem mem_zOf {Q : Subgroup K} {w : K} : w ∈ zOf Q ↔ w ∈ Q ∧ ∀ x ∈ Q, x * w = w * x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun x hx => congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hx⟩)⟩
  · rintro ⟨hw, hc⟩
    exact ⟨⟨w, hw⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2), rfl⟩

theorem conjSubgroup_zOf (g : K) (Q : Subgroup K) :
    conjSubgroup g (zOf Q) = zOf (conjSubgroup g Q) := by
  ext w
  rw [mem_conjSubgroup, mem_zOf, mem_zOf]
  constructor
  · rintro ⟨hQ, hc⟩
    refine ⟨mem_conjSubgroup.2 hQ, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ Q := mem_conjSubgroup.1 hx
    have h := hc _ hx'
    calc x * w = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = w * x := by group
  · rintro ⟨hQ, hc⟩
    refine ⟨mem_conjSubgroup.1 hQ, fun x hx => ?_⟩
    have hx' : g * x * g⁻¹ ∈ conjSubgroup g Q := mem_conjSubgroup.2 (by simpa [mul_assoc] using hx)
    have h := hc _ hx'
    calc x * (g⁻¹ * w * g) = g⁻¹ * ((g * x * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * x * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * w * g) * x := by group

theorem normalizer_le_normalizer_zOf (Q : Subgroup K) :
    Subgroup.normalizer (Q : Set K) ≤ Subgroup.normalizer ((zOf Q : Subgroup K) : Set K) := by
  intro n hn
  rw [mem_normalizer_iff_conjSubgroup_eq] at hn ⊢
  rw [conjSubgroup_zOf, hn]

theorem coe_smul_eq_conjSubgroup (g : K) (Q : Sylow 2 K) :
    ((g • Q : Sylow 2 K) : Subgroup K) = conjSubgroup g (Q : Subgroup K) := by
  ext x
  rw [Sylow.coe_subgroup_smul, mem_conjSubgroup, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

end Zof

section Quotient

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

set_option quotPrecheck false in
local notation "TQ" =>
  (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

set_option quotPrecheck false in
local notation "T₁Q" =>
  (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))

omit [Finite G] in
theorem Sec3.exists_lift_involution_of_conj (hS : Sec3 T T₁) {ā : XQ}
    (hconj : ∃ gb : XQ, ā ∈ conjSubgroup gb TQ) :
    ∃ (a : G) (ha : a ∈ T ⊔ T₁), a * a = 1 ∧
      QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨a, ha⟩ = ā := by
  obtain ⟨gb, hgb⟩ := hconj
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have h1 : (g : XQ)⁻¹ * ā * (g : XQ) ∈ TQ := mem_conjSubgroup.1 hgb
  obtain ⟨y, hy, hyā⟩ := Subgroup.mem_map.1 h1
  have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.1 hy
  have hπa : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) (g * y * g⁻¹) = ā := by
    have e : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) g = (g : XQ) := rfl
    rw [map_mul, map_mul, map_inv, e, hyā]
    group
  have hcoe : ((g * y * g⁻¹ : ↥(T ⊔ T₁)) : G) = (g : G) * (y : G) * (g : G)⁻¹ := rfl
  refine ⟨((g * y * g⁻¹ : ↥(T ⊔ T₁)) : G), (g * y * g⁻¹).2, ?_, hπa⟩
  have hyy : (y : G) * y = 1 := elemAbelian_mul_self hS.cfg.wc.1 hyT
  rw [hcoe]
  calc (g : G) * y * (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹)
      = (g : G) * ((y : G) * y) * (g : G)⁻¹ := by group
    _ = 1 := by rw [hyy]; group

omit [Finite G] in
theorem Sec3.eq_one_of_real (hS : Sec3 T T₁) {x : G} (hxX : x ∈ T ⊔ T₁)
    (hodd : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩)))
    (hx1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩ ≠ 1)
    {a b : G} (haX : a ∈ T ⊔ T₁) (hbX : b ∈ T ⊔ T₁) (haa : a * a = 1) (hbb : b * b = 1)
    (hπab : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x, hxX⟩ =
      QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨a * b, (T ⊔ T₁).mul_mem haX hbX⟩) :
    ∀ m ∈ cfgM T T₁, x * m * x⁻¹ = m → m = 1 := by
  intro m hm hxm
  have habX : a * b ∈ T ⊔ T₁ := (T ⊔ T₁).mul_mem haX hbX
  have hno : ¬ ∃ P : Subgroup G, P ≤ T ⊔ T₁ ∧ IsPGroup 2 P ∧ a ∈ P ∧ b ∈ P := by
    rintro ⟨P, -, hP, haP, hbP⟩
    have hPsub : IsPGroup 2 (P.subgroupOf (T ⊔ T₁)) := hP.comap_subtype
    have hmem : (⟨a * b, habX⟩ : ↥(T ⊔ T₁)) ∈ P.subgroupOf (T ⊔ T₁) :=
      Subgroup.mem_subgroupOf.2 (P.mul_mem haP hbP)
    exact hx1 (hπab ▸ eq_one_of_odd_orderOf_map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) hPsub hmem (hπab ▸ hodd))
  have hC := hS.cfgM_inf_centralizer_inf_centralizer_of_not_common_two_group haX haa hbX hbb hno
  have hconj := hS.conj_cfgM_eq_of_map_eq hxX habX hπab hm
  rw [hxm] at hconj
  exact eq_one_of_conj_mul_eq_of_inf_centralizer hS.cfg.isElemAbelian_cfgM haa hbb
    (fun m' hm' => hS.cfg.conj_mem_cfgM haX hm') hC hm hconj.symm

theorem Sec3.exists_pair_torus_sz (hS : Sec3 T T₁)
    (hS' : Sec3 T₁ T) {a : ℕ} (ha : 1 ≤ a) (e : XQ ≃* Sz a) :
    ∃ k ∈ T ⊔ T₁, k ∈ Subgroup.normalizer (T : Set G) ∧ k ∈ Subgroup.normalizer (T₁ : Set G) ∧
      k ≠ 1 ∧ ∀ m ∈ cfgM T T₁, k * m * k⁻¹ = m → m = 1 := by
  classical
  have hset := szSetting_of_equiv ha e
  have hK : CFSG.BenderSuzuki.IsBenderGroup XQ :=
    CFSG.ComponentClassification.Asc76X.isBenderGroup_of_mulEquiv_sz ha e
  have hTs : StrongWC TQ := CFSG.CGT.T75M.strongWC_map hS
  have hT1 : TQ ≠ ⊥ := hS.map_ne_bot
  obtain ⟨Q₀, hTQ⟩ := (isPGroup_two_of_isElemAbelian hTs.1).exists_le_sylow
  have hTeq : TQ = zOf (Q₀ : Subgroup XQ) :=
    CFSG.CGT.T75M.eq_center_of_strongWC hK hTs hT1 Q₀ hTQ
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS.conj
  have hconj := conjSubgroup_map_eq_right hx₀X hx₀
  set xq₀ : XQ := QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀X⟩ with hxq₀
  set Q₁ : Sylow 2 XQ := xq₀ • Q₀ with hQ₁
  have hT₁eq : T₁Q = zOf (Q₁ : Subgroup XQ) := by
    rw [← hconj, hTeq, conjSubgroup_zOf, hQ₁, coe_smul_eq_conjSubgroup]
  have hne : Q₀ ≠ Q₁ := by
    intro h
    apply hS.map_ne_map
    rw [hT₁eq, hTeq, ← h]
  obtain ⟨y, w, hy₀, hy₁, hy1, hww, hwy⟩ := exists_inverted_pair hset hne
  have hHT : Subgroup.zpowers y ≤ Subgroup.normalizer (TQ : Set XQ) := by
    rw [hTeq, Subgroup.zpowers_le]
    exact normalizer_le_normalizer_zOf _ hy₀
  have hHT₁ : Subgroup.zpowers y ≤ Subgroup.normalizer (T₁Q : Set XQ) := by
    rw [hT₁eq, Subgroup.zpowers_le]
    exact normalizer_le_normalizer_zOf _ hy₁
  have hyodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (hset.odd_inter Q₀ Q₁ hne) (Subgroup.orderOf_dvd_natCard _ ⟨hy₀, hy₁⟩)
  have hHodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers]; exact hyodd
  have hM2 : IsPGroup 2 ((cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM).comap_subtype
  obtain ⟨K₀, hK₀card, hK₀H, hK₀1⟩ :=
    osg_exists_lift ((cfgM T T₁).subgroupOf (T ⊔ T₁)) hM2 (Subgroup.zpowers y) hHodd
  have hK₀gt : 1 < Nat.card K₀ := by
    rw [hK₀card, Nat.card_zpowers]
    have := orderOf_pos y
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    omega
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    ((Subgroup.one_lt_card_iff_ne_bot K₀).1 hK₀gt)
  have hk : (k : ↥(T ⊔ T₁)) ∈ K₀ := k.2
  have hk1' : (k : ↥(T ⊔ T₁)) ≠ 1 := fun h' => hk1 (Subtype.ext h')
  have hkX : ((k : ↥(T ⊔ T₁)) : G) ∈ T ⊔ T₁ := (k : ↥(T ⊔ T₁)).2
  have hπk := hK₀H _ hk
  refine ⟨((k : ↥(T ⊔ T₁)) : G), hkX, ?_, ?_, fun h1 => hk1' (Subtype.ext h1), ?_⟩
  · refine mem_normalizer_of_conjSubgroup_eq
      (hS.conjSubgroup_eq_of_le_mul_cfgM hkX fun z hz => ?_)
    have hzX : z ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hkX hz
    refine osg_exists_eq_mul_cfgM_of_map_mem_left hzX ?_
    have h1 := map_mem_conjSubgroup_map hkX hzX hz
    have h2 : conjSubgroup
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩)
        TQ = TQ := mem_normalizer_iff_conjSubgroup_eq.1 (hHT hπk)
    rwa [h2] at h1
  · have hkX' : ((k : ↥(T ⊔ T₁)) : G) ∈ T₁ ⊔ T := by rw [sup_comm]; exact hkX
    refine mem_normalizer_of_conjSubgroup_eq
      (hS'.conjSubgroup_eq_of_le_mul_cfgM hkX' fun z hz => ?_)
    have hzX' : z ∈ T₁ ⊔ T := conjSubgroup_le_of_le_of_mem le_sup_left hkX' hz
    have hzX : z ∈ T ⊔ T₁ := by rw [sup_comm]; exact hzX'
    have hzc : z ∈ conjSubgroup ((k : ↥(T ⊔ T₁)) : G) T₁ := hz
    have h1 := map_mem_conjSubgroup_map_right hkX hzX hzc
    have h2 : conjSubgroup
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩)
        T₁Q = T₁Q := mem_normalizer_iff_conjSubgroup_eq.1 (hHT₁ hπk)
    rw [h2] at h1
    obtain ⟨t, ht, m, hm, rfl⟩ := exists_eq_mul_cfgM_of_map_mem_right hzX h1
    exact ⟨t, ht, m, by rw [cfgM_symm]; exact hm, rfl⟩
  ·
    set kq : XQ := QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
      ⟨((k : ↥(T ⊔ T₁)) : G), hkX⟩ with hkq
    have hkq1 : kq ≠ 1 := fun h' => hk1' (hK₀1 _ hk h')
    have hkqH : kq ∈ Subgroup.zpowers y := hπk
    have hkqodd : Odd (orderOf kq) :=
      Odd.of_dvd_nat hyodd (orderOf_dvd_of_mem_zpowers hkqH)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hkqH
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hwk : w * kq * w⁻¹ = kq⁻¹ := by
      rw [← hj]
      have : w * y ^ j * w⁻¹ = (w * y * w⁻¹) ^ j := by simp
      rw [this, hwy, inv_zpow]
    have hbb : (w * kq) * (w * kq) = 1 := by
      calc (w * kq) * (w * kq) = (w * kq * w⁻¹) * kq := by rw [hwinv]; group
        _ = 1 := by rw [hwk]; group
    have hw1 : w ≠ 1 := by
      intro h1
      rw [h1] at hwy
      simp only [one_mul, inv_one, mul_one] at hwy
      have : y * y = 1 := by
        calc y * y = y * y⁻¹⁻¹ := by rw [inv_inv]
          _ = 1 := by rw [← hwy]; group
      have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact this)
      have h3 : orderOf y = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h4 | h4
        · exact h4
        · rw [h4] at hyodd; exact absurd hyodd (by decide)
      exact hy1 (orderOf_eq_one_iff.1 h3)
    have hwk1 : w * kq ≠ 1 := by
      intro h1
      have hwk' : w = kq⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hwH : w ∈ Subgroup.zpowers y := by
        rw [hwk']; exact Subgroup.inv_mem _ hkqH
      have hwodd : Odd (orderOf w) := Odd.of_dvd_nat hyodd (orderOf_dvd_of_mem_zpowers hwH)
      have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
      have h3 : orderOf w = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h4 | h4
        · exact h4
        · rw [h4] at hwodd; exact absurd hwodd (by decide)
      exact hw1 (orderOf_eq_one_iff.1 h3)
    have hinvconj : ∀ ā : XQ, ā * ā = 1 → ā ≠ 1 → ∃ gb : XQ, ā ∈ conjSubgroup gb TQ := by
      intro ā hā hā1
      obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
      have htt : (t : XQ) * t = 1 := elemAbelian_mul_self hS.isElemAbelian_map t.2
      have hto : orderOf (t : XQ) = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact htt) (fun h => ht1 (Subtype.ext h))
      have hāo : orderOf ā = 2 := orderOf_eq_prime (by rw [pow_two]; exact hā) hā1
      obtain ⟨c, hc⟩ := isConj_iff.1
        (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hK hto hāo)
      refine ⟨c, mem_conjSubgroup.2 ?_⟩
      have : c⁻¹ * ā * c = t := by rw [← hc]; group
      rw [this]; exact t.2
    obtain ⟨a₁, haX, haa, hπa⟩ := Sec3.exists_lift_involution_of_conj hS (ā := w)
      (hinvconj w hww hw1)
    obtain ⟨b₁, hbX, hbb', hπb⟩ := Sec3.exists_lift_involution_of_conj hS (ā := w * kq)
      (hinvconj _ hbb hwk1)
    refine Sec3.eq_one_of_real hS hkX hkqodd hkq1 haX hbX haa hbb' ?_
    have : (⟨a₁ * b₁, (T ⊔ T₁).mul_mem haX hbX⟩ : ↥(T ⊔ T₁)) = ⟨a₁, haX⟩ * ⟨b₁, hbX⟩ := rfl
    rw [this, map_mul, hπa, hπb]
    calc kq = (w * w) * kq := by rw [hww]; group
      _ = w * (w * kq) := by group

end Quotient

theorem szTwoPointTorus : SzTwoPointTorus := by
  intro G _ _ T T₁ hS hS' _ a ha ⟨e⟩
  exact Sec3.exists_pair_torus_sz hS hS' ha e

end CFSG.CGT.PushingUpLit.T2KR
