module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Common

public section

namespace CFSG.ComponentClassification.Foote47

open scoped MatrixGroups

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

namespace P4Data

variable {M T S P : Subgroup G} {t z w : G}

theorem mem_innerAct_t_of_mem_innerAct_z (h : FooteSec4 G L) (d : P4Data L M T S P t z w)
    {x : G} (hxt : x ∈ centralizer ({t} : Set G))
    (hx : x ∈ innerAct (footeF L z)) : x ∈ innerAct (footeF L t) := by
  obtain ⟨Q₀, hd⟩ := d.c.hd
  have dz := zData_of h d.c.hv.hM d.c.hTsyl hd.hz hd.hzT hd.hzc
  have htK : t ∈ coreActionKernel (footeF L z) := dz.hTKle d.c.htT
  obtain ⟨hB, -, -, -, hfix⟩ := footeF_spec h dz.hKmax dz.hKF d.c.hv.ht htK
  have hKb : IsTwoComponentAt t (footeFixed (footeF L z) t) := hfix ▸ hB
  obtain ⟨hxN, hin⟩ := mem_innerAct_iff.mp hx
  have hxNt : x ∈ normalizer (footeFixed (footeF L z) t : Set G) := by
    rw [hfix]
    exact d.centralizer_le_normalizer_t h hxt
  have h1 := oddBarConj_mem_range_conj_of_footeFixed dz.hKmax.1 d.c.hv.ht htK hKb hxN hxNt hxt
    hin
  have h2 : x ∈ innerAct (footeFixed (footeF L z) t) := mem_innerAct_iff.mpr ⟨hxNt, h1⟩
  rwa [hfix] at h2

theorem exists_sylow_image (h : FooteSec4 G L) (d : P4Data L M T S P t z w) :
    ∃ (ε : footeF L t ⧸ pPrimeCore 2 (footeF L t) ≃* L ⧸ Open.fusionZStar L)
      (RS : Sylow 2 (L ⧸ Open.fusionZStar L)),
      ∀ s : L ⧸ Open.fusionZStar L, s ∈ (RS : Subgroup (L ⧸ Open.fusionZStar L)) ↔
        ∃ (r : G) (hr : r ∈ P ⊓ footeF L t),
          s = ε ((⟨r, (mem_inf.mp hr).2⟩ : footeF L t) : footeF L t ⧸ pPrimeCore 2 _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ε⟩⟩ := d.quotient_t h
  obtain ⟨R₀, hR₀⟩ := (d.isSylowOf_R h).exists_sylow_eq_subgroupOf
  set R₁ := R₀.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 (footeF L t)))
  refine ⟨ε, R₁.mapSurjective (f := ε.toMonoidHom) ε.surjective, fun s => ?_⟩
  constructor
  · rintro ⟨_, ⟨⟨r, hrF⟩, hr, rfl⟩, rfl⟩
    have hr' : r ∈ P ⊓ footeF L t := by
      have := hR₀ ▸ hr
      exact this
    exact ⟨r, hr', rfl⟩
  · rintro ⟨r, hr, rfl⟩
    have hr' : (⟨r, (mem_inf.mp hr).2⟩ : footeF L t) ∈ (R₀ : Subgroup (footeF L t)) := by
      rw [hR₀]
      exact hr
    exact ⟨_, ⟨_, hr', rfl⟩, rfl⟩

theorem orderOf_mk_eq_two (d : P4Data L M T S P t z w) {u : G} (huR : u ∈ P ⊓ footeF L t)
    (hu : orderOf u = 2) :
    orderOf ((⟨u, (mem_inf.mp huR).2⟩ : footeF L t) : footeF L t ⧸ pPrimeCore 2 _) = 2 := by
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [← QuotientGroup.mk_pow]
    have h2 : (⟨u, (mem_inf.mp huR).2⟩ : footeF L t) ^ 2 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hu]
      exact pow_orderOf_eq_one u)
    rw [h2, QuotientGroup.mk_one]
  · rw [QuotientGroup.eq_one_iff, mem_pPrimeCore_iff_mem_oddCoreIn] at h1
    have h3 := eq_one_of_mem_of_odd (d.c.hPsyl.isPGroup.to_le inf_le_left)
      (odd_card_oddCoreIn _) huR h1
    rw [h3, orderOf_one] at hu
    omega

theorem w_mem_commutator (h : FooteSec4 G L) (hCI : Foote47CentralInvolution)
    (d : P4Data L M T S P t z w) {τ : G} (hτP : τ ∈ P) (hτ2 : τ * τ = 1)
    (hτI : τ ∉ innerAct (footeF L t)) : w ∈ ⁅P, P⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := footeF L t with hF
  set N := normalizer (F : Set G) with hN
  set SL := L ⧸ Open.fusionZStar L with hSL
  obtain ⟨ε, RS, hRS⟩ := d.exists_sylow_image h
  set Φ : ↥N →* MulAut SL := (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj F) with hΦ
  have hPN : P ≤ N := d.P_le_normalizer h
  have hτN : τ ∈ N := hPN hτP
  have hΦF : ∀ (r : G) (hrF : r ∈ F), Φ ⟨r, le_normalizer hrF⟩ =
      MulAut.conj (ε ((⟨r, hrF⟩ : F) : F ⧸ pPrimeCore 2 F)) := by
    intro r hrF
    rw [hΦ, MonoidHom.comp_apply, oddBarConj_eq_conj F hrF]
    exact FooteLit.MulAut.congr_conj ε _
  have hinner : ∀ (x : G) (hx : x ∈ N), Φ ⟨x, hx⟩ ∈ (MulAut.conj : SL →* MulAut SL).range →
      x ∈ innerAct F := by
    rintro x hx ⟨s, hs⟩
    refine mem_innerAct_iff.mpr ⟨hx, ε.symm s, ?_⟩
    apply (MulAut.congr ε).injective
    rw [FooteLit.MulAut.congr_conj, MulEquiv.apply_symm_apply, hs]
    rfl
  set τ' := Φ ⟨τ, hτN⟩ with hτ'
  have hτ'2 : τ' * τ' = 1 := by
    rw [hτ', ← map_mul, show (⟨τ, hτN⟩ : N) * ⟨τ, hτN⟩ = 1 from Subtype.ext hτ2, map_one]
  have hτ'out : τ' ∉ (MulAut.conj : SL →* MulAut SL).range := fun h1 => hτI (hinner τ hτN h1)
  have hact : ∀ (x : G) (hx : x ∈ P) (r : G) (hrF : r ∈ F),
      Φ ⟨x, hPN hx⟩ (ε ((⟨r, hrF⟩ : F) : F ⧸ pPrimeCore 2 F)) =
        ε ((⟨x * r * x⁻¹, (mem_normalizer_iff.mp (hPN hx) r).mp hrF⟩ : F) :
          F ⧸ pPrimeCore 2 F) := by
    intro x hx r hrF
    rw [hΦ, MonoidHom.comp_apply]
    change ε (GSThmB.oddBarConj F ⟨x, hPN hx⟩ (ε.symm (ε _))) = _
    rw [MulEquiv.symm_apply_apply, GSThmB.oddBarConj_apply_mk]
  have hRnorm : ∀ x ∈ P, ∀ r ∈ P ⊓ F, x * r * x⁻¹ ∈ P ⊓ F := fun x hx r hr =>
    mem_inf.mpr ⟨mul_mem (mul_mem hx (mem_inf.mp hr).1) (inv_mem hx),
      (mem_normalizer_iff.mp (hPN hx) r).mp (mem_inf.mp hr).2⟩
  have hmapR : ∀ x (hx : x ∈ P),
      (RS : Subgroup SL).map (Φ ⟨x, hPN hx⟩).toMonoidHom = RS := by
    intro x hx
    refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective (Φ ⟨x, hPN hx⟩).injective])
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (hRS s).mp hs
    rw [MulEquiv.coe_toMonoidHom, hact x hx r (mem_inf.mp hr).2]
    exact (hRS _).mpr ⟨_, hRnorm x hx r hr, rfl⟩
  have hwR := d.w_mem_R
  set c := ε ((⟨w, (mem_inf.mp hwR).2⟩ : F) : F ⧸ pPrimeCore 2 F) with hc
  have hcR : c ∈ (RS : Subgroup SL) := (hRS c).mpr ⟨w, hwR, rfl⟩
  have hc2 : orderOf c = 2 := by rw [hc, MulEquiv.orderOf_eq, d.orderOf_mk_eq_two hwR d.hw]
  have hcZ : ∀ s ∈ (RS : Subgroup SL), c * s = s * c := by
    intro s hs
    obtain ⟨r, hr, rfl⟩ := (hRS s).mp hs
    rw [hc, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (d.hwc r (d.P_le_S (mem_inf.mp hr).1)).symm
  have hτc : τ' c = c := by
    rw [hτ', hc, hact τ hτP w (mem_inf.mp hwR).2]
    congr 2
    exact Subtype.ext (by
      show τ * w * τ⁻¹ = w
      rw [d.hwc τ (d.P_le_S hτP), mul_inv_cancel_right])
  have hmem := hCI SL h.footeFamilyType RS τ' hτ'2 hτ'out (hmapR τ hτP) c hcR hc2 hcZ hτc
  set D := (P ⊓ F) ⊔ zpowers τ with hD
  have hDP : D ≤ P := sup_le inf_le_left (zpowers_le.mpr hτP)
  have hDN : D ≤ N := hDP.trans hPN
  set D' := D.subgroupOf N with hD'
  have hmapD : D'.map Φ = (RS : Subgroup SL).map (MulAut.conj : SL →* MulAut SL) ⊔
      zpowers τ' := by
    have h1 : D' = (P ⊓ F).subgroupOf N ⊔ (zpowers τ).subgroupOf N :=
      subgroupOf_sup (inf_le_left.trans hPN) (zpowers_le.mpr hτN)
    rw [h1, Subgroup.map_sup]
    congr 1
    · ext u
      constructor
      · rintro ⟨⟨r, hrN⟩, hr, rfl⟩
        have hr' : r ∈ P ⊓ F := hr
        refine ⟨ε ((⟨r, (mem_inf.mp hr').2⟩ : F) : F ⧸ pPrimeCore 2 F),
          (hRS _).mpr ⟨r, hr', rfl⟩, ?_⟩
        exact (hΦF r (mem_inf.mp hr').2).symm
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨r, hr, rfl⟩ := (hRS s).mp hs
        exact ⟨⟨r, le_normalizer (mem_inf.mp hr).2⟩, hr, hΦF r (mem_inf.mp hr).2⟩
    · have h2 : (zpowers τ).subgroupOf N = zpowers (⟨τ, hτN⟩ : N) := by
        ext y
        rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k, Subtype.ext (by rw [← hk]; simp)⟩
        · rintro ⟨k, hk⟩
          exact ⟨k, by rw [← hk]; simp⟩
      rw [h2, MonoidHom.map_zpowers]
  rw [← hmapD, ← Subgroup.map_commutator] at hmem
  obtain ⟨k, hk, hkc⟩ := hmem
  have hwN : w ∈ N := hPN d.w_mem_P
  have hkw : Φ (k⁻¹ * ⟨w, hwN⟩) = 1 := by
    rw [map_mul, map_inv, hkc, hc, ← hΦF w (mem_inf.mp hwR).2, inv_mul_cancel]
  have hkwC : ((k : G))⁻¹ * w ∈ coreActionKernel F := by
    have h0 : MulAut.congr ε (GSThmB.oddBarConj F (k⁻¹ * ⟨w, hwN⟩)) = 1 := hkw
    have h1 : GSThmB.oddBarConj F (k⁻¹ * ⟨w, hwN⟩) = 1 :=
      (map_eq_one_iff _ (MulAut.congr ε).injective).mp h0
    exact GSThmB.mem_coreActionKernel_of_oddBarConj_eq_one h1
  have hcomm_le : ⁅D', D'⁆ ≤ D' := (Subgroup.commutator_le).mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hkD : (k : G) ∈ D := (hcomm_le hk : k ∈ D')
  have hwD : w ∈ D := mem_sup_left hwR
  have hDC : ∀ y ∈ D, y ∈ coreActionKernel F → y = 1 := by
    intro y hy hyC
    have hy' : y ∈ ((zpowers τ ⊔ (P ⊓ F) : Subgroup G) : Set G) := by rw [sup_comm]; exact hy
    have hτnorm : τ ∈ normalizer ((P ⊓ F : Subgroup G) : Set G) := by
      refine mem_normalizer_iff.mpr fun r => ⟨fun hr => hRnorm τ hτP r hr, fun hr => ?_⟩
      have h1 := hRnorm τ⁻¹ (inv_mem hτP) _ hr
      rwa [show τ⁻¹ * (τ * r * τ⁻¹) * τ⁻¹⁻¹ = r by group] at h1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (zpowers_le.mpr hτnorm)] at hy'
    obtain ⟨a, ha, r, hr, rfl⟩ := hy'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    have hpow : τ ^ n = 1 ∨ τ ^ n = τ := by
      rcases Int.emod_two_eq_zero_or_one n with h0 | h0
      · left
        rw [← Int.emod_add_mul_ediv n 2, h0, zero_add, zpow_mul,
          show τ ^ (2 : ℤ) = 1 by rw [zpow_two, hτ2], one_zpow]
      · right
        rw [← Int.emod_add_mul_ediv n 2, h0, zpow_add, zpow_one, zpow_mul,
          show τ ^ (2 : ℤ) = 1 by rw [zpow_two, hτ2], one_zpow, mul_one]
    have hrO : ∀ {r : G}, r ∈ P ⊓ F → r ∈ coreActionKernel F → r = 1 := by
      intro r hr hrC
      exact eq_one_of_mem_of_odd (d.c.hPsyl.isPGroup.to_le inf_le_left) (odd_card_oddCoreIn F)
        hr (mem_oddCoreIn_of_mem_coreActionKernel (d.center_eq_bot_t h) (mem_inf.mp hr).2 hrC)
    rcases hpow with h0 | h0
    · simp only [h0, one_mul] at hyC ⊢
      exact hrO hr hyC
    · exfalso
      simp only [h0] at hyC
      apply hτI
      have h1 : τ = (τ * r) * r⁻¹ := by group
      rw [h1]
      exact mul_mem (coreActionKernel_le_innerAct F hyC)
        (le_innerAct F (inv_mem (mem_inf.mp hr).2))
  have hk1 : ((k : G))⁻¹ * w = 1 :=
    hDC _ (mul_mem (inv_mem hkD) hwD) hkwC
  have hkw' : (k : G) = w := by
    calc (k : G) = k * ((k : G)⁻¹ * w) := by rw [hk1, mul_one]
      _ = w := by group
  have hcomm : ⁅D, D⁆ ≤ ⁅P, P⁆ := commutator_mono hDP hDP
  apply hcomm
  rw [← hkw']
  have h1 : (⁅D', D'⁆).map N.subtype = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, hD', subgroupOf_map_subtype, inf_eq_left.mpr hDN]
  rw [← h1]
  exact ⟨k, hk, rfl⟩

theorem exists_commutator_ne_one (h : FooteSec4 G L) (hOF : Foote47OuterOrderFour)
    (d : P4Data L M T S P t z w) {x : G} (hxP : x ∈ P) (hx4 : orderOf x = 4)
    (hx2 : x ^ 2 ∉ innerAct (footeF L t)) : ∃ r ∈ P ⊓ footeF L t, x * r * x⁻¹ ≠ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := footeF L t with hF
  set N := normalizer (F : Set G) with hN
  set SL := L ⧸ Open.fusionZStar L with hSL
  obtain ⟨ε, RS, hRS⟩ := d.exists_sylow_image h
  set Φ : ↥N →* MulAut SL := (MulAut.congr ε).toMonoidHom.comp (GSThmB.oddBarConj F) with hΦ
  have hPN : P ≤ N := d.P_le_normalizer h
  have hxN : x ∈ N := hPN hxP
  have hinner : ∀ (y : G) (hy : y ∈ N), Φ ⟨y, hy⟩ ∈ (MulAut.conj : SL →* MulAut SL).range →
      y ∈ innerAct F := by
    rintro y hy ⟨s, hs⟩
    refine mem_innerAct_iff.mpr ⟨hy, ε.symm s, ?_⟩
    apply (MulAut.congr ε).injective
    rw [FooteLit.MulAut.congr_conj, MulEquiv.apply_symm_apply, hs]
    rfl
  have hact : ∀ (y : G) (hy : y ∈ P) (r : G) (hrF : r ∈ F),
      Φ ⟨y, hPN hy⟩ (ε ((⟨r, hrF⟩ : F) : F ⧸ pPrimeCore 2 F)) =
        ε ((⟨y * r * y⁻¹, (mem_normalizer_iff.mp (hPN hy) r).mp hrF⟩ : F) :
          F ⧸ pPrimeCore 2 F) := by
    intro y hy r hrF
    rw [hΦ, MonoidHom.comp_apply]
    change ε (GSThmB.oddBarConj F ⟨y, hPN hy⟩ (ε.symm (ε _))) = _
    rw [MulEquiv.symm_apply_apply, GSThmB.oddBarConj_apply_mk]
  have hRnorm : ∀ y ∈ P, ∀ r ∈ P ⊓ F, y * r * y⁻¹ ∈ P ⊓ F := fun y hy r hr =>
    mem_inf.mpr ⟨mul_mem (mul_mem hy (mem_inf.mp hr).1) (inv_mem hy),
      (mem_normalizer_iff.mp (hPN hy) r).mp (mem_inf.mp hr).2⟩
  have hmapR : (RS : Subgroup SL).map (Φ ⟨x, hxN⟩).toMonoidHom = RS := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective (Φ ⟨x, hxN⟩).injective])
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (hRS s).mp hs
    rw [MulEquiv.coe_toMonoidHom, hact x hxP r (mem_inf.mp hr).2]
    exact (hRS _).mpr ⟨_, hRnorm x hxP r hr, rfl⟩
  set φ := Φ ⟨x, hxN⟩ with hφ
  have hpowN : ∀ n : ℕ, φ ^ n = Φ ⟨x ^ n, pow_mem hxN n⟩ := fun n => by
    rw [hφ, ← map_pow]
    rfl
  have hφ2 : φ ^ 2 ≠ 1 := by
    intro h1
    apply hx2
    refine hinner _ (pow_mem hxN 2) ⟨1, ?_⟩
    rw [map_one, ← hpowN, h1]
  have hdvd : orderOf φ ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hx4, ← Subgroup.orderOf_mk x hxN]
    exact orderOf_map_dvd Φ _
  obtain ⟨k, hk, hkφ⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk2 : k = 2 := by
    by_contra hne
    apply hφ2
    rw [← orderOf_dvd_iff_pow_eq_one, hkφ]
    exact (pow_dvd_pow 2 (show k ≤ 1 by omega)).trans (by norm_num)
  have hφ4 : orderOf φ = 4 := by rw [hkφ, hk2]; norm_num
  have hinnerpow : ∀ n : ℕ, φ ^ n ∈ (MulAut.conj : SL →* MulAut SL).range → φ ^ n = 1 := by
    intro n hn
    have hxn : x ^ n ∈ innerAct F := hinner _ (pow_mem hxN n) (hpowN n ▸ hn)
    have hmod : x ^ n = x ^ (n % 4) := by rw [← hx4, pow_mod_orderOf]
    have hsq : x ^ (2 * n) ∈ innerAct F := by
      rw [pow_mul']
      exact pow_mem hxn 2
    have hmod2 : x ^ (2 * n) = x ^ (2 * n % 4) := by rw [← hx4, pow_mod_orderOf]
    have hφn : φ ^ n = φ ^ (n % 4) := by rw [← hφ4, pow_mod_orderOf]
    have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : n % 4
    · rw [hφn, pow_zero]
    · exfalso
      apply hx2
      rw [show 2 * n % 4 = 2 by omega] at hmod2
      rw [← hmod2]
      exact hsq
    · exfalso
      apply hx2
      rw [hmod] at hxn
      exact hxn
    · exfalso
      apply hx2
      rw [show 2 * n % 4 = 2 by omega] at hmod2
      rw [← hmod2]
      exact hsq
  obtain ⟨s, hs, hφs⟩ := hOF SL h.footeFamilyType RS φ ⟨2, by rw [hφ4]; norm_num⟩
    (by rw [hφ4]) hinnerpow hmapR
  obtain ⟨r, hr, rfl⟩ := (hRS s).mp hs
  refine ⟨r, hr, fun h1 => hφs ?_⟩
  rw [hφ, hact x hxP r (mem_inf.mp hr).2]
  congr 2
  exact Subtype.ext h1

end P4Data

end CFSG.ComponentClassification.Foote47
