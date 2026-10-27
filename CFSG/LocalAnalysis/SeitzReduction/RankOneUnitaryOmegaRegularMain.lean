module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmegaRegular

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.GH74.Uniqueness.Bender AffineModel

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem hasRegularNormalSubgroup_of_even_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) (heven : Even f) :
    HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range := by
  classical
  set R₁ := szR (szT₁ L T) R₂ t with hR₁def
  set Y := normalizer (R₁ : Set G) with hYdef
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨hR₁u, -, -, -, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hYK : Y ≤ normalizer (R₂ : Set G) := fun y hy => (mem_inf.mp (hNR₁ hy)).2
  have hYH : Y ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := fun y hy =>
    (mem_inf.mp (hNR₁ hy)).1
  have htH : t ∉ szT₁ L T ⊔ R₂ := fun h1 => h.not_mem_szT₁_of_card_sylow hS2 (hTH ⟨htT, h1⟩)
  have : (R₂.subgroupOf R₁).Normal := normal_subgroupOf_szR hR
  set N := R₂.subgroupOf R₁ with hNdef
  set ρ := quotConj Y le_rfl hYK with hρdef
  have hρ : ∀ (y : Y) (x : R₁), ρ y (x : R₁ ⧸ N) =
      ((⟨(y : G) * x * (y : G)⁻¹, (mem_normalizer_iff.mp y.2 x).mp x.2⟩ : R₁) : R₁ ⧸ N) :=
    fun y x => quotConj_mk Y le_rfl hYK y x
  have hsqR₁ : ∀ x ∈ R₁, x ^ 2 ∈ R₂ := fun x hx =>
    hR.le (h.sq_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 (hR₁u ▸ hx))
  have hcommR₁ : ∀ x ∈ R₁, ∀ x' ∈ R₁, x * x' * x⁻¹ * x'⁻¹ ∈ R₂ := fun x hx x' hx' =>
    hR.le (h.comm_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 (hR₁u ▸ hx) (hR₁u ▸ hx'))
  have hmkeq : ∀ x x' : R₁, (x : R₁ ⧸ N) = (x' : R₁ ⧸ N) ↔ (x : G)⁻¹ * x' ∈ R₂ := fun x x' =>
    QuotientGroup.eq.trans mem_subgroupOf
  have hVcomm : ∀ a b : R₁ ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H x' => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmkeq]
    have := hcommR₁ _ (inv_mem x'.2) _ (inv_mem x.2)
    simpa [mul_assoc] using this
  let _ : CommGroup (R₁ ⧸ N) := { (inferInstance : Group (R₁ ⧸ N)) with mul_comm := hVcomm }
  set t' : R₁ ⧸ N := ((⟨t, mem_szR_right _ _ _⟩ : R₁) : R₁ ⧸ N) with ht'
  set M := ρ.range with hM
  have hV : ∀ v : R₁ ⧸ N, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hsqR₁ _ x.2
  set U : Subgroup (R₁ ⧸ N) := ((szT₁ L T ⊔ R₂).subgroupOf R₁).map (QuotientGroup.mk' N)
    with hU
  have hHR₁ : szT₁ L T ⊔ R₂ ≤ R₁ := le_sup_left
  have memU : ∀ x : R₁, (x : R₁ ⧸ N) ∈ U ↔ (x : G) ∈ szT₁ L T ⊔ R₂ := by
    intro x
    constructor
    · rintro ⟨z, hz, hzx⟩
      have h1 := (hmkeq z x).mp hzx
      have h2 : ((z : G) * ((z : G)⁻¹ * x)) ∈ szT₁ L T ⊔ R₂ :=
        mul_mem (mem_subgroupOf.mp hz) (mem_sup_right h1)
      simpa using h2
    · intro hx
      exact ⟨x, mem_subgroupOf.mpr hx, rfl⟩
  have hUrep : ∀ u ∈ U, ∃ w, ∃ hw : w ∈ szT₁ L T,
      u = ((⟨w, le_szR_left _ _ _ hw⟩ : R₁) : R₁ ⧸ N) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, r, hr, hwr⟩ := hR.mem_sup_iff.mp (mem_subgroupOf.mp hz)
    refine ⟨w, hw, ?_⟩
    rw [QuotientGroup.mk'_apply, eq_comm, hmkeq]
    have : (w : G)⁻¹ * (z : G) = r := by rw [← hwr]; group
    simpa [this] using hr
  have hUcard : Nat.card U = 2 ^ (2 * f) := by
    rw [hU, ← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hHR₁]
    have h1 := StrongClosureMod.relIndex_mul_card_of_le (le_sup_right : R₂ ≤ szT₁ L T ⊔ R₂)
    have h2 := hR.card_sup_mul
    rw [← h1, hT₁card, hA₁card, hR.card] at h2
    have hq : 0 < (2 ^ f) ^ 2 * 2 ^ f := by positivity
    have h3 : R₂.relIndex (szT₁ L T ⊔ R₂) * ((2 ^ f) ^ 2 * 2 ^ f) =
        2 ^ (2 * f) * ((2 ^ f) ^ 2 * 2 ^ f) := by
      rw [← mul_assoc, h2, pow_mul']
      ring
    exact Nat.eq_of_mul_eq_mul_right hq h3
  have ht'U : t' ∉ U := fun h1 => htH ((memU _).mp h1)
  have hUt : IsCompl U (zpowers t') := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxt⟩ := mem_inf.mp hx
      rcases mem_zpowers_involution_eq_one_or_eq (hV t') hxt with rfl | rfl
      · exact one_mem _
      · exact absurd hxU ht'U
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      induction v using QuotientGroup.induction_on with | H x => ?_
      obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_of_mem_szR hR x.2
      have hzR : z ∈ R₁ := zpowers_le.mpr (mem_szR_right _ _ _) hz
      have hx : x = ⟨w, hHR₁ hw⟩ * ⟨z, hzR⟩ := Subtype.ext hwz.symm
      rw [hx, QuotientGroup.mk_mul]
      refine mul_mem_sup ((memU _).mpr hw) ?_
      rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with h1 | h1
      · have : (⟨z, hzR⟩ : R₁) = 1 := Subtype.ext h1
        rw [this, QuotientGroup.mk_one]
        exact one_mem _
      · have : (⟨z, hzR⟩ : R₁) = ⟨t, mem_szR_right _ _ _⟩ := Subtype.ext h1
        rw [this]
        exact mem_zpowers t'
  have hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U := by
    rintro _ ⟨y, rfl⟩ u hu
    obtain ⟨w, hw, rfl⟩ := hUrep u hu
    rw [hρ, memU]
    exact (mem_normalizer_iff.mp (hYH y.2) w).mp (mem_sup_left hw)
  have hρtriv : ∀ y : Y, (y : G) ∈ R₁ → ρ y = 1 := by
    intro y hy
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [hρ, MulAut.one_apply, hmkeq]
    have := hcommR₁ _ hy _ (inv_mem x.2)
    simpa [mul_assoc] using this
  obtain ⟨-, -, -, hNAR₁, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hNAT₁ := h.normalizer_szA_le_of_card_sylow hS2
  set B := L ⊓ normalizer (szT₁ L T : Set G) with hB
  have hBY : B ≤ Y := fun b hb => hNAR₁ (h.inf_normalizer_le_normalizer_szA hb)
  set H : Subgroup (MulAut (R₁ ⧸ N)) := (B.subgroupOf Y).map ρ with hH
  have hHM : H ≤ M := map_le_range ρ _
  have hHt : ∀ x ∈ H, x t' = t' := by
    rintro _ ⟨b, hb, rfl⟩
    have hbL : (b : G) ∈ L := (mem_inf.mp (mem_subgroupOf.mp hb)).1
    rw [ht', hρ]
    congr 1
    apply Subtype.ext
    change (b : G) * t * (b : G)⁻¹ = t
    rw [mem_centralizer_iff.mp h.mem _ hbL, mul_inv_cancel_right]
  have hCtL : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1
  have hHn : ∀ m ∈ M, m t' = t' → ∀ x ∈ H, m * x * m⁻¹ ∈ H := by
    rintro _ ⟨y, rfl⟩ hyt _ ⟨b, hb, rfl⟩
    have h1 : (⟨(y : G) * t * (y : G)⁻¹, _⟩ : R₁) = (⟨(y : G) * t * (y : G)⁻¹,
        (mem_normalizer_iff.mp y.2 t).mp (mem_szR_right _ _ _)⟩ : R₁) := rfl
    rw [ht', hρ, hmkeq] at hyt
    set r := (y : G) * t * (y : G)⁻¹ * t with hrdef
    have hyt' : (y : G) * t * (y : G)⁻¹ = r * t := by rw [hrdef, mul_assoc _ t t, ← sq, hR.t_sq,
      mul_one]
    have hr : r ∈ R₂ := by
      have h2 : r = t * ((((y : G) * t * (y : G)⁻¹)⁻¹ * t)⁻¹) * t⁻¹ := by
        rw [hrdef, hR.t_inv]; group
      rw [h2]
      exact hR.tN _ (inv_mem (by simpa using hyt))
    have hr2 : (r * t) ^ 2 = 1 := by
      rw [← hyt', show ((y : G) * t * (y : G)⁻¹) ^ 2 = (y : G) * t ^ 2 * (y : G)⁻¹ by
        rw [sq, sq]; group, hR.t_sq, mul_one, mul_inv_cancel]
    have hrA := hR.mem_szA_of_sq_eq_one hc hr hr2
    have hyA₁ := h.normalizer_sup_le_normalizer_szA₁_of_card_sylow hS2 hR (hYH y.2)
    have hyNA := h.mem_normalizer_szA_of_conj_mem_of_card_sylow hS2 hR hc y.2 hyA₁
      (by rw [hyt']; exact mul_mem (mem_sup_left hr) (mem_sup_right (mem_zpowers t)))
    have hyT₁ := hNAT₁ hyNA
    obtain ⟨r₀, hr₀, hr₀t⟩ := hR.rho_onto r hrA
    have hr₀R₁ : r₀ ∈ R₁ := le_szR_mid _ _ _ hr₀
    have hr₀Y : r₀ ∈ Y := Subgroup.le_normalizer hr₀R₁
    set c := r₀⁻¹ * (y : G) with hcdef
    have hcY : c ∈ Y := mul_mem (inv_mem hr₀Y) y.2
    have hct : c * t = t * c := by
      have e1 : r₀ * t * r₀⁻¹ = r * t := by
        rw [← hr₀t, mul_assoc (r₀ * t * r₀⁻¹) t t, ← sq, hR.t_sq, mul_one]
      have e2 : c * t * c⁻¹ = t := by
        calc c * t * c⁻¹ = r₀⁻¹ * ((y : G) * t * (y : G)⁻¹) * r₀ := by rw [hcdef]; group
          _ = r₀⁻¹ * (r₀ * t * r₀⁻¹) * r₀ := by rw [hyt', e1]
          _ = t := by group
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [e2]
    have hcL : c ∈ normalizer (L : Set G) := hCtL (mem_centralizer_singleton_iff.mpr hct)
    have hcT₁ : c ∈ normalizer (szT₁ L T : Set G) :=
      mul_mem (inv_mem (centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun x hx => (hR.commT₁ x hx r₀ hr₀)))) hyT₁
    have hyeq : y = ⟨r₀, hr₀Y⟩ * ⟨c, hcY⟩ := Subtype.ext (by
      change (y : G) = r₀ * (r₀⁻¹ * y)
      group)
    have hρy : ρ y = ρ ⟨c, hcY⟩ := by rw [hyeq, map_mul, hρtriv _ hr₀R₁, one_mul]
    obtain ⟨hbL, hbT⟩ := mem_inf.mp (mem_subgroupOf.mp hb)
    have hcbB : c * b * c⁻¹ ∈ B := mem_inf.mpr ⟨(mem_normalizer_iff.mp hcL _).mp hbL,
      mul_mem (mul_mem hcT₁ hbT) (inv_mem hcT₁)⟩
    refine ⟨⟨c, hcY⟩ * b * ⟨c, hcY⟩⁻¹, mem_subgroupOf.mpr hcbB, ?_⟩
    rw [hρy, map_mul, map_mul, map_inv]
  obtain ⟨D, hDc, hDB, hBD, hDfpf, hDtr⟩ := h.exists_cartan_data_of_card_sylow hS2
  have hDY : D ≤ Y := hDB.trans hBY
  have hρB : ∀ b : Y, (b : G) ∈ B → ∃ d ∈ D, ∃ hd : d ∈ Y, ρ b = ρ ⟨d, hd⟩ := by
    intro b hb
    obtain ⟨p, hp, d, hd, hpd⟩ := hBD _ hb
    have hpR₁ : p ∈ R₁ := le_szR_left _ _ _ hp
    have hpY : p ∈ Y := Subgroup.le_normalizer hpR₁
    refine ⟨d, hd, hDY hd, ?_⟩
    have hbeq : b = ⟨p, hpY⟩ * ⟨d, hDY hd⟩ := Subtype.ext hpd
    rw [hbeq, map_mul, hρtriv _ hpR₁, one_mul]
  have hHc : IsCyclic H := by
    let φ : D →* MulAut (R₁ ⧸ N) :=
      MonoidHom.mk' (fun d => ρ ⟨(d : G), hDY d.2⟩) (fun d d' => by rw [← map_mul]; rfl)
    have hle : H ≤ φ.range := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨d, hd, hdY, hbd⟩ := hρB b (mem_subgroupOf.mp hb)
      exact ⟨⟨d, hd⟩, hbd.symm⟩
    exact isCyclic_of_le_isCyclic
      (isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective) hle
  have hne1 : ∀ w (hw : w ∈ szT₁ L T), ((⟨w, le_szR_left _ _ _ hw⟩ : R₁) : R₁ ⧸ N) ≠ 1 →
      w ∉ szA₁ (szT₁ L T) := by
    intro w hw h1 hwA
    apply h1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hR.le hwA
  have hfix : ∀ d ∈ D, ∀ (hd : d ∈ Y) w (hw : w ∈ szT₁ L T),
      ρ ⟨d, hd⟩ ((⟨w, le_szR_left _ _ _ hw⟩ : R₁) : R₁ ⧸ N) =
        ((⟨w, le_szR_left _ _ _ hw⟩ : R₁) : R₁ ⧸ N) → w ∉ szA₁ (szT₁ L T) → d = 1 := by
    intro d hd hdY w hw hfx hwA
    by_contra hd1
    apply hwA
    refine hDfpf d hd hd1 w hw ?_
    rw [hρ, hmkeq] at hfx
    have hdT : d ∈ normalizer (szT₁ L T : Set G) := (mem_inf.mp (hDB hd)).2
    have hdw : d * w * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hdT w).mp hw
    set a := (d * w * d⁻¹)⁻¹ * w with ha
    have haA : a ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      exact mem_inf.mpr ⟨mul_mem (inv_mem hdw) hw, by simpa using hfx⟩
    have e : d * w * d⁻¹ * w⁻¹ = w * a⁻¹ * w⁻¹ := by rw [ha]; group
    rw [e]
    have hca : w * a⁻¹ = a⁻¹ * w :=
      mem_centralizer_iff.mp (mem_szA₁.mp (inv_mem haA)).2 w hw
    rw [hca, mul_inv_cancel_right]
    exact inv_mem haA
  have hHreg : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! x : H, (x : MulAut (R₁ ⧸ N)) u = v := by
    intro u v hu hv
    obtain ⟨w₁, hw₁, hu₁⟩ := hUrep u u.2
    obtain ⟨w₂, hw₂, hv₂⟩ := hUrep v v.2
    have hw₁A : w₁ ∉ szA₁ (szT₁ L T) :=
      hne1 w₁ hw₁ (fun h1 => hu (Subtype.ext (by rw [hu₁, h1]; rfl)))
    have hw₂A : w₂ ∉ szA₁ (szT₁ L T) :=
      hne1 w₂ hw₂ (fun h1 => hv (Subtype.ext (by rw [hv₂, h1]; rfl)))
    obtain ⟨d, hd, hdd⟩ := hDtr heven w₁ hw₁ hw₁A w₂ hw₂ hw₂A
    have hdY := hDY hd
    have hdmove : ρ ⟨d, hdY⟩ (u : R₁ ⧸ N) = v := by
      rw [hu₁, hv₂, hρ, hmkeq]
      exact hR.le hdd
    refine ⟨⟨ρ ⟨d, hdY⟩, ⟨d, hdY⟩, mem_subgroupOf.mpr (hDB hd), rfl⟩, hdmove, ?_⟩
    intro x hxuv
    obtain ⟨b, hb, hbx⟩ := x.2
    obtain ⟨d', hd', hd'Y, hbd'⟩ := hρB b (mem_subgroupOf.mp hb)
    apply Subtype.ext
    change (x : MulAut (R₁ ⧸ N)) = ρ ⟨d, hdY⟩
    rw [← hbx, hbd']
    have hbuv' : ρ ⟨d', hd'Y⟩ (u : R₁ ⧸ N) = v := by
      rw [← hbd', hbx]
      exact hxuv
    have hfx : ρ ⟨d⁻¹ * d', mul_mem (inv_mem hdY) hd'Y⟩ (u : R₁ ⧸ N) = (u : R₁ ⧸ N) := by
      have e : (⟨d⁻¹ * d', mul_mem (inv_mem hdY) hd'Y⟩ : Y) = ⟨d, hdY⟩⁻¹ * ⟨d', hd'Y⟩ := rfl
      rw [e, map_mul, map_inv, MulAut.mul_apply, hbuv', ← hdmove, MulAut.inv_apply,
        MulEquiv.symm_apply_apply]
    rw [hu₁] at hfx
    have h1 := hfix _ (mul_mem (inv_mem hd) hd') _ w₁ hw₁ hfx hw₁A
    have h2 : d' = d := by
      have := congrArg (d * ·) h1
      simpa using this
    subst h2
    rfl
  have hYne : Y ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.setting.1
    have hn : (szT₁ L T ⊔ R₂).Normal :=
      normalizer_eq_top_iff.mp (eq_top_iff.mpr (htop ▸ hYH))
    rcases hn.eq_bot_or_eq_top with hbot | htop'
    · have h1 : Nat.card (szT₁ L T) ≤ 1 := by
        have := card_le_of_le (le_sup_left.trans hbot.le : szT₁ L T ≤ ⊥)
        rwa [card_bot] at this
      rw [hT₁card] at h1
      have : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by
        have := h.two_le; omega))
      omega
    · exact htH (htop' ▸ mem_top t)
  have hcat : NonabelianSimpleNormalCatalog (orbitImage M t') := by
    intro S hSN hSn hs hnab
    let φ : Y →* Equiv.Perm (Orbit M t') :=
      (MulAction.toPermHom M (Orbit M t')).comp ρ.rangeRestrict
    have hrange : φ.range = orbitImage M t' := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ρ.rangeRestrict_surjective,
        ← MonoidHom.range_eq_map]
    exact catalog_of_le_range_of_kProper h.setting.2.2.1 hYne φ (hSN.trans hrange.ge) hs hnab
  have hn3 : 3 ≤ 2 * f := by have := h.two_le; omega
  have hreg : HasRegularNormalSubgroup (orbitImage M t') :=
    (regularNormal_or_projective_of_affineModel hV hn3 hUcard hUt hMU hHM hHt hHn hHc hHreg
      hcat).resolve_right fun hp => by
        obtain ⟨h3, -⟩ := hp
        omega
  have hR₁N : R₁ ≤ normalizer (R₂ : Set G) :=
    sup_le (sup_le hR.T₁_le_normalizer Subgroup.le_normalizer) (zpowers_le.mpr hR.t_mem_normalizer)
  let φ₀ : R₁ ⧸ N → Subgroup G :=
    Quotient.lift (fun x : R₁ => R₂ ⊔ zpowers (x : G)) fun a b hab => by
      have h1 : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
      rw [mem_subgroupOf] at h1
      change R₂ ⊔ zpowers (a : G) = R₂ ⊔ zpowers (b : G)
      have e : (b : G) = a * ((a⁻¹ * b : R₁) : G) := by simp
      rw [e, sup_zpowers_mul_eq h1]
  have hφ₀ : ∀ x : R₁, φ₀ (x : R₁ ⧸ N) = R₂ ⊔ zpowers (x : G) := fun x => rfl
  have horb : ∀ s : Orbit M t', ∃ y : Y, (s : R₁ ⧸ N) = ρ y t' := by
    rintro ⟨_, m, rfl⟩
    obtain ⟨y, hy⟩ := m.2
    refine ⟨y, ?_⟩
    change (m : MulAut (R₁ ⧸ N)) t' = ρ y t'
    rw [hy]
  have hmemΩ : ∀ s : Orbit M t', φ₀ s ∈ u3Omega L T R₂ t := by
    intro s
    obtain ⟨y, hy⟩ := horb s
    rw [hy, ht', hρ, hφ₀]
    exact ⟨y, y.2, (map_conj_sup_zpowers (hYK y.2)).symm⟩
  let e₀ : Orbit M t' → u3Omega L T R₂ t := fun s => ⟨φ₀ s, hmemΩ s⟩
  have hinj : Function.Injective e₀ := by
    intro s s' hss
    have h1 : φ₀ s = φ₀ s' := congrArg Subtype.val hss
    obtain ⟨y, hy⟩ := horb s
    obtain ⟨y', hy'⟩ := horb s'
    apply Subtype.ext
    rw [hy, hy'] at h1 ⊢
    rw [ht', hρ, hρ, hφ₀, hφ₀] at h1
    rw [ht', hρ, hρ, hmkeq]
    have hxR₁ : (y : G) * t * (y : G)⁻¹ ∈ R₁ :=
      (mem_normalizer_iff.mp y.2 t).mp (mem_szR_right _ _ _)
    have hxN : (y : G) * t * (y : G)⁻¹ ∈ normalizer (R₂ : Set G) := hR₁N hxR₁
    have hx2 : ((y : G) * t * (y : G)⁻¹) ^ 2 = 1 := by
      rw [show ((y : G) * t * (y : G)⁻¹) ^ 2 = (y : G) * t ^ 2 * (y : G)⁻¹ by rw [sq, sq]; group,
        hR.t_sq, mul_one, mul_inv_cancel]
    have hmem : (y' : G) * t * (y' : G)⁻¹ ∈
        ((R₂ ⊔ zpowers ((y : G) * t * (y : G)⁻¹) : Subgroup G) : Set G) := by
      change _ ∈ R₂ ⊔ zpowers ((y : G) * t * (y : G)⁻¹)
      rw [h1]
      exact mem_sup_right (mem_zpowers _)
    rw [coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hxN)] at hmem
    obtain ⟨r, hr, z, hz, hrz⟩ := Set.mem_mul.mp hmem
    rcases mem_zpowers_involution_eq_one_or_eq hx2 hz with hz1 | hz1
    · exfalso
      rw [hz1, mul_one] at hrz
      have h2 : (y' : G)⁻¹ * ((y' : G) * t * (y' : G)⁻¹) * (y' : G) ∈ R₂ :=
        (mem_normalizer_iff''.mp (hYK y'.2) _).mp (hrz ▸ hr)
      rw [show (y' : G)⁻¹ * ((y' : G) * t * (y' : G)⁻¹) * (y' : G) = t by group] at h2
      exact htH (mem_sup_right h2)
    · rw [hz1] at hrz
      change ((y : G) * t * (y : G)⁻¹)⁻¹ * ((y' : G) * t * (y' : G)⁻¹) ∈ R₂
      rw [← hrz]
      have h3 := (mem_normalizer_iff''.mp hxN r).mp hr
      simpa [mul_assoc] using h3
  have hsurj : Function.Surjective e₀ := by
    rintro ⟨_, y₀, hy₀, rfl⟩
    set m : M := ⟨ρ ⟨y₀, hy₀⟩, ⟨y₀, hy₀⟩, rfl⟩ with hm
    refine ⟨⟨m • t', MulAction.mem_orbit t' m⟩, Subtype.ext ?_⟩
    change φ₀ (ρ ⟨y₀, hy₀⟩ t') = (R₂ ⊔ zpowers t).map (MulAut.conj y₀).toMonoidHom
    rw [ht', hρ, hφ₀, map_conj_sup_zpowers (hYK hy₀)]
  set e := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩ with he
  have key : ∀ y : Y, u3OmegaAction L T R₂ t y =
      e.permCongrHom (MulAction.toPermHom M (Orbit M t') (ρ.rangeRestrict y)) := by
    intro y
    refine Equiv.ext fun X => ?_
    obtain ⟨s, rfl⟩ := e.surjective X
    rw [permCongrHom_apply_apply, Equiv.symm_apply_apply]
    apply Subtype.ext
    change (φ₀ s).map (MulAut.conj (y : G)).toMonoidHom = φ₀ (ρ y (s : R₁ ⧸ N))
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (s : R₁ ⧸ N)
    rw [← hx, hρ, hφ₀, hφ₀, map_conj_sup_zpowers (hYK y.2)]
  have hrange : (u3OmegaAction L T R₂ t).range =
      (orbitImage M t').map e.permCongrHom.toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      exact ⟨_, ⟨ρ.rangeRestrict y, rfl⟩, (key y).symm⟩
    · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      obtain ⟨y, hy⟩ := ρ.rangeRestrict_surjective m
      exact ⟨y, by rw [key, hy]; rfl⟩
  rw [hrange]
  exact hreg.map_permCongr e

theorem omega_regular_of_even_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) (heven : Even f)
    (hmove : ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) :
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 ∧
      HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range :=
  ⟨h.ncard_u3Omega_of_even_of_card_sylow hS2 hR heven hmove,
    h.hasRegularNormalSubgroup_of_even_of_card_sylow hS2 hR hc heven⟩

end Certificates

end U3Start

@[expose] def U3OmegaOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → Odd f →
    (∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) →
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 ∧
      HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem omega_regular_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hodd : U3OmegaOddInput)
    (hmove : ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) :
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 ∧
      HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range := by
  rcases Nat.even_or_odd f with heven | hfodd
  · exact h.omega_regular_of_even_of_card_sylow hS2 hR hc heven hmove
  · exact hodd G L f t T R₂ h hS2 hR hc hfodd hmove

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
