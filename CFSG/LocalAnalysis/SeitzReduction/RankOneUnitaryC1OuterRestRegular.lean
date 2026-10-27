module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestW
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestCard

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.GH74.Uniqueness.Bender AffineModel

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3C1OuterConf

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D V : Subgroup G} {k : ℕ}

section Certificates


theorem outerRest_exists_centralizing_of_ne_three (hc : U3C1OuterConf G L f t T R₂ D V k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hk : 2 ≤ k) {d : G} (hC : U3C1Cartan L T D d) (hf : f ≠ 3)
    (htrY : ∀ b ∈ szA₁ (szT₁ L T), ∃ y ∈ normalizer (szR (szT₁ L T) V t : Set G),
      outerRestPt t k y = b) :
    ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ normalizer (szR (szT₁ L T) V t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), outerRestPt t k x = b := by
  classical
  obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  set R := szR (szT₁ L T) V t with hRdef
  set Y := normalizer (R : Set G) with hYdef
  set A₁ := szA₁ (szT₁ L T) with hA₁def
  set W : Subgroup G := V ⊔ zpowers t with hWdef
  set N₀ := outerRestOmega hc.comm (2 ^ k) with hN₀def
  have hYW : Y ≤ normalizer (W : Set G) := hc.outerRest_le_normalizer_W h hS2 hk
  have hYV : ∀ y ∈ Y, y ∈ normalizer (V : Set G) := fun y hy =>
    (hc.normalizer_szR_le h hS2 hk hy).2.1
  have hYN : Y ≤ normalizer (N₀ : Set G) := fun y hy =>
    hc.outerRest_le_normalizer_powKer (hYV y hy)
  have hYA : Y ≤ normalizer (A₁ : Set G) := fun y hy =>
    normalizer_le_normalizer_inf_centralizer _ (hc.normalizer_szR_le h hS2 hk hy).2.2.1
  have hN₀V : N₀ ≤ V := outerRestOmega_le hc.comm _
  have hVW : V ≤ W := le_sup_left
  have htW : t ∈ W := mem_sup_right (mem_zpowers t)
  have hN₀W : N₀ ≤ W := hN₀V.trans hVW
  have htV : t ∉ V := fun ht => hc.outerRest_t_not_mem h hS2 hk (mem_sup_right ht)
  have : (N₀.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hN₀W).mpr (hc.outerRest_W_le_normalizer_powKer h)
  set N := N₀.subgroupOf W with hNdef
  set ρ := quotConj Y hYW hYN with hρdef
  have hρ : ∀ (y : Y) (x : W), ρ y (x : W ⧸ N) =
      ((⟨(y : G) * x * (y : G)⁻¹, (mem_normalizer_iff.mp (hYW y.2) x).mp x.2⟩ : W) : W ⧸ N) :=
    fun y x => quotConj_mk Y hYW hYN y x
  have hmkeq : ∀ x x' : W, (x : W ⧸ N) = (x' : W ⧸ N) ↔ (x : G)⁻¹ * x' ∈ N₀ := fun x x' =>
    QuotientGroup.eq.trans mem_subgroupOf
  have hV : ∀ v : W ⧸ N, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hc.outerRest_sq_mem_powKer h x.2
  have hVcomm : ∀ a b : W ⧸ N, a * b = b * a := by
    intro a b
    have e1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV _)
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV b),
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV a)] at e1
    exact e1.symm
  let _ : CommGroup (W ⧸ N) := { (inferInstance : Group (W ⧸ N)) with mul_comm := hVcomm }
  set t' : W ⧸ N := ((⟨t, htW⟩ : W) : W ⧸ N) with ht'
  set M := ρ.range with hM
  set U : Subgroup (W ⧸ N) := (V.subgroupOf W).map (QuotientGroup.mk' N) with hU
  have hrtW : ∀ r ∈ V, r * t ∈ W := fun r hr => mul_mem (hVW hr) htW
  have hmkV : ∀ r (hr : r ∈ V) r' (hr' : r' ∈ V),
      ((⟨r, hVW hr⟩ : W) : W ⧸ N) = ((⟨r', hVW hr'⟩ : W) : W ⧸ N) ↔
        r ^ 2 ^ k = r' ^ 2 ^ k := by
    intro r hr r' hr'
    rw [hmkeq]
    change r⁻¹ * r' ∈ N₀ ↔ _
    rw [mem_outerRestOmega, (Commute.mul_pow (hc.comm _ (inv_mem hr) _ hr') _), inv_pow]
    exact ⟨fun h1 => eq_of_inv_mul_eq_one h1.2,
      fun h1 => ⟨mul_mem (inv_mem hr) hr', by rw [h1, inv_mul_cancel]⟩⟩
  have hkey : ∀ (y : Y) r (hr : r ∈ V) s (hs : s ∈ V),
      ρ y ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) = ((⟨s * t, hrtW s hs⟩ : W) : W ⧸ N) ↔
        (y : G) * r ^ 2 ^ k * (y : G)⁻¹ * outerRestPt t k y = s ^ 2 ^ k := by
    intro y r hr s hs
    have hσ := hc.outerRest_comm_t_mem h hS2 hk y.2
    have hyr : (y : G) * r * (y : G)⁻¹ ∈ V := (mem_normalizer_iff.mp (hYV y y.2) r).mp hr
    have hm : (y : G) * r * (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹ * t⁻¹) ∈ V := mul_mem hyr hσ
    rw [hρ, hmkeq]
    have e : (y : G) * (r * t) * (y : G)⁻¹ =
        ((y : G) * r * (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹ * t⁻¹)) * t := by group
    change ((y : G) * (r * t) * (y : G)⁻¹)⁻¹ * (s * t) ∈ N₀ ↔ _
    rw [e, hc.outerRest_mul_t_iff h hm hs, (Commute.mul_pow (hc.comm _ hyr _ hσ) _), conj_pow,
      outerRestPt_def]
  have ht'1 : t' = ((⟨1 * t, hrtW 1 (one_mem V)⟩ : W) : W ⧸ N) := by
    rw [ht']; congr 1; exact Subtype.ext (one_mul t).symm
  have hkey0 : ∀ (y : Y), ρ y t' = t' ↔ outerRestPt t k y = 1 := by
    intro y
    rw [ht'1, hkey y 1 (one_mem V) 1 (one_mem V), one_pow, mul_one, mul_inv_cancel, one_mul]
  have hkey1 : ∀ (y : Y) s (hs : s ∈ V),
      ρ y t' = ((⟨s * t, hrtW s hs⟩ : W) : W ⧸ N) ↔ outerRestPt t k y = s ^ 2 ^ k := by
    intro y s hs
    rw [ht'1, hkey y 1 (one_mem V) s hs, one_pow, mul_one, mul_inv_cancel, one_mul]
  have memU : ∀ x : W, (x : W ⧸ N) ∈ U ↔ (x : G) ∈ V := by
    intro x
    constructor
    · rintro ⟨z, hz, hzx⟩
      have h1 := (hmkeq z x).mp hzx
      have h2 : ((z : G) * ((z : G)⁻¹ * x)) ∈ V := mul_mem (mem_subgroupOf.mp hz) (hN₀V h1)
      simpa using h2
    · intro hx
      exact ⟨x, mem_subgroupOf.mpr hx, rfl⟩
  have hUrep : ∀ u ∈ U, ∃ r, ∃ hr : r ∈ V, u = ((⟨r, hVW hr⟩ : W) : W ⧸ N) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, mem_subgroupOf.mp hz, rfl⟩
  have hUcard : Nat.card U = 2 ^ f := by
    rw [hU, ← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf hVW]
    have h1 := relIndex_mul_card (H := N₀) (K := V)
    rw [inf_of_le_left hN₀V, hc.outerRest_card_powKer h hS2, hc.card] at h1
    have h2 : N₀.relIndex V * (2 ^ f) ^ k = 2 ^ f * (2 ^ f) ^ k := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have ht'U : t' ∉ U := fun h1 => htV ((memU _).mp h1)
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
      obtain ⟨r, hr, hx | hx⟩ := hc.outerRest_mem_W h x.2
      · have : x = ⟨r, hVW hr⟩ := Subtype.ext hx
        rw [this]
        exact mem_sup_left ((memU _).mpr hr)
      · have : x = ⟨r, hVW hr⟩ * ⟨t, htW⟩ := Subtype.ext hx
        rw [this, QuotientGroup.mk_mul]
        exact mul_mem_sup ((memU _).mpr hr) (mem_zpowers t')
  have hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U := by
    rintro _ ⟨y, rfl⟩ u hu
    obtain ⟨r, hr, rfl⟩ := hUrep u hu
    rw [hρ, memU]
    exact (mem_normalizer_iff.mp (hYV y y.2) r).mp hr
  have hρtriv : ∀ y : Y, outerRestPt t k y = 1 → (∀ b ∈ A₁, (y : G) * b * (y : G)⁻¹ = b) →
      ρ y = 1 := by
    intro y hy1 hyA
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [MulAut.one_apply]
    obtain ⟨r, hr, hx | hx⟩ := hc.outerRest_mem_W h x.2
    · have hxe : x = ⟨r, hVW hr⟩ := Subtype.ext hx
      rw [hxe, hρ]
      have hyr : (y : G) * r * (y : G)⁻¹ ∈ V := (mem_normalizer_iff.mp (hYV y y.2) r).mp hr
      refine (hmkV _ hyr r hr).mpr ?_
      rw [conj_pow, hyA _ (hc.outerRest_pow_mem_szA₁ hr)]
    · have hxe : x = ⟨r * t, hrtW r hr⟩ := Subtype.ext hx
      rw [hxe]
      refine (hkey y r hr r hr).mpr ?_
      rw [hyA _ (hc.outerRest_pow_mem_szA₁ hr), hy1, mul_one]
  have hRC : R ≤ centralizer (A₁ : Set G) := by
    refine sup_le (sup_le (fun y hy => mem_centralizer_iff.mpr fun b hb =>
      (mem_centralizer_iff.mp (mem_szA₁.mp hb).2 y hy).symm) (fun r hr =>
        mem_centralizer_iff.mpr fun b hb => hc.comm b (hc.le hb) r hr)) (zpowers_le.mpr
          (mem_centralizer_iff.mpr fun b hb =>
            mem_centralizer_iff.mp h.mem_centralizer_szT₁ b (szA₁_le _ hb)))
  have hρR : ∀ y : Y, (y : G) ∈ R → ρ y = 1 := fun y hy => hρtriv y
    ((hc.mem_outerRestStab_iff h hS2 hk).mp (szR_le_outerRestStab h hy)).2
    (fun b hb => by rw [← mem_centralizer_iff.mp (hRC hy) b hb, mul_inv_cancel_right])
  set B : Subgroup G := L ⊓ normalizer (szT₁ L T : Set G) ⊓ normalizer (V : Set G) with hB
  have hBY : B ≤ Y := fun b hb => by
    obtain ⟨hbLT, hbV⟩ := mem_inf.mp hb
    obtain ⟨hbL, hbT⟩ := mem_inf.mp hbLT
    exact mem_normalizer_szR_of hbT hbV (mem_centralizer_iff.mp h.mem b hbL)
  set H : Subgroup (MulAut (W ⧸ N)) := (B.subgroupOf Y).map ρ with hH
  have hHM : H ≤ M := map_le_range ρ _
  have hHt : ∀ x ∈ H, x t' = t' := by
    rintro _ ⟨b, hb, rfl⟩
    have hbL : (b : G) ∈ L := (mem_inf.mp (mem_inf.mp (mem_subgroupOf.mp hb)).1).1
    exact (hkey0 b).mpr (U3C1OuterConf.outerRestPt_of_comm (mem_centralizer_iff.mp h.mem _ hbL))
  have hCtL : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1
  have hHn : ∀ m ∈ M, m t' = t' → ∀ x ∈ H, m * x * m⁻¹ ∈ H := by
    rintro _ ⟨y, rfl⟩ hyt _ ⟨b, hb, rfl⟩
    have hy1 : outerRestPt t k y = 1 := (hkey0 y).mp hyt
    obtain ⟨s, hs, hst⟩ := hc.outerRest_exists_of_pt_eq_one h hS2 hk y.2 hy1
    have hsR : s ∈ R := le_szR_mid _ _ _ hs
    have hsY : s ∈ Y := Subgroup.le_normalizer hsR
    set c := s⁻¹ * (y : G) with hcdef
    have hcY : c ∈ Y := mul_mem (inv_mem hsY) y.2
    have hcL : c ∈ normalizer (L : Set G) := hCtL (mem_centralizer_singleton_iff.mpr hst)
    have hcT₁ : c ∈ normalizer (szT₁ L T : Set G) := (hc.normalizer_szR_le h hS2 hk hcY).2.2.1
    have hcV : c ∈ normalizer (V : Set G) := hYV c hcY
    have hyeq : y = ⟨s, hsY⟩ * ⟨c, hcY⟩ := Subtype.ext (by
      change (y : G) = s * (s⁻¹ * y)
      group)
    have hρy : ρ y = ρ ⟨c, hcY⟩ := by rw [hyeq, map_mul, hρR _ hsR, one_mul]
    obtain ⟨hbLT, hbV⟩ := mem_inf.mp (mem_subgroupOf.mp hb)
    obtain ⟨hbL, hbT⟩ := mem_inf.mp hbLT
    have hcbB : c * b * c⁻¹ ∈ B := mem_inf.mpr ⟨mem_inf.mpr
      ⟨(mem_normalizer_iff.mp hcL _).mp hbL, mul_mem (mul_mem hcT₁ hbT) (inv_mem hcT₁)⟩,
      mul_mem (mul_mem hcV hbV) (inv_mem hcV)⟩
    refine ⟨⟨c, hcY⟩ * b * ⟨c, hcY⟩⁻¹, mem_subgroupOf.mpr hcbB, ?_⟩
    rw [hρy, map_mul, map_mul, map_inv]
  obtain ⟨D', hDc, hDB, hBD, -, -⟩ := h.exists_cartan_data_of_card_sylow hS2
  set D'' : Subgroup G := D' ⊓ normalizer (V : Set G) with hD''
  have hD''c : IsCyclic D'' := isCyclic_of_le_isCyclic hDc inf_le_left
  have hD''Y : D'' ≤ Y := fun x hx => hBY (mem_inf.mpr ⟨hDB (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)
  have hρB : ∀ b : Y, (b : G) ∈ B → ∃ d' ∈ D'', ∃ hd : d' ∈ Y, ρ b = ρ ⟨d', hd⟩ := by
    intro b hb
    obtain ⟨hbLT, hbV⟩ := mem_inf.mp hb
    obtain ⟨p, hp, d', hd', hpd⟩ := hBD _ hbLT
    have hpR : p ∈ R := le_szR_left _ _ _ hp
    have hpY : p ∈ Y := Subgroup.le_normalizer hpR
    have hd'V : d' ∈ normalizer (V : Set G) := by
      have e : d' = p⁻¹ * b := by rw [hpd]; group
      rw [e]; exact mul_mem (inv_mem (hYV p hpY)) hbV
    have hd'' : d' ∈ D'' := mem_inf.mpr ⟨hd', hd'V⟩
    refine ⟨d', hd'', hD''Y hd'', ?_⟩
    have hbeq : b = ⟨p, hpY⟩ * ⟨d', hD''Y hd''⟩ := Subtype.ext hpd
    rw [hbeq, map_mul, hρR _ hpR, one_mul]
  have hHc : IsCyclic H := by
    let φD : D'' →* MulAut (W ⧸ N) :=
      MonoidHom.mk' (fun x => ρ ⟨(x : G), hD''Y x.2⟩) (fun x x' => by rw [← map_mul]; rfl)
    have hle : H ≤ φD.range := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨d', hd', hdY, hbd⟩ := hρB b (mem_subgroupOf.mp hb)
      exact ⟨⟨d', hd'⟩, hbd.symm⟩
    exact isCyclic_of_le_isCyclic
      (isCyclic_of_surjective φD.rangeRestrict φD.rangeRestrict_surjective) hle
  have hHcomm : ∀ x ∈ H, ∀ x' ∈ H, x * x' = x' * x := by
    intro x hx x' hx'
    let _ := hHc.commGroup
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : H) ⟨x', hx'⟩)
  have hdB : d ∈ B := mem_inf.mpr ⟨mem_inf.mpr ⟨hC.le hC.mem, hC.le_normalizer hC.mem⟩,
    hc.D_le hC.mem⟩
  have hdY : d ∈ Y := hBY hdB
  have hne1 : ∀ r (hr : r ∈ V), ((⟨r, hVW hr⟩ : W) : W ⧸ N) ≠ 1 → r ^ 2 ^ k ≠ 1 := by
    intro r hr h1 hr1
    apply h1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact ⟨hr, hr1⟩
  have htrH : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃ x ∈ H, x (u : W ⧸ N) = v := by
    intro u v hu hv
    obtain ⟨r, hr, hur⟩ := hUrep u u.2
    obtain ⟨r', hr', hvr⟩ := hUrep v v.2
    have hrA : r ^ 2 ^ k ≠ 1 := hne1 r hr (fun h1 => hu (Subtype.ext (by rw [hur, h1]; rfl)))
    have hr'A : r' ^ 2 ^ k ≠ 1 := hne1 r' hr' (fun h1 => hv (Subtype.ext (by rw [hvr, h1]; rfl)))
    obtain ⟨n, hn⟩ := hC.trans _ (hc.outerRest_pow_mem_szA₁ hr) _
      (hc.outerRest_pow_mem_szA₁ hr') hrA hr'A
    have hyY : (d ^ n)⁻¹ ∈ Y := inv_mem (pow_mem hdY n)
    have hyB : (d ^ n)⁻¹ ∈ B := inv_mem (pow_mem hdB n)
    refine ⟨ρ ⟨(d ^ n)⁻¹, hyY⟩, ⟨⟨(d ^ n)⁻¹, hyY⟩, mem_subgroupOf.mpr hyB, rfl⟩, ?_⟩
    rw [hur, hvr, hρ]
    have hdr : (d ^ n)⁻¹ * r * ((d ^ n)⁻¹)⁻¹ ∈ V := (mem_normalizer_iff.mp (hYV _ hyY) r).mp hr
    refine (hmkV _ hdr r' hr').mpr ?_
    rw [conj_pow, inv_inv, hn]
  have hHreg : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! x : H, (x : MulAut (W ⧸ N)) u = v := by
    intro u v hu hv
    obtain ⟨x, hx, hxuv⟩ := htrH u v hu hv
    refine ⟨⟨x, hx⟩, hxuv, fun x' hx' => Subtype.ext ?_⟩
    have hkH : x⁻¹ * (x' : MulAut (W ⧸ N)) ∈ H := mul_mem (inv_mem hx) x'.2
    have hku : (x⁻¹ * (x' : MulAut (W ⧸ N))) (u : W ⧸ N) = u := by
      rw [MulAut.mul_apply, hx', ← hxuv, MulAut.inv_apply_self]
    have hk1 : x⁻¹ * (x' : MulAut (W ⧸ N)) = 1 := by
      refine eq_one_of_fix hUt (hHt _ hkH) fun w hw => ?_
      by_cases hw1 : (⟨w, hw⟩ : U) = 1
      · have : w = 1 := congrArg Subtype.val hw1
        rw [this, map_one]
      · obtain ⟨g, hg, hgu⟩ := htrH u ⟨w, hw⟩ hu hw1
        have hc' := hHcomm _ hkH g hg
        calc (x⁻¹ * (x' : MulAut (W ⧸ N))) w = (x⁻¹ * (x' : MulAut (W ⧸ N))) (g u) := by
              rw [hgu]
          _ = ((x⁻¹ * (x' : MulAut (W ⧸ N))) * g) u := rfl
          _ = (g * (x⁻¹ * (x' : MulAut (W ⧸ N)))) u := by rw [hc']
          _ = g ((x⁻¹ * (x' : MulAut (W ⧸ N))) u) := rfl
          _ = w := by rw [hku, hgu]
    have h2 := congrArg (x * ·) hk1
    simp only [mul_one, mul_inv_cancel_left] at h2
    exact h2
  have hO3 : ∀ s : W ⧸ N, s ∈ MulAction.orbit M t' ↔
      ∃ r, ∃ hr : r ∈ V, s = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) := by
    intro s
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨y, hy⟩ := m.2
      have hσ := hc.outerRest_comm_t_mem h hS2 hk y.2
      refine ⟨_, hσ, ?_⟩
      change (m : MulAut (W ⧸ N)) t' = _
      rw [← hy, ht', hρ]
      congr 1
      exact Subtype.ext (by
        change (y : G) * t * (y : G)⁻¹ = (y : G) * t * (y : G)⁻¹ * t⁻¹ * t
        group)
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨y, hyY, hyr⟩ := htrY _ (hc.outerRest_pow_mem_szA₁ hr)
      exact ⟨⟨ρ ⟨y, hyY⟩, ⟨y, hyY⟩, rfl⟩, (hkey1 ⟨y, hyY⟩ r hr).mpr hyr⟩
  have hmemO : ∀ u : U, (u : W ⧸ N) * t' ∈ MulAction.orbit M t' := by
    intro u
    obtain ⟨r, hr, hur⟩ := hUrep u u.2
    rw [hO3]
    exact ⟨r, hr, by rw [hur, ht', ← QuotientGroup.mk_mul]; rfl⟩
  have hOcard : Nat.card (Orbit M t') = 2 ^ f := by
    rw [← hUcard]
    symm
    refine Nat.card_eq_of_bijective (fun u : U => (⟨(u : W ⧸ N) * t', hmemO u⟩ : Orbit M t'))
      ⟨fun u u' huu => ?_, ?_⟩
    · have h1 : (u : W ⧸ N) * t' = (u' : W ⧸ N) * t' := congrArg Subtype.val huu
      exact Subtype.ext (mul_right_cancel h1)
    · rintro ⟨s, hs⟩
      obtain ⟨r, hr, rfl⟩ := (hO3 s).mp hs
      refine ⟨⟨((⟨r, hVW hr⟩ : W) : W ⧸ N), (memU _).mpr hr⟩, Subtype.ext ?_⟩
      change ((⟨r, hVW hr⟩ : W) : W ⧸ N) * t' = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N)
      rw [ht', ← QuotientGroup.mk_mul]
      rfl
  set ω₀ : Orbit M t' := ⟨t', MulAction.mem_orbit_self t'⟩ with hω₀
  set φ : Y →* Equiv.Perm (Orbit M t') :=
    (MulAction.toPermHom M (Orbit M t')).comp ρ.rangeRestrict with hφdef
  have hrange : φ.range = orbitImage M t' := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ρ.rangeRestrict_surjective,
      ← MonoidHom.range_eq_map]
  have hφ : ∀ (y : Y) (s : Orbit M t'), ((φ y s : Orbit M t') : W ⧸ N) = ρ y (s : W ⧸ N) :=
    fun _ _ => rfl
  have hYne : Y ≠ ⊤ := by
    intro htop
    have : IsSimpleGroup G := h.setting.1
    have hYH : Y ≤ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) := fun y hy =>
      (hc.normalizer_szR_le h hS2 hk hy).1
    have hn : (szT₁ L T ⊔ V).Normal :=
      normalizer_eq_top_iff.mp (eq_top_iff.mpr (htop ▸ hYH))
    rcases hn.eq_bot_or_eq_top with hbot | htop'
    · have h1 : Nat.card (szT₁ L T) ≤ 1 := by
        have := card_le_of_le (le_sup_left.trans hbot.le : szT₁ L T ≤ ⊥)
        rwa [card_bot] at this
      rw [hT₁card] at h1
      have : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by
        have := h.two_le; omega))
      omega
    · exact hc.outerRest_t_not_mem h hS2 hk (htop' ▸ mem_top t)
  have hcat : NonabelianSimpleNormalCatalog (orbitImage M t') := by
    intro S hSN hSn hs hnab
    exact catalog_of_le_range_of_kProper h.setting.2.2.1 hYne φ (hSN.trans hrange.ge) hs hnab
  have hnot : ∀ (s : Orbit M t') (r : G) (hr : r ∈ V),
      (s : W ⧸ N) = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) → s ≠ ω₀ → r ^ 2 ^ k ≠ 1 := by
    intro s r hr hsr hs hr1
    apply hs
    apply Subtype.ext
    rw [hsr, hω₀]
    change ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) = t'
    rw [ht'1, hmkeq]
    exact (hc.outerRest_mul_t_iff h hr (one_mem V)).mpr (by rw [hr1, one_pow])
  have hreg : HasRegularNormalSubgroup (orbitImage M t') := by
    rcases (show f = 2 ∨ 4 ≤ f by have := h.two_le; omega) with hf2 | hf4
    ·
      refine hasRegularNormalSubgroup_of_card_eq_four (by rw [hOcard, hf2]; norm_num)
        (U3C1Regular.two_transitive_of_stabilizer ω₀ (fun a => ?_) fun a b ha hb => ?_)
      · obtain ⟨m, hm⟩ := a.2
        exact ⟨MulAction.toPermHom M (Orbit M t') m, ⟨m, rfl⟩, Subtype.ext hm⟩
      · obtain ⟨r, hr, har⟩ := (hO3 a).mp a.2
        obtain ⟨r', hr', hbr⟩ := (hO3 b).mp b.2
        have hrA := hnot a r hr har ha
        have hr'A := hnot b r' hr' hbr hb
        obtain ⟨n, hn⟩ := hC.trans _ (hc.outerRest_pow_mem_szA₁ hr) _
          (hc.outerRest_pow_mem_szA₁ hr') hrA hr'A
        have hyY : (d ^ n)⁻¹ ∈ Y := inv_mem (pow_mem hdY n)
        have hdnt : (d ^ n)⁻¹ * t = t * (d ^ n)⁻¹ :=
          (Commute.pow_left (mem_centralizer_iff.mp h.mem d (hC.le hC.mem)) n).inv_left.eq
        have hpt : outerRestPt t k (d ^ n)⁻¹ = 1 := U3C1OuterConf.outerRestPt_of_comm hdnt
        refine ⟨φ ⟨(d ^ n)⁻¹, hyY⟩, by rw [← hrange]; exact ⟨_, rfl⟩, Subtype.ext ?_,
          Subtype.ext ?_⟩
        · rw [hφ, hω₀]
          exact (hkey0 ⟨(d ^ n)⁻¹, hyY⟩).mpr hpt
        · rw [hφ, har, hbr]
          refine (hkey ⟨(d ^ n)⁻¹, hyY⟩ r hr r' hr').mpr ?_
          change (d ^ n)⁻¹ * r ^ 2 ^ k * ((d ^ n)⁻¹)⁻¹ * outerRestPt t k (d ^ n)⁻¹ = _
          rw [hpt, mul_one, inv_inv, hn]
    · exact (regularNormal_or_projective_of_affineModel hV (by omega) hUcard hUt hMU hHM hHt hHn
        hHc hHreg hcat).resolve_right fun hp => by have := hp.1; omega
  have hker : ∀ y : Y, φ y = 1 → ∀ c ∈ A₁, (y : G) * c * (y : G)⁻¹ = c := by
    intro y hy1 c hc'
    have hfix : ∀ s : Orbit M t', ρ y (s : W ⧸ N) = s := fun s => by
      rw [← hφ, hy1]; rfl
    obtain ⟨r, hr, hrc⟩ := hc.outerRest_exists_pow_eq h hS2 hc'
    have h0 := hfix ω₀
    have h1 := hfix ⟨_, (hO3 _).mpr ⟨r, hr, rfl⟩⟩
    change ρ y t' = t' at h0
    change ρ y ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) at h1
    have hy0 := (hkey0 y).mp h0
    have h2 := (hkey y r hr r hr).mp h1
    rwa [hy0, mul_one, hrc] at h2
  intro b hb
  obtain ⟨r, hr, hrb⟩ := hc.outerRest_exists_pow_eq h hS2 hb
  obtain ⟨E, hEle, hEn, hEreg⟩ := hreg
  rw [← hrange] at hEle hEn
  obtain ⟨y, hy, hyc⟩ := U3C1Regular.exists_centralizing_of_regular (by have := h.two_le; omega)
    hOcard hA₁card φ hEle hEn hEreg hYA hker hdY hC.trans ω₀ ⟨_, (hO3 _).mpr ⟨r, hr, rfl⟩⟩
  refine ⟨y, mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun c hc' => ?_⟩, ?_⟩
  · calc c * (y : G) = (y : G) * c * (y : G)⁻¹ * y := by rw [hyc c hc']
      _ = (y : G) * c := by group
  · have h1 : ρ y t' = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) := by
      have := congrArg Subtype.val hy
      rwa [hφ] at this
    rw [← hrb]
    exact (hkey1 y r hr).mp h1

end Certificates

end U3C1OuterConf

end CFSG.SeitzReduction.RankOne
