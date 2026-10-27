module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1RegularEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1RegularTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Level1
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Move
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1RegularBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.GH74.Uniqueness.Bender AffineModel

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem exists_conj_t_of_ne_three (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) (hf : f ≠ 3)
    (htrY : ∀ r ∈ R₂, ∃ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G),
      y * t * y⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) :
    ∀ r ∈ R₂, ∃ x ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T) := by
  classical
  obtain ⟨hYT, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  have hYW := h.normalizer_szR_le_normalizer_sup_zpowers_of_inv hS2 hR hinv
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨hT₁card, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨hR₁u, -, -, -, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  set R₁ := szR (szT₁ L T) R₂ t with hR₁def
  set Y := normalizer (R₁ : Set G) with hYdef
  set A₁ := szA₁ (szT₁ L T) with hA₁def
  set W : Subgroup G := R₂ ⊔ zpowers t with hWdef
  have hYR₂ : Y ≤ normalizer (R₂ : Set G) := fun y hy => (mem_inf.mp (hNR₁ hy)).2
  have hYH : Y ≤ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := fun y hy =>
    (mem_inf.mp (hNR₁ hy)).1
  have hWR₁ : W ≤ R₁ := sup_le (le_szR_mid _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))
  have hR₁C : R₁ ≤ centralizer (A₁ : Set G) := hR.szR_le_centralizer_szA₁
  have hA₁W : A₁ ≤ W := hR.le.trans le_sup_left
  have htW : t ∈ W := mem_sup_right (mem_zpowers t)
  have htH : t ∉ szT₁ L T ⊔ R₂ := h.t_not_mem_sup_of_card_sylow hS2 hR
  have hcA : ∀ a ∈ A₁, ∀ x ∈ W, a * x = x * a := fun a ha x hx =>
    mem_centralizer_iff.mp (hR₁C (hWR₁ hx)) a ha
  have : (A₁.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hA₁W).mpr
      ((hWR₁.trans hR₁C).trans (centralizer_le_normalizer _))
  set N := A₁.subgroupOf W with hNdef
  set ρ := quotConj Y hYW hYA with hρdef
  have hρ : ∀ (y : Y) (x : W), ρ y (x : W ⧸ N) =
      ((⟨(y : G) * x * (y : G)⁻¹, (mem_normalizer_iff.mp (hYW y.2) x).mp x.2⟩ : W) : W ⧸ N) :=
    fun y x => quotConj_mk Y hYW hYA y x
  have hmkeq : ∀ x x' : W, (x : W ⧸ N) = (x' : W ⧸ N) ↔ (x : G)⁻¹ * x' ∈ A₁ := fun x x' =>
    QuotientGroup.eq.trans mem_subgroupOf
  have hWdec : ∀ x ∈ W, ∃ r ∈ R₂, x = r ∨ x = r * t := by
    intro x hx
    have hx' : x ∈ ((W : Subgroup G) : Set G) := hx
    rw [hWdef, coe_mul_of_right_le_normalizer_left R₂ (zpowers t)
      (zpowers_le.mpr hR.t_mem_normalizer)] at hx'
    obtain ⟨r, hr, z, hz, rfl⟩ := Set.mem_mul.mp hx'
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with rfl | rfl
    · exact ⟨r, hr, Or.inl (mul_one r)⟩
    · exact ⟨r, hr, Or.inr rfl⟩
  have hsqW : ∀ x ∈ W, x ^ 2 ∈ A₁ := by
    intro x hx
    obtain ⟨r, hr, hxr | hxr⟩ := hWdec x hx
    · rw [hxr]; exact hR.sq_mem r hr
    · rw [hxr, hR.mul_t_sq_eq_one_of_inv hinv hr]; exact one_mem _
  have hV : ∀ v : W ⧸ N, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hsqW _ x.2
  have hVcomm : ∀ a b : W ⧸ N, a * b = b * a := by
    intro a b
    have e1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV _)
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV b),
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV a)] at e1
    exact e1.symm
  let _ : CommGroup (W ⧸ N) := { (inferInstance : Group (W ⧸ N)) with mul_comm := hVcomm }
  set t' : W ⧸ N := ((⟨t, htW⟩ : W) : W ⧸ N) with ht'
  set M := ρ.range with hM
  set U : Subgroup (W ⧸ N) := (R₂.subgroupOf W).map (QuotientGroup.mk' N) with hU
  have memU : ∀ x : W, (x : W ⧸ N) ∈ U ↔ (x : G) ∈ R₂ := by
    intro x
    constructor
    · rintro ⟨z, hz, hzx⟩
      have h1 := (hmkeq z x).mp hzx
      have h2 : ((z : G) * ((z : G)⁻¹ * x)) ∈ R₂ := mul_mem (mem_subgroupOf.mp hz) (hR.le h1)
      simpa using h2
    · intro hx
      exact ⟨x, mem_subgroupOf.mpr hx, rfl⟩
  have hUrep : ∀ u ∈ U, ∃ r, ∃ hr : r ∈ R₂, u = ((⟨r, le_sup_left (a := R₂) hr⟩ : W) : W ⧸ N) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, mem_subgroupOf.mp hz, rfl⟩
  have hUcard : Nat.card U = 2 ^ f := by
    rw [hU, ← relIndex_ker, QuotientGroup.ker_mk', relIndex_subgroupOf (le_sup_left : R₂ ≤ W)]
    have h1 := relIndex_mul_card (H := A₁) (K := R₂)
    rw [inf_of_le_left hR.le, hA₁card, hR.card] at h1
    have h2 : A₁.relIndex R₂ * 2 ^ f = 2 ^ f * 2 ^ f := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have ht'U : t' ∉ U := fun h1 => htH (mem_sup_right ((memU _).mp h1))
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
      obtain ⟨r, hr, hx | hx⟩ := hWdec x x.2
      · have : x = ⟨r, le_sup_left (a := R₂) hr⟩ := Subtype.ext hx
        rw [this]
        exact mem_sup_left ((memU _).mpr hr)
      · have : x = ⟨r, le_sup_left (a := R₂) hr⟩ * ⟨t, htW⟩ := Subtype.ext hx
        rw [this, QuotientGroup.mk_mul]
        exact mul_mem_sup ((memU _).mpr hr) (mem_zpowers t')
  have hMU : ∀ m ∈ M, ∀ u ∈ U, m u ∈ U := by
    rintro _ ⟨y, rfl⟩ u hu
    obtain ⟨r, hr, rfl⟩ := hUrep u hu
    rw [hρ, memU]
    exact (mem_normalizer_iff.mp (hYR₂ y.2) r).mp hr
  have hρtriv : ∀ y : Y, (y : G) ∈ R₁ → ρ y = 1 := by
    intro y hy
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with | H x => ?_
    rw [hρ, MulAut.one_apply, hmkeq]
    have := h.comm_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 (hR₁u ▸ hy)
      (hR₁u ▸ hWR₁ (inv_mem x.2))
    simpa [mul_assoc] using this
  obtain ⟨-, -, -, hNAR₁, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  set B := L ⊓ normalizer (szT₁ L T : Set G) with hB
  have hBY : B ≤ Y := fun b hb => hNAR₁ (h.inf_normalizer_le_normalizer_szA hb)
  set H : Subgroup (MulAut (W ⧸ N)) := (B.subgroupOf Y).map ρ with hH
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
    rw [ht', hρ, hmkeq] at hyt
    have haA : (y : G) * t * (y : G)⁻¹ * t⁻¹ ∈ A₁ := by
      have h1 := inv_mem hyt
      have e : (y : G) * t * (y : G)⁻¹ * t⁻¹ =
          t * (((y : G) * t * (y : G)⁻¹)⁻¹ * t)⁻¹ * t⁻¹ := by group
      rw [e, ← hcA _ h1 t htW, mul_inv_cancel_right]
      exact h1
    obtain ⟨r₀, hr₀, hr₀a⟩ := hR.exists_sq_eq_of_inv hinv haA
    have hr₀t : r₀ * t * r₀⁻¹ = (y : G) * t * (y : G)⁻¹ := by
      rw [hR.conj_t_eq_sq_mul_of_inv hinv hr₀, hr₀a]; group
    have hr₀R₁ : r₀ ∈ R₁ := le_szR_mid _ _ _ hr₀
    have hr₀Y : r₀ ∈ Y := Subgroup.le_normalizer hr₀R₁
    set c := r₀⁻¹ * (y : G) with hcdef
    have hcY : c ∈ Y := mul_mem (inv_mem hr₀Y) y.2
    have hct : c * t = t * c := by
      have e2 : c * t * c⁻¹ = t := by
        calc c * t * c⁻¹ = r₀⁻¹ * ((y : G) * t * (y : G)⁻¹) * r₀ := by rw [hcdef]; group
          _ = r₀⁻¹ * (r₀ * t * r₀⁻¹) * r₀ := by rw [hr₀t]
          _ = t := by group
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [e2]
    have hcL : c ∈ normalizer (L : Set G) := hCtL (mem_centralizer_singleton_iff.mpr hct)
    have hcT₁ : c ∈ normalizer (szT₁ L T : Set G) := hYT hcY
    have hyeq : y = ⟨r₀, hr₀Y⟩ * ⟨c, hcY⟩ := Subtype.ext (by
      change (y : G) = r₀ * (r₀⁻¹ * y)
      group)
    have hρy : ρ y = ρ ⟨c, hcY⟩ := by rw [hyeq, map_mul, hρtriv _ hr₀R₁, one_mul]
    obtain ⟨hbL, hbT⟩ := mem_inf.mp (mem_subgroupOf.mp hb)
    have hcbB : c * b * c⁻¹ ∈ B := mem_inf.mpr ⟨(mem_normalizer_iff.mp hcL _).mp hbL,
      mul_mem (mul_mem hcT₁ hbT) (inv_mem hcT₁)⟩
    refine ⟨⟨c, hcY⟩ * b * ⟨c, hcY⟩⁻¹, mem_subgroupOf.mpr hcbB, ?_⟩
    rw [hρy, map_mul, map_mul, map_inv]
  obtain ⟨D, hDc, hDB, hBD, -, -⟩ := h.exists_cartan_data_of_card_sylow hS2
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
    let φD : D →* MulAut (W ⧸ N) :=
      MonoidHom.mk' (fun d => ρ ⟨(d : G), hDY d.2⟩) (fun d d' => by rw [← map_mul]; rfl)
    have hle : H ≤ φD.range := by
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨d, hd, hdY, hbd⟩ := hρB b (mem_subgroupOf.mp hb)
      exact ⟨⟨d, hd⟩, hbd.symm⟩
    exact isCyclic_of_le_isCyclic
      (isCyclic_of_surjective φD.rangeRestrict φD.rangeRestrict_surjective) hle
  have hHcomm : ∀ x ∈ H, ∀ x' ∈ H, x * x' = x' * x := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
    obtain ⟨d, hd, hdY, hbd⟩ := hρB b (mem_subgroupOf.mp hb)
    obtain ⟨d', hd', hd'Y, hbd'⟩ := hρB b' (mem_subgroupOf.mp hb')
    have key : (⟨d, hd⟩ : D) * ⟨d', hd'⟩ = ⟨d', hd'⟩ * ⟨d, hd⟩ := by
      let _ := hDc.commGroup
      exact mul_comm _ _
    have key' : d * d' = d' * d := congrArg Subtype.val key
    rw [hbd, hbd', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext key'
  obtain ⟨d₀, k₀, hd₀L, hd₀⟩ := h.exists_u3RTorus_of_card_sylow hS2
  have hd₀B : d₀ ∈ B := mem_inf.mpr ⟨hd₀L, hd₀.mem_normalizer_T₁⟩
  have hd₀Y : d₀ ∈ Y := hBY hd₀B
  have hd₀R₂ : d₀ ∈ normalizer (R₂ : Set G) := hYR₂ hd₀Y
  have hd₀tr := hd₀.trans
  have hne1 : ∀ r (hr : r ∈ R₂), ((⟨r, le_sup_left (a := R₂) hr⟩ : W) : W ⧸ N) ≠ 1 →
      r ∉ A₁ := by
    intro r hr h1 hrA
    apply h1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hrA
  have htrH : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃ x ∈ H, x (u : W ⧸ N) = v := by
    intro u v hu hv
    obtain ⟨r, hr, hur⟩ := hUrep u u.2
    obtain ⟨r', hr', hvr⟩ := hUrep v v.2
    have hrA : r ∉ A₁ := hne1 r hr (fun h1 => hu (Subtype.ext (by rw [hur, h1]; rfl)))
    have hr'A : r' ∉ A₁ := hne1 r' hr' (fun h1 => hv (Subtype.ext (by rw [hvr, h1]; rfl)))
    obtain ⟨n, hn⟩ := hR.exists_inv_mul_conj_pow_mem hinv hd₀R₂ hd₀tr hr hrA hr' hr'A
    have hyY : (d₀ ^ n)⁻¹ ∈ Y := inv_mem (pow_mem hd₀Y n)
    have hyB : (d₀ ^ n)⁻¹ ∈ B := inv_mem (pow_mem hd₀B n)
    refine ⟨ρ ⟨(d₀ ^ n)⁻¹, hyY⟩, ⟨⟨(d₀ ^ n)⁻¹, hyY⟩, mem_subgroupOf.mpr hyB, rfl⟩, ?_⟩
    rw [hur, hvr, hρ, hmkeq]
    change ((d₀ ^ n)⁻¹ * r * ((d₀ ^ n)⁻¹)⁻¹)⁻¹ * r' ∈ A₁
    rw [show ((d₀ ^ n)⁻¹ * r * ((d₀ ^ n)⁻¹)⁻¹)⁻¹ * r' =
      (r'⁻¹ * ((d₀ ^ n)⁻¹ * r * d₀ ^ n))⁻¹ by group]
    exact inv_mem hn
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
        have hc := hHcomm _ hkH g hg
        calc (x⁻¹ * (x' : MulAut (W ⧸ N))) w = (x⁻¹ * (x' : MulAut (W ⧸ N))) (g u) := by
              rw [hgu]
          _ = ((x⁻¹ * (x' : MulAut (W ⧸ N))) * g) u := rfl
          _ = (g * (x⁻¹ * (x' : MulAut (W ⧸ N)))) u := by rw [hc]
          _ = g ((x⁻¹ * (x' : MulAut (W ⧸ N))) u) := rfl
          _ = w := by rw [hku, hgu]
    have h2 := congrArg (x * ·) hk1
    simp only [mul_one, mul_inv_cancel_left] at h2
    exact h2
  have hrtW : ∀ r ∈ R₂, r * t ∈ W := fun r hr => mul_mem (le_sup_left (a := R₂) hr) htW
  have hswap : ∀ a ∈ W, ∀ b ∈ W, a⁻¹ * b ∈ A₁ → a * b⁻¹ ∈ A₁ := by
    intro a ha b hb hab
    rw [show a * b⁻¹ = a * (a⁻¹ * b)⁻¹ * a⁻¹ by group, ← hcA _ (inv_mem hab) a ha,
      mul_inv_cancel_right]
    exact inv_mem hab
  have hswap' : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ A₁ → a⁻¹ * b ∈ A₁ := by
    intro a ha b hb hab
    rw [show a⁻¹ * b = b⁻¹ * ((a * b⁻¹)⁻¹ * b) by group, hcA _ (inv_mem hab) b hb,
      inv_mul_cancel_left]
    exact inv_mem hab
  have hpt_iff : ∀ (y : Y) (r : G) (hr : r ∈ R₂),
      ρ y t' = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) ↔
        (y : G) * t * (y : G)⁻¹ * (r * t)⁻¹ ∈ A₁ := by
    intro y r hr
    rw [ht', hρ, hmkeq]
    have hyW : (y : G) * t * (y : G)⁻¹ ∈ W := (mem_normalizer_iff.mp (hYW y.2) t).mp htW
    exact ⟨hswap _ hyW _ (hrtW r hr), hswap' _ hyW _ (hrtW r hr)⟩
  have hO3 : ∀ s : W ⧸ N, s ∈ MulAction.orbit M t' ↔
      ∃ r, ∃ hr : r ∈ R₂, s = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) := by
    intro s
    constructor
    · rintro ⟨m, rfl⟩
      obtain ⟨y, hy⟩ := m.2
      obtain ⟨r, hr, hyt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv y.2
      refine ⟨r, hr, ?_⟩
      change (m : MulAut (W ⧸ N)) t' = _
      rw [← hy, ht', hρ]
      congr 1
      exact Subtype.ext hyt
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨y, hyY, hyr⟩ := htrY r hr
      exact ⟨⟨ρ ⟨y, hyY⟩, ⟨y, hyY⟩, rfl⟩, (hpt_iff ⟨y, hyY⟩ r hr).mpr hyr⟩
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
      refine ⟨⟨((⟨r, le_sup_left (a := R₂) hr⟩ : W) : W ⧸ N), (memU _).mpr hr⟩, Subtype.ext ?_⟩
      change ((⟨r, le_sup_left (a := R₂) hr⟩ : W) : W ⧸ N) * t' =
        ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N)
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
    exact catalog_of_le_range_of_kProper h.setting.2.2.1 hYne φ (hSN.trans hrange.ge) hs hnab
  have hreg : HasRegularNormalSubgroup (orbitImage M t') := by
    rcases (show f = 2 ∨ 4 ≤ f by have := h.two_le; omega) with hf2 | hf4
    ·
      refine hasRegularNormalSubgroup_of_card_eq_four (by rw [hOcard, hf2]; norm_num)
        (U3C1Regular.two_transitive_of_stabilizer ω₀ (fun a => ?_) fun a b ha hb => ?_)
      · obtain ⟨m, hm⟩ := a.2
        exact ⟨MulAction.toPermHom M (Orbit M t') m, ⟨m, rfl⟩, Subtype.ext hm⟩
      · obtain ⟨r, hr, har⟩ := (hO3 a).mp a.2
        obtain ⟨r', hr', hbr⟩ := (hO3 b).mp b.2
        have hnot : ∀ (s : Orbit M t') (r : G) (hr : r ∈ R₂),
            (s : W ⧸ N) = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) → s ≠ ω₀ → r ∉ A₁ := by
          intro s r hr hsr hs hrA
          apply hs
          apply Subtype.ext
          rw [hsr, hω₀]
          change ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) = t'
          rw [ht', hmkeq]
          change (r * t)⁻¹ * t ∈ A₁
          rw [show (r * t)⁻¹ * t = t⁻¹ * r⁻¹ * t by group, mul_assoc,
            hcA _ (inv_mem hrA) t htW, inv_mul_cancel_left]
          exact inv_mem hrA
        have hrA := hnot a r hr har ha
        have hr'A := hnot b r' hr' hbr hb
        obtain ⟨n, hn⟩ := hR.exists_inv_mul_conj_pow_mem hinv hd₀R₂ hd₀tr hr hrA hr' hr'A
        have hyY : (d₀ ^ n)⁻¹ ∈ Y := inv_mem (pow_mem hd₀Y n)
        have hdnt : d₀ ^ n * t = t * d₀ ^ n := (Commute.pow_left hd₀.comm_t n).eq
        refine ⟨φ ⟨(d₀ ^ n)⁻¹, hyY⟩, by rw [← hrange]; exact ⟨_, rfl⟩, Subtype.ext ?_,
          Subtype.ext ?_⟩
        · rw [hφ, hω₀]
          change ρ ⟨(d₀ ^ n)⁻¹, hyY⟩ t' = t'
          rw [ht', hρ]
          congr 1
          apply Subtype.ext
          change (d₀ ^ n)⁻¹ * t * ((d₀ ^ n)⁻¹)⁻¹ = t
          rw [inv_inv, mul_assoc, ← hdnt, inv_mul_cancel_left]
        · rw [hφ, har, hbr, hρ, hmkeq]
          change ((d₀ ^ n)⁻¹ * (r * t) * ((d₀ ^ n)⁻¹)⁻¹)⁻¹ * (r' * t) ∈ A₁
          have e1 : (d₀ ^ n)⁻¹ * (r * t) * ((d₀ ^ n)⁻¹)⁻¹ = ((d₀ ^ n)⁻¹ * r * d₀ ^ n) * t := by
            rw [inv_inv, mul_assoc, mul_assoc, ← hdnt]
            group
          have hc' := inv_mem hn
          rw [e1, show (((d₀ ^ n)⁻¹ * r * d₀ ^ n) * t)⁻¹ * (r' * t) =
            t⁻¹ * ((r'⁻¹ * ((d₀ ^ n)⁻¹ * r * d₀ ^ n))⁻¹ * t) by group,
            hcA _ hc' t htW, inv_mul_cancel_left]
          exact hc'
    · exact (regularNormal_or_projective_of_affineModel hV (by omega) hUcard hUt hMU hHM hHt hHn
        hHc hHreg hcat).resolve_right fun hp => by have := hp.1; omega
  have hker : ∀ y : Y, φ y = 1 → ∀ c ∈ A₁, (y : G) * c * (y : G)⁻¹ = c := by
    intro y hy1 c hc
    have hfix : ∀ s : Orbit M t', ρ y (s : W ⧸ N) = s := fun s => by
      rw [← hφ, hy1]; rfl
    obtain ⟨r, hr, hrc⟩ := hR.exists_sq_eq_of_inv hinv hc
    have h0 := hfix ω₀
    have h1 := hfix ⟨_, (hO3 _).mpr ⟨r, hr, rfl⟩⟩
    rw [hω₀] at h0
    change ρ y t' = t' at h0
    change ρ y ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) at h1
    rw [ht', hρ, hmkeq] at h0
    rw [hρ, hmkeq] at h1
    change ((y : G) * t * (y : G)⁻¹)⁻¹ * t ∈ A₁ at h0
    change ((y : G) * (r * t) * (y : G)⁻¹)⁻¹ * (r * t) ∈ A₁ at h1
    have hp : (y : G) * r * (y : G)⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hYR₂ y.2) r).mp hr
    have hpr : ((y : G) * r * (y : G)⁻¹)⁻¹ * r ∈ A₁ := by
      have e : ((y : G) * r * (y : G)⁻¹)⁻¹ * r =
          t * ((((y : G) * t * (y : G)⁻¹)⁻¹ * t)⁻¹ *
            (((y : G) * (r * t) * (y : G)⁻¹)⁻¹ * (r * t))) * t⁻¹ := by group
      have hm := mul_mem (inv_mem h0) h1
      rw [e, ← hcA _ hm t htW, mul_inv_cancel_right]
      exact hm
    have ha : r⁻¹ * ((y : G) * r * (y : G)⁻¹) ∈ A₁ := by
      have := inv_mem hpr
      rwa [mul_inv_rev, inv_inv] at this
    have hp2 : ((y : G) * r * (y : G)⁻¹) ^ 2 = r ^ 2 := by
      have e : (y : G) * r * (y : G)⁻¹ = r * (r⁻¹ * ((y : G) * r * (y : G)⁻¹)) := by group
      rw [e, (show Commute r (r⁻¹ * ((y : G) * r * (y : G)⁻¹)) from
        hR.comm r hr _ (hR.le ha)).mul_pow, hR.sq_A₁ _ ha, mul_one]
    calc (y : G) * c * (y : G)⁻¹ = ((y : G) * r * (y : G)⁻¹) ^ 2 := by
          rw [← hrc, sq, sq]; group
      _ = r ^ 2 := hp2
      _ = c := hrc
  intro r hr
  obtain ⟨E, hEle, hEn, hEreg⟩ := hreg
  rw [← hrange] at hEle hEn
  obtain ⟨y, hy, hyc⟩ := U3C1Regular.exists_centralizing_of_regular (by have := h.two_le; omega)
    hOcard hA₁card φ hEle hEn hEreg hYA hker hd₀Y hd₀tr ω₀ ⟨_, (hO3 _).mpr ⟨r, hr, rfl⟩⟩
  refine ⟨y, mem_inf.mpr ⟨y.2, mem_centralizer_iff.mpr fun c hc => ?_⟩, ?_⟩
  · calc c * (y : G) = (y : G) * c * (y : G)⁻¹ * y := by rw [hyc c hc]
      _ = (y : G) * c := by group
  · have h1 : ρ y t' = ((⟨r * t, hrtW r hr⟩ : W) : W ⧸ N) := by
      have := congrArg Subtype.val hy
      rwa [hφ] at this
    exact (hpt_iff y r hr).mp h1

theorem exists_conj_t_of_le (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hT : T ≤ szT₁ L T ⊔ zpowers t) :
    ∀ r ∈ R₂, ∃ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G),
      y * t * y⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨y₀, hy₀, r₀, hr₀, hr₀A, hy₀t⟩ := h.exists_move_of_inv_of_le_of_card_sylow hS2 hR hinv hT
  obtain ⟨d, hdt, hdR, hdT, hdtr⟩ := hR.torus
  exact exists_conj_t_of_move hR hinv hy₀ hr₀ hr₀A hy₀t (mem_normalizer_szR_of hdT hdR hdt) hdt
    hdR hdtr

end Certificates

end U3Start

section Certificates


theorem u3C1RegularInput : U3C1RegularInput := by
  intro G _ _ L f t T R₂ h hS2 hR hinv hne hT
  have htrY := h.exists_conj_t_of_le hS2 hR hinv hT
  refine h.exists_regular_of_transitive hS2 hR hinv hne ?_
  by_cases hf : f = 3
  · exact h.exists_conj_t_of_eight hS2 hR hinv hne hf htrY
  · exact h.exists_conj_t_of_ne_three hS2 hR hinv hne hf htrY

end Certificates

end CFSG.SeitzReduction.RankOne
