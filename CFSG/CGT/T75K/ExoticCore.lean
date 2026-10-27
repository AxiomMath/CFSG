module

public import CFSG.CGT.T75K.ExoticLevi

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G]

theorem eq_of_mem_conj [Finite G] {T A B : Subgroup G} (hwc : IsWC T)
    (hA : ∃ k : G, A = conjSubgroup k T) (hB : ∃ k : G, B = conjSubgroup k T) {z : G}
    (hzA : z ∈ A) (hzB : z ∈ B) (hz1 : z ≠ 1) : A = B := by
  by_contra hne
  have hL : normIn A B ≠ ⊥ := fun hb =>
    hz1 (Subgroup.mem_bot.1 (hb ▸ mem_normIn.2 ⟨hzA, Subgroup.le_normalizer hzB⟩))
  have hcfg := cfg_of_conj_conj hwc hA hB (Ne.symm hne) hL
  have h : z ∈ A ⊓ B := ⟨hzA, hzB⟩
  rw [hcfg.inf, Subgroup.mem_bot] at h
  exact hz1 h

variable {T T₁ T₂ : Subgroup G} {n m : ℕ} {x l : G}

theorem exotic_core (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m) (hn : 4 ≤ n)
    (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) {h : G} (hh : LeviProps T T₁ x h (2 ^ m)) :
    ∃ t ∈ T, T₂ = conjSubgroup t T₁ := by
  have := hc.finite
  have hcfg := hc.sec3.cfg
  have hwc : IsWC T := hc.hy.pair.wc
  have hM : ∀ a ∈ cfgM T T₁, ∀ b ∈ cfgM T T₁, a * b = b * a := fun a ha b hb =>
    elemAbelian_mul_comm hcfg.isElemAbelian_cfgM ha hb
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 (by
          rintro rfl
          have h4 := hc.hy.card
          rw [hc.hT, pow_zero, one_pow] at h4
          omega))
  have hhT : h ∈ Subgroup.normalizer (T : Set G) := hh.hT
  have hxT₁ : x ∈ T₁ := normIn_le _ _ d.hx
  have hhT₁ : h ∈ Subgroup.normalizer (T₁ : Set G) := by
    refine hcfg.wc₁.centralizer_le_normalizer hxT₁ d.hx1 ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hh.hx
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hL : ∀ c ∈ normIn T T₁, h * c * h⁻¹ ∈ normIn T T₁ := by
    intro c hc'
    obtain ⟨hcT, hcN⟩ := mem_normIn.1 hc'
    exact mem_normIn.2 ⟨conj_mem_of_mem_normalizer hhT hcT,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhT₁ hcN) (Subgroup.inv_mem _ hhT₁)⟩
  have hL₁ : ∀ u ∈ normIn T₁ T, h * u * h⁻¹ ∈ normIn T₁ T := by
    intro u hu
    obtain ⟨huT₁, huN⟩ := mem_normIn.1 hu
    exact mem_normIn.2 ⟨conj_mem_of_mem_normalizer hhT₁ huT₁,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhT huN) (Subgroup.inv_mem _ hhT)⟩
  have hLM : ∀ c ∈ normIn T T₁, c ∈ cfgM T T₁ := fun c hc' => Cfg.normIn_le_cfgM_left T T₁ hc'
  have hL₁M : ∀ u ∈ normIn T₁ T, u ∈ cfgM T T₁ := fun u hu => Cfg.normIn_le_cfgM_right T T₁ hu
  have hMconj : ∀ a ∈ cfgM T T₁, h * a * h⁻¹ ∈ cfgM T T₁ := by
    intro a ha
    obtain ⟨c, hcL, u, huL, rfl⟩ := hcfg.mem_cfgM_iff.1 ha
    have e : h * (c * u) * h⁻¹ = (h * c * h⁻¹) * (h * u * h⁻¹) := by group
    rw [e]
    exact (cfgM T T₁).mul_mem (hLM _ (hL c hcL)) (hL₁M _ (hL₁ u huL))
  obtain ⟨Z₀, hZ₀c, hZ₀⟩ := hh.hZ₀
  obtain ⟨Z₁, hZ₁c, hZ₁⟩ := hh.hZ₁
  let Zp : Set G := (fun ab : G × G => ab.1 * ab.2) '' (Z₀ ×ˢ Z₁)
  have hZp : Zp.ncard ≤ 2 ^ m * 2 ^ m := by
    calc Zp.ncard ≤ (Z₀ ×ˢ Z₁).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = Z₀.ncard * Z₁.ncard := Set.ncard_prod
      _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul hZ₀c hZ₁c
  have hL₂card : ((normIn T₂ T : Subgroup G) : Set G).ncard = (2 ^ m) ^ (n - 1) := by
    rw [← Nat.card_coe_set_eq]
    have : Nat.card ↥(normIn T₂ T) = (2 ^ m) ^ (n - 1) := by
      rw [d.card_L₂ hc, hc.card_normIn]
    exact this
  have hlt : Zp.ncard < ((normIn T₂ T : Subgroup G) : Set G).ncard := by
    rw [hL₂card]
    calc Zp.ncard ≤ 2 ^ m * 2 ^ m := hZp
      _ = (2 ^ m) ^ 2 := (sq _).symm
      _ < (2 ^ m) ^ (n - 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hmaps : ∀ z ∈ ((normIn T₂ T : Subgroup G) : Set G),
      (fun z => h * z * h⁻¹ * z⁻¹) z ∈ Zp := by
    intro z hz
    have hzM : z ∈ cfgM T T₁ := d.L₂_le_cfgM h1 hc hne hz
    obtain ⟨c, hcL, u, huL, rfl⟩ := hcfg.mem_cfgM_iff.1 hzM
    have hb : h * u * h⁻¹ ∈ cfgM T T₁ := hL₁M _ (hL₁ u huL)
    have hu' : u⁻¹ ∈ cfgM T T₁ := (cfgM T T₁).inv_mem (hL₁M _ huL)
    have hc'' : c⁻¹ ∈ cfgM T T₁ := (cfgM T T₁).inv_mem (hLM _ hcL)
    have hcomm : c⁻¹ * (h * u * h⁻¹ * u⁻¹) = (h * u * h⁻¹ * u⁻¹) * c⁻¹ :=
      hM _ hc'' _ ((cfgM T T₁).mul_mem hb hu')
    have e : h * (c * u) * h⁻¹ * (c * u)⁻¹ = (h * c * h⁻¹ * c⁻¹) * (h * u * h⁻¹ * u⁻¹) := by
      calc h * (c * u) * h⁻¹ * (c * u)⁻¹
          = (h * c * h⁻¹) * (h * u * h⁻¹ * u⁻¹) * c⁻¹ := by group
        _ = (h * c * h⁻¹) * (c⁻¹ * (h * u * h⁻¹ * u⁻¹)) := by rw [hcomm]; group
        _ = (h * c * h⁻¹ * c⁻¹) * (h * u * h⁻¹ * u⁻¹) := by group
    show h * (c * u) * h⁻¹ * (c * u)⁻¹ ∈ Zp
    rw [e]
    exact ⟨(h * c * h⁻¹ * c⁻¹, h * u * h⁻¹ * u⁻¹), ⟨hZ₀ c hcL, hZ₁ u huL⟩, rfl⟩
  obtain ⟨z₁, hz₁, z₂, hz₂, hne12, heq⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt hmaps (Set.toFinite _)
  have hz₁M : z₁ ∈ cfgM T T₁ := d.L₂_le_cfgM h1 hc hne hz₁
  have hz₂M : z₂ ∈ cfgM T T₁ := d.L₂_le_cfgM h1 hc hne hz₂
  have ha₂M : h * z₂ * h⁻¹ ∈ cfgM T T₁ := hMconj _ hz₂M
  have heq' : h * z₁ * h⁻¹ * z₁⁻¹ = h * z₂ * h⁻¹ * z₂⁻¹ := heq
  rw [mul_inv_eq_iff_eq_mul] at heq'
  have hcomm₁ : (z₂⁻¹ * z₁) * (h * z₂ * h⁻¹)⁻¹ = (h * z₂ * h⁻¹)⁻¹ * (z₂⁻¹ * z₁) :=
    hM _ ((cfgM T T₁).mul_mem ((cfgM T T₁).inv_mem hz₂M) hz₁M) _ ((cfgM T T₁).inv_mem ha₂M)
  have hcomm₂ : z₂⁻¹ * z₁ = z₁ * z₂⁻¹ := hM _ ((cfgM T T₁).inv_mem hz₂M) _ hz₁M
  have hfix : h * (z₁ * z₂⁻¹) * h⁻¹ = z₁ * z₂⁻¹ := by
    calc h * (z₁ * z₂⁻¹) * h⁻¹ = (h * z₁ * h⁻¹) * (h * z₂ * h⁻¹)⁻¹ := by group
      _ = ((h * z₂ * h⁻¹) * z₂⁻¹ * z₁) * (h * z₂ * h⁻¹)⁻¹ := by rw [heq']
      _ = (h * z₂ * h⁻¹) * (((z₂⁻¹ * z₁) * (h * z₂ * h⁻¹)⁻¹)) := by group
      _ = (h * z₂ * h⁻¹) * ((h * z₂ * h⁻¹)⁻¹ * (z₂⁻¹ * z₁)) := by rw [hcomm₁]
      _ = z₂⁻¹ * z₁ := by group
      _ = z₁ * z₂⁻¹ := hcomm₂
  set z : G := z₁ * z₂⁻¹ with hzdef
  have hzL₂ : z ∈ normIn T₂ T := (normIn T₂ T).mul_mem hz₁ ((normIn T₂ T).inv_mem hz₂)
  have hz1 : z ≠ 1 := fun h' => hne12 (mul_inv_eq_one.1 h')
  have hzT₂ : z ∈ T₂ := normIn_le _ _ hzL₂
  have hzc : z ∈ conjSubgroup h T₂ := by
    rw [mem_conjSubgroup]
    have e : h⁻¹ * z * h = z := by
      have h' := hfix
      rw [mul_inv_eq_iff_eq_mul] at h'
      calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
        _ = h⁻¹ * (h * z) := by rw [h']
        _ = z := by group
    rw [e]
    exact hzT₂
  have hconjT₂ : ∃ k : G, conjSubgroup h T₂ = conjSubgroup k T := by
    obtain ⟨k, hk⟩ := d.hT₂
    exact ⟨h * k, by rw [hk, conjSubgroup_conjSubgroup]⟩
  have hT₂eq : conjSubgroup h T₂ = T₂ := eq_of_mem_conj hwc hconjT₂ d.hT₂ hzc hzT₂ hz1
  have hhT₂ : h ∈ Subgroup.normalizer (T₂ : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hT₂eq
  have hL₂conj : ∀ w ∈ normIn T₂ T, h * w * h⁻¹ ∈ normIn T₂ T := by
    intro w hw
    obtain ⟨hwT₂, hwN⟩ := mem_normIn.1 hw
    exact mem_normIn.2 ⟨conj_mem_of_mem_normalizer hhT₂ hwT₂,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hhT hwN) (Subgroup.inv_mem _ hhT)⟩
  obtain ⟨uv, huv, hhuv⟩ := hh.hv
  have hcfg₂ := d.sec3₂ hc
  have huvM₂ : uv ∈ cfgM T T₂ := by
    rw [d.cfgM_T₂_eq h1 hc hne]
    exact hL₁M _ huv
  obtain ⟨c, hcL₂, zv, hzvL₂, hcz⟩ := hcfg₂.cfg.mem_cfgM_iff.1 huvM₂
  rw [d.normIn_T₂ hc] at hcL₂
  have hcT : c ∈ T := normIn_le _ _ hcL₂
  have hcM : c ∈ cfgM T T₁ := hLM _ hcL₂
  have hzvM : zv ∈ cfgM T T₁ := d.L₂_le_cfgM h1 hc hne hzvL₂
  have hxM : x ∈ cfgM T T₁ := hL₁M _ d.hx
  have hwL₂ := hL₂conj zv hzvL₂
  have hwM : h * zv * h⁻¹ ∈ cfgM T T₁ := hMconj _ hzvM
  have haM : h * c * h⁻¹ ∈ cfgM T T₁ := hMconj _ hcM
  have haL : h * c * h⁻¹ ∈ normIn T T₁ := hL c hcL₂
  have E1 : (h * c * h⁻¹) * (h * zv * h⁻¹) = c * zv * x := by
    have h' : h * (c * zv) * h⁻¹ = c * zv * x := by rw [← hcz]; exact hhuv
    rw [← h']
    group
  have hzvx : zv * x = x * zv := hM _ hzvM _ hxM
  have E2 : (h * zv * h⁻¹) * zv⁻¹ = ((h * c * h⁻¹)⁻¹ * c) * x := by
    have h3 : h * zv * h⁻¹ = (h * c * h⁻¹)⁻¹ * (c * zv * x) := eq_inv_mul_of_mul_eq E1
    calc (h * zv * h⁻¹) * zv⁻¹ = (h * c * h⁻¹)⁻¹ * (c * (zv * x * zv⁻¹)) := by rw [h3]; group
      _ = (h * c * h⁻¹)⁻¹ * (c * x) := by rw [hzvx]; group
      _ = ((h * c * h⁻¹)⁻¹ * c) * x := by group
  have hyL₂ : x * l ∈ normIn T₂ T := d.mem_normIn₂
  have hr : ((h * zv * h⁻¹) * zv⁻¹) * (x * l)⁻¹ ∈ normIn T₂ T :=
    (normIn T₂ T).mul_mem ((normIn T₂ T).mul_mem hwL₂ ((normIn T₂ T).inv_mem hzvL₂))
      ((normIn T₂ T).inv_mem hyL₂)
  have hlT : l ∈ T := d.hl
  have hlM : l ∈ cfgM T T₁ := hLM _ (d.l_mem hc)
  have hxl : l * x = x * l := hM _ hlM _ hxM
  have hrT : ((h * zv * h⁻¹) * zv⁻¹) * (x * l)⁻¹ ∈ T := by
    rw [E2]
    have e : (((h * c * h⁻¹)⁻¹ * c) * x) * (x * l)⁻¹ = (h * c * h⁻¹)⁻¹ * c * l⁻¹ := by
      calc (((h * c * h⁻¹)⁻¹ * c) * x) * (x * l)⁻¹
          = (h * c * h⁻¹)⁻¹ * c * (x * (l⁻¹ * x⁻¹)) := by group
        _ = (h * c * h⁻¹)⁻¹ * c * l⁻¹ := by
          have : x * (l⁻¹ * x⁻¹) = l⁻¹ := by
            have hxl' : x * l⁻¹ = l⁻¹ * x := by
              have := hM _ hxM _ ((cfgM T T₁).inv_mem hlM)
              exact this
            calc x * (l⁻¹ * x⁻¹) = (x * l⁻¹) * x⁻¹ := by group
              _ = l⁻¹ := by rw [hxl']; group
          rw [this]
    rw [e]
    exact T.mul_mem (T.mul_mem (T.inv_mem (conj_mem_of_mem_normalizer hhT hcT)) hcT)
      (T.inv_mem hlT)
  have hrbot : ((h * zv * h⁻¹) * zv⁻¹) * (x * l)⁻¹ = 1 := by
    have hrT₂ : ((h * zv * h⁻¹) * zv⁻¹) * (x * l)⁻¹ ∈ T ⊓ T₂ := ⟨hrT, normIn_le _ _ hr⟩
    rw [(d.sec3₂ hc).cfg.inf, Subgroup.mem_bot] at hrT₂
    exact hrT₂
  have hly : l = (h * c * h⁻¹)⁻¹ * c := by
    have h4 : (h * zv * h⁻¹) * zv⁻¹ = x * l := mul_inv_eq_one.1 hrbot
    rw [E2] at h4
    have h5 : ((h * c * h⁻¹)⁻¹ * c) * x = l * x := by rw [h4, hxl]
    exact (mul_right_cancel h5).symm
  have hcT' : h * c⁻¹ * h⁻¹ * c = c * (h * c⁻¹ * h⁻¹) :=
    mul_comm_T hc (conj_mem_of_mem_normalizer hhT (T.inv_mem hcT)) hcT
  obtain ⟨t, ht, htx⟩ := hh.hT0 c hcL₂
  have hl2 : l = h * c⁻¹ * h⁻¹ * c := by rw [hly]; group
  have htx' : t * x * t⁻¹ = x * l := by rw [htx, hl2, hcT']
  have hyt : x * l ∈ conjSubgroup t T₁ := by
    rw [mem_conjSubgroup, ← htx']
    have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
    rw [e]
    exact hxT₁
  have hconjT₁ : ∃ k : G, conjSubgroup t T₁ = conjSubgroup k T := by
    obtain ⟨x₀, hx₀⟩ := hc.hy.pair.conj
    exact ⟨t * x₀, by rw [hx₀, conjSubgroup_conjSubgroup]⟩
  exact ⟨t, ht, eq_of_mem_conj hwc d.hT₂ hconjT₁ d.hyT₂ hyt d.y_ne_one⟩

end CFSG.CGT.T75K
