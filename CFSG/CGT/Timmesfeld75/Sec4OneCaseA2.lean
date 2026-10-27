module

public import CFSG.CGT.Timmesfeld75.Sec4OneCaseA
public import CFSG.CGT.Timmesfeld75.Sec4OneQuotient

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section CaseA2

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem cfgM_le_normalizer_right (T T₁ : Subgroup G) :
    cfgM T T₁ ≤ Subgroup.normalizer (T₁ : Set G) :=
  sup_le inf_le_right ((normIn_le _ _).trans Subgroup.le_normalizer)

theorem Sec4Hyp.conj_eq_of_fixed (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) {g : G}
    (hg : g ∈ T₁ ⊔ conjSubgroup a T₁)
    (hfix : ∀ u ∈ conjSubgroup g T₁, ∃ u' ∈ conjSubgroup g T₁, ∃ n ∈ cfgM T T₁,
      a * u * a⁻¹ = u' * n) : conjSubgroup g T₁ = T := by
  have hc := h.sec3.cfg
  have hMn : g ∈ Subgroup.normalizer (cfgM T T₁ : Set G) := by
    have := (h.cfg₁a hA).le_normalizer_cfgM hg
    rwa [h.cfgM_conj_eq hA] at this
  have hMg : conjSubgroup g (cfgM T T₁) = cfgM T T₁ := mem_normalizer_iff_conjSubgroup_eq.1 hMn
  have hMa : conjSubgroup a (cfgM T T₁) = cfgM T T₁ :=
    mem_normalizer_iff_conjSubgroup_eq.1 (h.mem_normalizer_cfgM hA)
  have hMU : cfgM T T₁ ≤ Subgroup.normalizer (conjSubgroup g T₁ : Set G) := by
    intro m hm
    rw [mem_normalizer_conjSubgroup_iff]
    apply cfgM_le_normalizer_right T T₁
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hMn) m).1 hm
    simpa using this
  obtain ⟨x, hx⟩ := h.pair.conj
  have hUc : ∃ k : G, conjSubgroup g T₁ = conjSubgroup k T :=
    ⟨g * x, by rw [hx, conjSubgroup_conjSubgroup]⟩
  have hVc : ∃ k : G, conjSubgroup a (conjSubgroup g T₁) = conjSubgroup k T :=
    ⟨a * (g * x), by rw [hx, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_assoc]⟩
  have hWne : conjSubgroup g T₁ ⊓ cfgM T T₁ ≠ ⊥ := by
    have e1 : conjSubgroup g T₁ ⊓ cfgM T T₁ = conjSubgroup g (normIn T₁ T) := by
      rw [← hc.inf_cfgM_right, conjSubgroup_inf, hMg]
    rw [e1]
    exact fun h0 => hc.ne₁ (conjSubgroup_eq_bot_iff.1 h0)
  have hlt : normIn T T₁ < T := hc.normIn_lt h.pair.conj
  have hcardlt : Nat.card (normIn T T₁) < Nat.card T := by
    by_contra hge
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (not_lt.1 hge))
  have hMab : IsElemAbelian 2 (cfgM T T₁) := hc.isElemAbelian_cfgM
  generalize hU : conjSubgroup g T₁ = U at hfix hMU hUc hVc hWne ⊢
  have hP : conjSubgroup a U ≤ U ⊔ cfgM T T₁ := by
    refine conjSubgroup_le_of_forall_mem fun u hu => ?_
    obtain ⟨u', hu', n, hn, e⟩ := hfix u hu
    rw [e]
    exact (U ⊔ cfgM T T₁).mul_mem (Subgroup.mem_sup_left hu') (Subgroup.mem_sup_right hn)
  have hUM : U ⊔ cfgM T T₁ ≤ Subgroup.normalizer (U : Set G) :=
    sup_le Subgroup.le_normalizer hMU
  have haU : conjSubgroup a U = U := by
    by_contra hne
    have hle := h.pair.card_normIn_le hVc hUc (Ne.symm hne)
    have e : normIn (conjSubgroup a U) U = conjSubgroup a U := inf_eq_left.2 (hP.trans hUM)
    obtain ⟨k, hk⟩ := hVc
    rw [e, hk, card_conjSubgroup] at hle
    exact absurd hle (not_le.2 hcardlt)
  have hW : conjSubgroup a (U ⊓ cfgM T T₁) = U ⊓ cfgM T T₁ := by
    rw [conjSubgroup_inf, haU, hMa]
  have hWab : IsElemAbelian 2 (U ⊓ cfgM T T₁) := isElemAbelian_of_le hMab inf_le_right
  obtain ⟨w, hwW, hw1, hwa⟩ := exists_fixed_ne_one_of_involution hWne
    (isPGroup_two_of_isElemAbelian hWab) h.mul_self_eq_one fun w hw => by
      rw [← hW]
      exact conj_mem_conjSubgroup a hw
  have hwL : w ∈ normIn T T₁ := by
    rw [← h.cfgM_inf_centralizer_of_not_normalizer hA]
    exact ⟨hwW.2, Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hwa).symm⟩
  obtain ⟨k, hk⟩ := hUc
  have hne : T ⊓ conjSubgroup k T ≠ ⊥ := by
    intro h0
    have hmem : w ∈ T ⊓ conjSubgroup k T := ⟨(mem_normIn.1 hwL).1, hk ▸ hwW.1⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  exact hk.trans (h.pair.wc.conj_eq_of_inf_ne_bot hne)

theorem Sec4Hyp.false_of_inner (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) {X : Subgroup G} (hTX : T ≤ X)
    (hT₁X : T₁ ≤ X) {t : G} (htT : t ∈ T) (htM : t ∉ cfgM T T₁)
    (hb : ∀ x ∈ X, (t⁻¹ * a) * x * (t⁻¹ * a)⁻¹ * x⁻¹ ∈ cfgM T T₁) : False := by
  have hc := h.sec3.cfg
  have hwc := h.pair.wc
  have hMab : IsElemAbelian 2 (cfgM T T₁) := hc.isElemAbelian_cfgM
  have haa := h.mul_self_eq_one
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hti : t⁻¹ = t := elemAbelian_inv hwc.1 htT
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := h.sec3.exists_swap
  have hsX' : s ∈ X := sup_le hTX hT₁X hsX
  have hbL : ∀ l ∈ normIn T T₁, (t⁻¹ * a) * l * (t⁻¹ * a)⁻¹ = l := by
    intro l hl
    have hal : a * l = l * a := h.comm_normIn_of_not_normalizer hA hl
    have htl : t * l = l * t := elemAbelian_mul_comm hwc.1 htT (normIn_le _ _ hl)
    calc (t⁻¹ * a) * l * (t⁻¹ * a)⁻¹ = t⁻¹ * (a * l) * a⁻¹ * t := by group
      _ = t⁻¹ * (l * t) * (a * a⁻¹) := by rw [hal, hti]; group
      _ = l := by rw [mul_inv_cancel, mul_one, ← htl]; group
  have hL₁ : normIn T₁ T = conjSubgroup s (normIn T T₁) := by
    have := normIn_conj s T T₁
    rwa [hsT, hsT₁] at this
  have hbL₁ : ∀ l ∈ normIn T₁ T, (t⁻¹ * a) * l * (t⁻¹ * a)⁻¹ = l := by
    intro l₁ hl₁
    have hl : s⁻¹ * l₁ * s ∈ normIn T T₁ := by
      rw [hL₁] at hl₁
      exact mem_conjSubgroup.1 hl₁
    have hbl := hbL _ hl
    have hm := hb s hsX'
    have hm2 : ∀ m ∈ cfgM T T₁, m * l₁ = l₁ * m := fun m hm =>
      elemAbelian_mul_comm hMab hm (Cfg.normIn_le_cfgM_right T T₁ hl₁)
    set b : G := t⁻¹ * a with hbdef
    set m : G := b * s * b⁻¹ * s⁻¹ with hmdef
    have hmM : m ∈ cfgM T T₁ := hm
    have e1 : b * l₁ * b⁻¹ = m * (s * (b * (s⁻¹ * l₁ * s) * b⁻¹) * s⁻¹) * m⁻¹ := by
      rw [hmdef]
      group
    rw [e1, hbl]
    have e2 : s * (s⁻¹ * l₁ * s) * s⁻¹ = l₁ := by group
    rw [e2, hm2 m hmM]
    group
  have hbM : ∀ m ∈ cfgM T T₁, (t⁻¹ * a) * m * (t⁻¹ * a)⁻¹ = m := by
    intro m hm
    obtain ⟨l, hl, y, hy, rfl⟩ := hc.mem_cfgM_iff.1 hm
    have e : (t⁻¹ * a) * (l * y) * (t⁻¹ * a)⁻¹ =
        ((t⁻¹ * a) * l * (t⁻¹ * a)⁻¹) * ((t⁻¹ * a) * y * (t⁻¹ * a)⁻¹) := by group
    rw [e, hbL l hl, hbL₁ y hy]
  set z : G := (t⁻¹ * a) * (t⁻¹ * a) with hzdef
  have hzeq : z = t * (a * t * a⁻¹) := by
    rw [hzdef, hti]
    calc t * a * (t * a) = t * (a * t * a) := by group
      _ = t * (a * t * a⁻¹) := by rw [hai]
  have hyT : a * t * a⁻¹ ∈ T := conj_mem_of_mem_normalizer h.mem_normalizer htT
  have hzT : z ∈ T := by
    rw [hzeq]
    exact T.mul_mem htT hyT
  have hza : a * z = z * a := by
    have h1 : a * (a * t * a⁻¹) * a⁻¹ = t := by
      calc a * (a * t * a⁻¹) * a⁻¹ = (a * a) * t * (a * a)⁻¹ := by group
        _ = t := by rw [haa]; group
    have hcomm : t * (a * t * a⁻¹) = (a * t * a⁻¹) * t := elemAbelian_mul_comm hwc.1 htT hyT
    have h2 : a * z * a⁻¹ = z := by
      rw [hzeq]
      calc a * (t * (a * t * a⁻¹)) * a⁻¹ = (a * t * a⁻¹) * (a * (a * t * a⁻¹) * a⁻¹) := by group
        _ = (a * t * a⁻¹) * t := by rw [h1]
        _ = t * (a * t * a⁻¹) := hcomm.symm
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hzL : z ∈ normIn T T₁ := by
    rw [← h.inf_centralizer_eq_of_not_normalizer hA]
    exact ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 hza.symm⟩
  have hz1 : z ≠ 1 := by
    intro hz
    apply htM
    have h1 : a * t * a⁻¹ = t := by
      have : t * (a * t * a⁻¹) = 1 := by rw [← hzeq]; exact hz
      have h2 : a * t * a⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right this
      rw [h2, hti]
    have htL : t ∈ normIn T T₁ := by
      rw [← h.inf_centralizer_eq_of_not_normalizer hA]
      exact ⟨htT, Subgroup.mem_centralizer_singleton_iff.2
        (by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1.symm)⟩
    exact Cfg.normIn_le_cfgM_left T T₁ htL
  have hXz : ∀ x ∈ X, x * z * x⁻¹ = z := by
    intro x hx
    have hc' := hb x hx
    have hcinv := (cfgM T T₁).inv_mem hc'
    set b : G := t⁻¹ * a with hbdef
    set c : G := (b * x * b⁻¹ * x⁻¹)⁻¹ with hcdef
    have hcM : c ∈ cfgM T T₁ := hcinv
    have hxb : x * b * x⁻¹ = c * b := by
      rw [hcdef]
      group
    have hbc : b * c * b⁻¹ = c := hbM c hcM
    have hcc : c * c = 1 := elemAbelian_mul_self hMab hcM
    calc x * z * x⁻¹ = (x * b * x⁻¹) * (x * b * x⁻¹) := by rw [hzdef]; group
      _ = c * (b * c * b⁻¹) * (b * b) := by rw [hxb]; group
      _ = (c * c) * (b * b) := by rw [hbc]
      _ = z := by rw [hcc, one_mul]
  have hT₁N : T₁ ≤ Subgroup.normalizer (T : Set G) := fun x hx =>
    hwc.centralizer_le_normalizer hzT hz1 (Subgroup.mem_centralizer_singleton_iff.2 (by
      have := hXz x (hT₁X hx)
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this))
  have hlt : normIn T₁ T < T₁ := hc.symm.normIn_lt ⟨s, hsT₁.symm⟩
  exact hlt.ne (le_antisymm (normIn_le _ _) fun x hx => mem_normIn.2 ⟨hx, hT₁N hx⟩)

theorem Sec4Hyp.false_of_not_normalizer (h : Sec4Hyp T T₁ a T₂)
    (hA : a ∉ Subgroup.normalizer (normIn T₁ T : Set G)) : False := by
  have haa := h.mul_self_eq_one
  have hne := h.conj_ne hA
  have hL : normIn T₁ (conjSubgroup a T₁) ≠ ⊥ := by
    rw [h.normIn_conj_eq hA]
    exact h.sec3.cfg.ne₁
  have hS' : Sec3 T₁ (conjSubgroup a T₁) :=
    sec3_of_conj_conj h.glob h.pair.conj h.conj_conj hne hL
  have hI' : Sec3Iso T₁ (conjSubgroup a T₁) :=
    sec3Iso_of_conj_conj h.iso h.pair.conj h.conj_conj hne hL
  obtain ⟨hN, f, hf, hpair⟩ := hS'.exists_isL2Pair hI'
  have hCM := h.cfgM_conj_eq hA
  have haN : a ∈ Subgroup.normalizer (cfgM T₁ (conjSubgroup a T₁) : Set G) := by
    rw [hCM]
    exact h.mem_normalizer_cfgM hA
  have haX : a ∈ Subgroup.normalizer ((T₁ ⊔ conjSubgroup a T₁ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup, conjSubgroup_conjSubgroup,
      haa, conjSubgroup_one, sup_comm]
  have hT₁X : T₁ ≤ T₁ ⊔ conjSubgroup a T₁ := le_sup_left
  obtain ⟨g, hg, hgfix⟩ := exists_fixed_conj_of_involution hT₁X hpair haa haX haN
  rw [hCM] at hgfix
  have hgT : conjSubgroup g T₁ = T := h.conj_eq_of_fixed hA hg hgfix
  have hTX : T ≤ T₁ ⊔ conjSubgroup a T₁ := hgT ▸ conjSubgroup_le_of_le_of_mem hT₁X hg
  have hpairT : IsL2Pair (↥(T₁ ⊔ conjSubgroup a T₁) ⧸
      (cfgM T₁ (conjSubgroup a T₁)).subgroupOf (T₁ ⊔ conjSubgroup a T₁))
      ((T.subgroupOf (T₁ ⊔ conjSubgroup a T₁)).map
        (QuotientGroup.mk' ((cfgM T₁ (conjSubgroup a T₁)).subgroupOf
          (T₁ ⊔ conjSubgroup a T₁)))) (2 ^ f) := by
    have := hpair.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥(T₁ ⊔ conjSubgroup a T₁)))
    rw [conjSubgroup_map_subgroupOf] at this
    rwa [← hgT]
  obtain ⟨t, htT, htN, hb⟩ := exists_inner_of_unique_fixed (cfgM_le_sup _ _) hTX hpairT haa haX haN
    h.mem_normalizer fun g' hg' hfix' => by
      have hgg : g' * g ∈ T₁ ⊔ conjSubgroup a T₁ := (T₁ ⊔ conjSubgroup a T₁).mul_mem hg' hg
      have e : conjSubgroup g' T = conjSubgroup (g' * g) T₁ := by
        rw [← hgT, conjSubgroup_conjSubgroup]
      rw [hCM] at hfix'
      rw [e] at hfix' ⊢
      exact h.conj_eq_of_fixed hA hgg hfix'
  rw [hCM] at htN hb
  exact h.false_of_inner hA hTX hT₁X htT htN hb

end CaseA2

end CFSG.CGT.Timmesfeld75
