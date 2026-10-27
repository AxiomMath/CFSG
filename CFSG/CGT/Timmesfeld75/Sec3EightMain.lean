module

public import CFSG.CGT.Timmesfeld75.Sec3EightFixed
public import CFSG.CGT.Timmesfeld75.Sec3EightIso

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a b : G}

theorem IsLElt.false_of_inner [Finite G] (hS : Sec3 T T₁) (ha : IsLElt T T₁ a) {X : Subgroup G}
    (hTX : T ≤ X) (hT₁X : T₁ ≤ X) {t : G} (htT : t ∈ T) (htM : t ∉ cfgM T T₁)
    (hb : ∀ x ∈ X, (t⁻¹ * a) * x * (t⁻¹ * a)⁻¹ * x⁻¹ ∈ cfgM T T₁) : False := by
  have hc := hS.cfg
  have hwc := hc.wc
  have hMab : IsElemAbelian 2 (cfgM T T₁) := hc.isElemAbelian_cfgM
  have haa : a * a = 1 := ha.transv.2.1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hti : t⁻¹ = t := elemAbelian_inv hwc.1 htT
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := hS.exists_swap
  have hsX' : s ∈ X := sup_le hTX hT₁X hsX
  have hbL : ∀ l ∈ normIn T T₁, (t⁻¹ * a) * l * (t⁻¹ * a)⁻¹ = l := by
    intro l hl
    have hal : a * l = l * a := ha.transv.2.2.1 l hl
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
  have hyT : a * t * a⁻¹ ∈ T := conj_mem_of_mem_normalizer ha.transv.1 htT
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
  have hzL : z ∈ normIn T T₁ := ha.cent z hzT hza
  have hz1 : z ≠ 1 := by
    intro hz
    apply htM
    have h1 : a * t * a⁻¹ = t := by
      have : t * (a * t * a⁻¹) = 1 := by rw [← hzeq]; exact hz
      have h2 : a * t * a⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right this
      rw [h2, hti]
    exact Cfg.normIn_le_cfgM_left T T₁ (ha.cent t htT (mul_inv_eq_iff_eq_mul.1 h1))
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

namespace Sec38Hyp

variable (h : Sec38Hyp T T₁ S a b)

include h

theorem cfgM_eq [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {g : G}
    (hg : g ∈ T₁ ⊔ conjSubgroup a T₁) (hgT : conjSubgroup g T₁ = T) :
    cfgM T₁ (conjSubgroup a T₁) = cfgM T T₁ := by
  have hS2 := h.sec₂ h214 hInv
  have hTX : T ≤ T₁ ⊔ conjSubgroup a T₁ := hgT ▸ conjSubgroup_le_of_le_of_mem le_sup_left hg
  obtain ⟨hM214, -⟩ := h214 G T₁ h.sec.cfg.wc₁ a h.conj_a_ne h.normIn_conj_ne_bot
  have hNT : cfgM T₁ (conjSubgroup a T₁) ≤ Subgroup.normalizer (T : Set G) := by
    have := pCoreOf_le_normalizer_of_isWC h.sec.cfg.wc hTX
    rwa [← hM214] at this
  have hL₁N := h.normIn_le_cfgM h214 hInv
  have hXN : T₁ ⊔ conjSubgroup a T₁ ≤ Subgroup.normalizer
      (cfgM T₁ (conjSubgroup a T₁) : Set G) := hS2.cfg.le_normalizer_cfgM
  have hLN : normIn T T₁ ≤ cfgM T₁ (conjSubgroup a T₁) := by
    intro u hu
    obtain ⟨x, hxT, hxM⟩ := IsConcreteLE.not_le_iff_exists.1 h.sec.not_le_cfgM
    obtain ⟨l, hl, hlx⟩ := h.sec.exists_mem_normIn₁_conj_eq hxT hxM hu
    have h1 := conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem (hXN (hTX hxT)))
      (hL₁N hl)
    have e : u = (x⁻¹ * l * x⁻¹⁻¹)  * l⁻¹ := by
      have e0 : l * x * l⁻¹ = x * u := hlx
      calc u = x⁻¹ * (l * x * l⁻¹) := by rw [e0]; group
        _ = (x⁻¹ * l * x⁻¹⁻¹) * l⁻¹ := by group
    rw [e]
    exact (cfgM T₁ (conjSubgroup a T₁)).mul_mem h1 ((cfgM T₁ (conjSubgroup a T₁)).inv_mem (hL₁N hl))
  have hle : cfgM T T₁ ≤ cfgM T₁ (conjSubgroup a T₁) := sup_le hLN hL₁N
  have hcard : Nat.card (cfgM T₁ (conjSubgroup a T₁)) ≤ Nat.card (cfgM T T₁) := by
    rw [hS2.card_cfgM_eq_sq, h.sec.card_cfgM_eq_sq, ← h.sec.card_normIn_swap]
    have hsub : normIn T₁ (conjSubgroup a T₁) ≤ normIn T₁ T := by
      intro y hy
      exact mem_normIn.2 ⟨(mem_normIn.1 hy).1,
        hNT (Cfg.normIn_le_cfgM_left T₁ (conjSubgroup a T₁) hy)⟩
    have := Subgroup.card_le_of_le hsub
    exact Nat.pow_le_pow_left this 2
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem false_of_inputs [Finite G] [IsSimpleGroup G] (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hSz : Section3SzInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) : False := by
  have hS2 := h.sec₂ h214 hInv
  have hN := hS2.normal_cfgM_subgroupOf
  have haa := h.aa
  have haX := h.mem_normalizer_sup
  have haN := h.mem_normalizer_cfgM
  have hpair := Sec3.sylowInner_map h214 hSz hnab hS2
  have hT₁X : T₁ ≤ T₁ ⊔ conjSubgroup a T₁ := le_sup_left
  obtain ⟨g, hg, hgfix⟩ := hpair.exists_fixed_conj_of_involution hT₁X haa haX haN
  have hgT : conjSubgroup g T₁ = T := h.conj_eq_of_fixed h214 hInv hg hgfix
  have hTX : T ≤ T₁ ⊔ conjSubgroup a T₁ := hgT ▸ conjSubgroup_le_of_le_of_mem hT₁X hg
  have hpairT : SylowInner (↥(T₁ ⊔ conjSubgroup a T₁) ⧸
      (cfgM T₁ (conjSubgroup a T₁)).subgroupOf (T₁ ⊔ conjSubgroup a T₁))
      ((T.subgroupOf (T₁ ⊔ conjSubgroup a T₁)).map
        (QuotientGroup.mk' ((cfgM T₁ (conjSubgroup a T₁)).subgroupOf
          (T₁ ⊔ conjSubgroup a T₁)))) := by
    have := hpair.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥(T₁ ⊔ conjSubgroup a T₁)))
    rw [conjSubgroup_map_subgroupOf] at this
    rwa [← hgT]
  obtain ⟨t, htT, htN, hb⟩ := hpairT.exists_inner_of_unique_fixed (cfgM_le_sup _ _) hTX haa haX
    haN h.ha.transv.1 fun g' hg' hfix' => by
      have hgg : g' * g ∈ T₁ ⊔ conjSubgroup a T₁ := (T₁ ⊔ conjSubgroup a T₁).mul_mem hg' hg
      have e : conjSubgroup g' T = conjSubgroup (g' * g) T₁ := by
        rw [← hgT, conjSubgroup_conjSubgroup]
      rw [e] at hfix' ⊢
      exact h.conj_eq_of_fixed h214 hInv hgg hfix'
  rw [h.cfgM_eq h214 hInv hg hgT] at htN hb
  exact h.ha.false_of_inner h.sec hTX hT₁X htT htN hb

end Sec38Hyp

end CFSG.CGT.Timmesfeld75
