module

public import CFSG.CGT.Timmesfeld75.Sec4OneCommon

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section CaseB

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem Sec4Hyp.comm_of_mem_normalizer (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) {l : G} (hl : l ∈ normIn T₁ T) :
    a * l = l * a := by
  have h1 : ⁅a, l⁆ ∈ T := h.hcomm l hl
  have h2 : ⁅a, l⁆ ∈ normIn T₁ T := by
    rw [commutatorElement_def]
    exact (normIn T₁ T).mul_mem (conj_mem_of_mem_normalizer hB hl) ((normIn T₁ T).inv_mem hl)
  have h3 : ⁅a, l⁆ ∈ T ⊓ T₁ := ⟨h1, normIn_le _ _ h2⟩
  rw [h.sec3.cfg.inf, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 h3

omit [Finite G] in
theorem Sec4Hyp.normIn_le_normalizer₂ (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) :
    normIn T₁ T ≤ Subgroup.normalizer (T₂ : Set G) := by
  obtain ⟨g, hg⟩ := h.conj
  have hwc₂ : IsWC T₂ := hg ▸ h.pair.wc.conj g
  intro l hl
  exact hwc₂.centralizer_le_normalizer h.haT₂ h.ne_one
    (Subgroup.mem_centralizer_singleton_iff.2 (h.comm_of_mem_normalizer hB hl).symm)

theorem Sec4Hyp.normIn_right_eq (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) : normIn T₁ T₂ = normIn T₁ T := by
  have hle : normIn T₁ T ≤ normIn T₁ T₂ := fun l hl =>
    mem_normIn.2 ⟨(mem_normIn.1 hl).1, h.normIn_le_normalizer₂ hB hl⟩
  have hcard : Nat.card (normIn T₁ T₂) ≤ Nat.card (normIn T₁ T) := by
    rw [h.card_normIn₁]
    exact h.pair.card_normIn_le h.pair.conj h.conj h.ne_right
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem Sec4Hyp.cfg₁₂ (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) : Cfg T₁ T₂ :=
  cfg_of_conj_conj h.pair.wc h.pair.conj h.conj h.ne_right (by
    rw [h.normIn_right_eq hB]
    exact h.sec3.cfg.ne₁)

theorem Sec4Hyp.card_normIn₂₁ (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) :
    Nat.card (normIn T₂ T₁) = Nat.card (normIn T T₁) := by
  have hconj : ∃ x : G, T₂ = conjSubgroup x T₁ := exists_conj_of_conj_conj h.pair.conj h.conj
  rw [← (h.cfg₁₂ hB).card_normIn_eq hconj, h.normIn_right_eq hB, h.card_normIn₁]

theorem Sec4Hyp.normIn₂_le (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) : normIn T₂ T ≤ normIn T₂ T₁ := by
  have hc21 : Cfg T₂ T₁ := (h.cfg₁₂ hB).symm
  intro x hx
  by_contra hxΛ
  have hxT₂ : x ∈ T₂ := (mem_normIn.1 hx).1
  have hxM : x ∉ cfgM T₂ T₁ := fun hM => hxΛ (by rw [← hc21.inf_cfgM]; exact ⟨hxT₂, hM⟩)
  have hC : ∀ l ∈ normIn T₁ T, l * x = x * l → l = 1 := by
    intro l hl hlx
    have hl₂ : l ∈ normIn T₁ T₂ := by rw [h.normIn_right_eq hB]; exact hl
    have hlM : l ∈ cfgM T₂ T₁ := Cfg.normIn_le_cfgM_right T₂ T₁ hl₂
    have hl' : l ∈ cfgM T₂ T₁ ⊓ Subgroup.centralizer ({x} : Set G) :=
      ⟨hlM, Subgroup.mem_centralizer_singleton_iff.2 hlx⟩
    rw [hc21.cfgM_inf_centralizer hxT₂ hxM] at hl'
    have h12 : l ∈ T₁ ⊓ T₂ := ⟨(mem_normIn.1 hl).1, (mem_normIn.1 hl').1⟩
    rw [h.inf_right_eq_bot, Subgroup.mem_bot] at h12
    exact h12
  have hnorm₂ : ∀ l ∈ normIn T₁ T, l * x * l⁻¹ ∈ normIn T₂ T := by
    intro l hl
    obtain ⟨-, hlN⟩ := mem_normIn.1 hl
    refine mem_normIn.2 ⟨conj_mem_of_mem_normalizer (h.normIn_le_normalizer₂ hB hl) hxT₂, ?_⟩
    exact (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem hlN (mem_normIn.1 hx).2)
      ((Subgroup.normalizer (T : Set G)).inv_mem hlN)
  let f : normIn T₁ T → normIn T₂ T := fun l => ⟨l * x * l⁻¹, hnorm₂ l l.2⟩
  have hinj : Function.Injective f := by
    intro l l' hll
    have h1 : (l : G) * x * (l : G)⁻¹ = l' * x * (l' : G)⁻¹ := congrArg Subtype.val hll
    have hm : (l' : G)⁻¹ * l ∈ normIn T₁ T :=
      (normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem l'.2) l.2
    have hcomm : ((l' : G)⁻¹ * l) * x = x * ((l' : G)⁻¹ * l) :=
      calc ((l' : G)⁻¹ * l) * x = (l' : G)⁻¹ * (l * x * (l : G)⁻¹) * l := by group
        _ = (l' : G)⁻¹ * (l' * x * (l' : G)⁻¹) * l := by rw [h1]
        _ = x * ((l' : G)⁻¹ * l) := by group
    exact Subtype.ext (inv_mul_eq_one.1 (hC _ hm hcomm)).symm
  have hcard : Nat.card (normIn T₂ T) ≤ Nat.card (normIn T₁ T) := by
    rw [h.card_normIn₂, h.card_normIn₁]
    exact h.card_normIn_le
  obtain ⟨l, hl⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨1, (normIn T₂ T).one_mem⟩
  have h1 : (l : G) * x * (l : G)⁻¹ = 1 := congrArg Subtype.val hl
  have hx1 : x = 1 :=
    calc x = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * l := by group
      _ = 1 := by rw [h1]; group
  exact hxΛ (hx1 ▸ (normIn T₂ T₁).one_mem)

theorem Sec4Hyp.comm_normIn₂ (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) {x l : G} (hx : x ∈ normIn T₂ T)
    (hl : l ∈ normIn T₁ T) : x * l = l * x := by
  have hxΛ := h.normIn₂_le hB hx
  exact mul_comm_of_mem_inf_normalizer h.inf_right_eq_bot (mem_normIn.1 hx).1
    (mem_normIn.1 hxΛ).2 (mem_normIn.1 hl).1 (h.normIn_le_normalizer₂ hB hl)

theorem Sec4Hyp.normIn_le_normIn (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) : normIn T T₂ ≤ normIn T T₁ := by
  have hS := h.sec3
  intro c hc
  by_contra hcL
  obtain ⟨hcT, hcN⟩ := mem_normIn.1 hc
  have hcM : c ∉ cfgM T T₁ := fun hM => hcL (by rw [← hS.cfg.inf_cfgM]; exact ⟨hcT, hM⟩)
  have hL₁N : ∀ l ∈ normIn T₁ T, l * c * l⁻¹ ∈ normIn T T₂ := by
    intro l hl
    obtain ⟨-, hlN⟩ := mem_normIn.1 hl
    have hl₂ := h.normIn_le_normalizer₂ hB hl
    exact mem_normIn.2 ⟨conj_mem_of_mem_normalizer hlN hcT,
      (Subgroup.normalizer (T₂ : Set G)).mul_mem
        ((Subgroup.normalizer (T₂ : Set G)).mul_mem hl₂ hcN)
        ((Subgroup.normalizer (T₂ : Set G)).inv_mem hl₂)⟩
  have hLle : normIn T T₁ ≤ normIn T T₂ := by
    intro u hu
    obtain ⟨l, hl, hlc⟩ := hS.exists_mem_normIn₁_conj_eq hcT hcM hu
    have h1 : c⁻¹ * (l * c * l⁻¹) ∈ normIn T T₂ :=
      (normIn T T₂).mul_mem ((normIn T T₂).inv_mem hc) (hL₁N l hl)
    rw [hlc, inv_mul_cancel_left] at h1
    exact h1
  have hEq : normIn T T₁ = normIn T T₂ := Subgroup.eq_of_le_of_card_ge hLle h.card_normIn_le
  exact hcL (hEq ▸ hc)

theorem Sec4Hyp.comm_normIn (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) {u : G} (hu : u ∈ normIn T T₁) :
    a * u = u * a := by
  have hS := h.sec3
  have haa := h.mul_self_eq_one
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  obtain ⟨t, htT, htL⟩ := IsConcreteLE.exists_of_lt (hS.cfg.normIn_lt h.pair.conj)
  have htM : t ∉ cfgM T T₁ := fun hM => htL (by rw [← hS.cfg.inf_cfgM]; exact ⟨htT, hM⟩)
  obtain ⟨l, hl, hlt⟩ := hS.exists_mem_normIn₁_conj_eq htT htM hu
  have hal : a * l * a⁻¹ = l := by rw [h.comm_of_mem_normalizer hB hl]; group
  have hal' : a * l⁻¹ * a⁻¹ = l⁻¹ :=
    calc a * l⁻¹ * a⁻¹ = (a * l * a⁻¹)⁻¹ := by group
      _ = l⁻¹ := by rw [hal]
  set s : G := a * t * a⁻¹ * t⁻¹ with hs
  have hsT : s ∈ T := T.mul_mem (conj_mem_of_mem_normalizer h.mem_normalizer htT) (T.inv_mem htT)
  have hsa : a * s * a⁻¹ = s := by
    have h1 : a * s * a⁻¹ = s⁻¹ :=
      calc a * s * a⁻¹ = (a * a) * t * a⁻¹ * t⁻¹ * a⁻¹ := by rw [hs]; group
        _ = t * a⁻¹ * t⁻¹ * a⁻¹ := by rw [haa, one_mul]
        _ = t * a * t⁻¹ * a⁻¹ := by rw [ha']
        _ = s⁻¹ := by rw [hs]; group
    rw [h1]
    exact elemAbelian_inv h.pair.wc.1 hsT
  have hsC : s ∈ T ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hsT, Subgroup.mem_centralizer_singleton_iff.2 (by
      have := congrArg (· * a) hsa
      simpa [mul_assoc] using this.symm)⟩
  have hsL : s ∈ normIn T T₁ := h.normIn_le_normIn hB (h.inf_centralizer_eq ▸ hsC)
  have hlsl : l * s * l⁻¹ = s := by
    rw [← hS.cfg.comm_L_L₁ hsL hl]
    group
  have hu' : u = t⁻¹ * l * t * l⁻¹ := by
    have : t⁻¹ * (l * t * l⁻¹) = u := by rw [hlt]; group
    rw [← this]
    group
  have key : a * u * a⁻¹ * u⁻¹ = t⁻¹ * (s⁻¹ * (l * s * l⁻¹)) * t := by
    have e1 : a * u * a⁻¹ = (a * t * a⁻¹)⁻¹ * l * (a * t * a⁻¹) * l⁻¹ := by
      rw [hu']
      calc a * (t⁻¹ * l * t * l⁻¹) * a⁻¹
          = (a * t⁻¹ * a⁻¹) * (a * l * a⁻¹) * (a * t * a⁻¹) * (a * l⁻¹ * a⁻¹) := by group
        _ = (a * t * a⁻¹)⁻¹ * l * (a * t * a⁻¹) * l⁻¹ := by rw [hal, hal']; group
    rw [e1, hu', hs]
    group
  have h1 : a * u * a⁻¹ * u⁻¹ = 1 := by rw [key, hlsl]; group
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem Sec4Hyp.normIn_eq (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) : normIn T T₂ = normIn T T₁ := by
  refine le_antisymm (h.normIn_le_normIn hB) fun u hu => ?_
  rw [← h.inf_centralizer_eq]
  exact ⟨(mem_normIn.1 hu).1, Subgroup.mem_centralizer_singleton_iff.2 (h.comm_normIn hB hu).symm⟩

theorem Sec4Hyp.card_normIn₂_eq (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) :
    Nat.card (normIn T₂ T) = Nat.card (normIn T T₁) := by
  rw [h.card_normIn₂, h.normIn_eq hB]

theorem Sec4Hyp.normIn₂_eq (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) : normIn T₂ T = normIn T₂ T₁ :=
  Subgroup.eq_of_le_of_card_ge (h.normIn₂_le hB)
    (by rw [h.card_normIn₂₁ hB, h.card_normIn₂_eq hB])

theorem Sec4Hyp.isElemAbelian_normIn (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) :
    IsElemAbelian 2 (normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T) := by
  obtain ⟨g, hg⟩ := h.conj
  have hwc₂ : IsWC T₂ := hg ▸ h.pair.wc.conj g
  have hM : IsElemAbelian 2 (normIn T T₁ ⊔ normIn T₁ T) := h.sec3.cfg.isElemAbelian_cfgM
  have hL₂ : IsElemAbelian 2 (normIn T₂ T) := isElemAbelian_of_le hwc₂.1 (normIn_le _ _)
  refine isElemAbelian_sup_of_comm hM hL₂ fun x hx y hy => ?_
  have hcent : normIn T T₁ ⊔ normIn T₁ T ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun l hl => ?_)
    · have hl' : l ∈ normIn T T₂ := by rw [h.normIn_eq hB]; exact hl
      exact Subgroup.mem_centralizer_singleton_iff.2 (h.cfg₂.comm_L_L₁ hl' hy)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h.comm_normIn₂ hB hy hl).symm
  exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hx)

theorem Sec4Hyp.normal_normIn (h : Sec4Hyp T T₁ a T₂)
    (hB : a ∈ Subgroup.normalizer (normIn T₁ T : Set G)) :
    ((normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T).subgroupOf (T ⊔ T₁ ⊔ T₂)).Normal := by
  have hc₁ := h.sec3.cfg
  have hc₂ := h.cfg₂
  have hc₁₂ := h.cfg₁₂ hB
  have hwc := h.pair.wc
  have hM₂ : cfgM T T₂ = normIn T T₁ ⊔ normIn T₂ T := by rw [cfgM, h.normIn_eq hB]
  have hM₁₂ : cfgM T₁ T₂ = normIn T₁ T ⊔ normIn T₂ T := by
    rw [cfgM, h.normIn_right_eq hB, ← h.normIn₂_eq hB]
  have hLN : normIn T T₁ ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T :=
    le_sup_of_le_left le_sup_left
  have hL₁N : normIn T₁ T ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T :=
    le_sup_of_le_left le_sup_right
  have hL₂N : normIn T₂ T ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T := le_sup_right
  have hTY : T ≤ T ⊔ T₁ ⊔ T₂ := le_sup_of_le_left le_sup_left
  have hT₁Y : T₁ ≤ T ⊔ T₁ ⊔ T₂ := le_sup_of_le_left le_sup_right
  have hT₂Y : T₂ ≤ T ⊔ T₁ ⊔ T₂ := le_sup_right
  have hNY : normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T ≤ T ⊔ T₁ ⊔ T₂ :=
    sup_le (sup_le ((normIn_le T T₁).trans hTY) ((normIn_le T₁ T).trans hT₁Y))
      ((normIn_le T₂ T).trans hT₂Y)
  have hconjN : ∀ g : G,
      (∀ x ∈ normIn T T₁, g * x * g⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T) →
      (∀ x ∈ normIn T₁ T, g * x * g⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T) →
      (∀ x ∈ normIn T₂ T, g * x * g⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T) →
      conjSubgroup g (normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T) ≤
        normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T := fun g h1 h2 h3 => by
    rw [conjSubgroup_sup_eq_sup, conjSubgroup_sup_eq_sup]
    exact sup_le (sup_le (conjSubgroup_le_of_forall_mem h1) (conjSubgroup_le_of_forall_mem h2))
      (conjSubgroup_le_of_forall_mem h3)
  have hmove : ∀ {g : G} {M : Subgroup G}, g ∈ Subgroup.normalizer (M : Set G) →
      M ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T → ∀ x ∈ M,
        g * x * g⁻¹ ∈ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T :=
    fun hg hMN x hx => hMN ((Subgroup.mem_normalizer_iff.1 hg x).1 hx)
  have hM₁N : cfgM T T₁ ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T := sup_le hLN hL₁N
  have hM₂N : cfgM T T₂ ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T := by
    rw [hM₂]; exact sup_le hLN hL₂N
  have hM₁₂N : cfgM T₁ T₂ ≤ normIn T T₁ ⊔ normIn T₁ T ⊔ normIn T₂ T := by
    rw [hM₁₂]; exact sup_le hL₁N hL₂N
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).2 ?_
  refine sup_le (sup_le ?_ ?_) ?_
  ·
    refine le_normalizer_of_conjSubgroup_le fun g hg => hconjN g (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [elemAbelian_mul_comm hwc.1 hg (normIn_le _ _ hx), mul_inv_cancel_right]
      exact hLN hx
    · exact hmove (hc₁.le_normalizer_cfgM (Subgroup.mem_sup_left hg)) hM₁N x
        (Cfg.normIn_le_cfgM_right T T₁ hx)
    · exact hmove (hc₂.le_normalizer_cfgM (Subgroup.mem_sup_left hg)) hM₂N x
        (by rw [hM₂]; exact Subgroup.mem_sup_right hx)
  ·
    refine le_normalizer_of_conjSubgroup_le fun g hg => hconjN g (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_)
    · exact hmove (hc₁.le_normalizer_cfgM (Subgroup.mem_sup_right hg)) hM₁N x
        (Cfg.normIn_le_cfgM_left T T₁ hx)
    · rw [elemAbelian_mul_comm (hc₁.wc₁).1 hg (normIn_le _ _ hx), mul_inv_cancel_right]
      exact hL₁N hx
    · exact hmove (hc₁₂.le_normalizer_cfgM (Subgroup.mem_sup_left hg)) hM₁₂N x
        (by rw [hM₁₂]; exact Subgroup.mem_sup_right hx)
  ·
    refine le_normalizer_of_conjSubgroup_le fun g hg => hconjN g (fun x hx => ?_)
      (fun x hx => ?_) (fun x hx => ?_)
    · exact hmove (hc₂.le_normalizer_cfgM (Subgroup.mem_sup_right hg)) hM₂N x
        (by rw [hM₂]; exact Subgroup.mem_sup_left hx)
    · exact hmove (hc₁₂.le_normalizer_cfgM (Subgroup.mem_sup_right hg)) hM₁₂N x
        (by rw [hM₁₂]; exact Subgroup.mem_sup_left hx)
    · rw [elemAbelian_mul_comm (hc₂.wc₁).1 hg (normIn_le _ _ hx), mul_inv_cancel_right]
      exact hL₂N hx

end CaseB

end CFSG.CGT.Timmesfeld75
