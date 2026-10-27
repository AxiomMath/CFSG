module

public import CFSG.GH74.GLS.IVK.Prod32.LangFixedAux

public section

namespace CFSG.GH74.GLS.IVK.Prod3.LangF

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open scoped commutatorElement

section S3

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem conj_mem₁ {c x : H} (hc : c ∈ K₁ ⊔ K₂) (hx : x ∈ K₁) : c * x * c⁻¹ ∈ K₁ := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff h).1 hc
  have h1 : k₂ * x * k₂⁻¹ = x := by rw [← h.comm x hx k₂ hk₂, mul_inv_cancel_right]
  have : k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₁ * x * k₁⁻¹ := by
    calc k₁ * k₂ * x * (k₁ * k₂)⁻¹ = k₁ * (k₂ * x * k₂⁻¹) * k₁⁻¹ := by group
      _ = k₁ * x * k₁⁻¹ := by rw [h1]
  rw [this]
  exact mul_mem (mul_mem hk₁ hx) (inv_mem hk₁)

theorem cen_normal₁ : ((cen K₁ a).subgroupOf (cen (K₁ ⊔ K₂) a)).Normal := by
  constructor
  intro n hn g
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨hn₁, hn₂⟩ := mem_cen.1 hn
  obtain ⟨hg₁, hg₂⟩ := mem_cen.1 g.2
  rw [mem_cen]
  exact ⟨conj_mem₁ h hg₁ hn₁, conj_comm_a hg₂ hn₂⟩

theorem commutator_mem_cen₁ {k₁ l₁ u v : H} (hk₁ : k₁ ∈ K₁) (hl₁ : l₁ ∈ K₁) (hu : u ∈ K₁ ⊓ K₂)
    (hv : v ∈ K₁ ⊓ K₂) (hku : a * k₁ * a⁻¹ = k₁ * u) (hlv : a * l₁ * a⁻¹ = l₁ * v) :
    ⁅k₁, l₁⁆ ∈ cen K₁ a := by
  rw [mem_cen]
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk₁ hl₁) (inv_mem hk₁)) (inv_mem hl₁)
  · have h1 : a * ⁅k₁, l₁⁆ * a⁻¹ = ⁅k₁, l₁⁆ := by
      have := map_commutatorElement (MulAut.conj a) k₁ l₁
      simp only [MulAut.conj_apply] at this
      rw [this, hku, hlv]
      exact commutatorElement_mul_mul
        (Commute.symm (h.comm l₁ hl₁ u hu.2))
        (Commute.symm (h.comm k₁ hk₁ v hv.2))
        (h.comm u hu.1 v hv.2)
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem commutator_mem_sup {c d : H} (hc : c ∈ cen (K₁ ⊔ K₂) a) (hd : d ∈ cen (K₁ ⊔ K₂) a) :
    ⁅c, d⁆ ∈ cen K₁ a ⊔ cen K₂ a := by
  obtain ⟨hcK, hca⟩ := mem_cen.1 hc
  obtain ⟨hdK, hda⟩ := mem_cen.1 hd
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff h).1 hcK
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := (mem_sup_iff h).1 hdK
  obtain ⟨u, hu, hu₁, hu₂⟩ := exists_twist_of_fixed h hk₁ hk₂ hca
  obtain ⟨v, hv, hv₁, hv₂⟩ := exists_twist_of_fixed h hl₁ hl₂ hda
  obtain ⟨hu₁', hu₂'⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hv₁', hv₂'⟩ := Subgroup.mem_inf.1 hv
  rw [commutator_split h.comm hk₁ hl₁ hk₂ hl₂]
  exact mul_mem (mem_sup_left (commutator_mem_cen₁ h hk₁ hl₁ hu hv hu₁ hv₁))
    (mem_sup_right (commutator_mem_cen₁ (symm h) hk₂ hl₂ (u := u⁻¹) (v := v⁻¹)
      (Subgroup.mem_inf.2 ⟨inv_mem hu₂', inv_mem hu₁'⟩)
      (Subgroup.mem_inf.2 ⟨inv_mem hv₂', inv_mem hv₁'⟩) hu₂ hv₂))

end S3

section S3b

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem isComponent_cen₁ [Finite F₁] {r : ℕ} (hr : 3 ≤ r) (hF₁ : Nat.card F₁ = r ^ 4) :
    CFSG.IsComponent ((cen K₁ a).subgroupOf (cen (K₁ ⊔ K₂) a)) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (cen_le_cen_sup₁ K₁ K₂ a)).symm (isQuasisimple_cen₁ h hr hF₁),
    (cen_normal₁ h).isSubnormal⟩

theorem isComponent_cen₂ [Finite F₂] {r : ℕ} (hr : 3 ≤ r) (hF₂ : Nat.card F₂ = r ^ 4) :
    CFSG.IsComponent ((cen K₂ a).subgroupOf (cen (K₁ ⊔ K₂) a)) := by
  have := isComponent_cen₁ (symm h) hr hF₂
  rwa [sup_comm] at this

theorem layer_le :
    layer ↥(cen (K₁ ⊔ K₂) a) ≤ (cen K₁ a ⊔ cen K₂ a).subgroupOf (cen (K₁ ⊔ K₂) a) := by
  refine sSup_le fun L hL => ?_
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hL.1.1
  refine le_of_eq_of_le hperf.symm (Subgroup.commutator_le.2 ?_)
  intro g₁ _ g₂ _
  rw [mem_subgroupOf]
  exact commutator_mem_sup h g₁.2 g₂.2

theorem eLayer_cen_sup [Finite F₁] [Finite F₂] {r : ℕ} (hr : 3 ≤ r) (hF₁ : Nat.card F₁ = r ^ 4)
    (hF₂ : Nat.card F₂ = r ^ 4) :
    ELayer (cen (K₁ ⊔ K₂) a) = ELayer (cen K₁ a) ⊔ ELayer (cen K₂ a) := by
  rw [eLayer_cen₁ h hr hF₁, eLayer_cen₁ (symm h) hr hF₂]
  apply le_antisymm
  · calc ELayer (cen (K₁ ⊔ K₂) a)
        ≤ ((cen K₁ a ⊔ cen K₂ a).subgroupOf (cen (K₁ ⊔ K₂) a)).map (cen (K₁ ⊔ K₂) a).subtype :=
          Subgroup.map_mono (layer_le h)
      _ = (cen K₁ a ⊔ cen K₂ a) ⊓ cen (K₁ ⊔ K₂) a := Subgroup.subgroupOf_map_subtype _ _
      _ ≤ cen K₁ a ⊔ cen K₂ a := inf_le_left
  · refine sup_le ?_ ?_
    · calc cen K₁ a = ((cen K₁ a).subgroupOf (cen (K₁ ⊔ K₂) a)).map (cen (K₁ ⊔ K₂) a).subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (cen_le_cen_sup₁ K₁ K₂ a)]
        _ ≤ ELayer (cen (K₁ ⊔ K₂) a) :=
            Subgroup.map_mono (CFSG.LocalCores.component_le_layer (isComponent_cen₁ h hr hF₁))
    · calc cen K₂ a = ((cen K₂ a).subgroupOf (cen (K₁ ⊔ K₂) a)).map (cen (K₁ ⊔ K₂) a).subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (cen_le_cen_sup₂ K₁ K₂ a)]
        _ ≤ ELayer (cen (K₁ ⊔ K₂) a) :=
            Subgroup.map_mono (CFSG.LocalCores.component_le_layer (isComponent_cen₂ h hr hF₂))

end S3b

end CFSG.GH74.GLS.IVK.Prod3.LangF
