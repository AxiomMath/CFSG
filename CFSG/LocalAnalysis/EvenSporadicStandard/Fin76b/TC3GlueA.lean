module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem commutator_mul_central {G : Type*} [Group G] {u₁ u₂ w₁ w₂ : G}
    (h1 : ∀ g, g * w₁ = w₁ * g) (h2 : ∀ g, g * w₂ = w₂ * g) :
    (u₁ * w₁) * (u₂ * w₂) * (u₁ * w₁)⁻¹ * (u₂ * w₂)⁻¹ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by
  have cj1 : ∀ g, w₁ * g * w₁⁻¹ = g := fun g => by rw [← h1 g]; group
  have cj2 : ∀ g, g * w₂ * g⁻¹ = w₂ := fun g => by rw [h2 g]; group
  calc (u₁ * w₁) * (u₂ * w₂) * (u₁ * w₁)⁻¹ * (u₂ * w₂)⁻¹
      = u₁ * (w₁ * (u₂ * w₂) * w₁⁻¹) * u₁⁻¹ * (w₂⁻¹ * u₂⁻¹) := by group
    _ = u₁ * (u₂ * w₂) * u₁⁻¹ * (w₂⁻¹ * u₂⁻¹) := by rw [cj1]
    _ = (u₁ * u₂ * u₁⁻¹) * (u₁ * w₂ * u₁⁻¹) * (w₂⁻¹ * u₂⁻¹) := by group
    _ = (u₁ * u₂ * u₁⁻¹) * w₂ * (w₂⁻¹ * u₂⁻¹) := by rw [cj2]
    _ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by group

structure A6Pair {H : Type*} [Group H] (Ab : Subgroup H) (zb : H) : Prop where
  iso : Nonempty (↥Ab ≃* alternatingGroup (Fin 6))
  central : ∀ y : H, y * zb = zb * y
  sq : zb * zb = 1
  not_mem : zb ∉ Ab
  index_two : (Ab ⊔ zpowers zb).index = 2
  no_outer : ∀ h : H, h * h ∈ zpowers zb → h ∈ Ab ⊔ zpowers zb

namespace A6Pair

variable {H : Type*} [Group H] {Ab : Subgroup H} {zb : H} (h : A6Pair Ab zb)

include h in
theorem zpowers_le_centralizer (S : Subgroup H) : zpowers zb ≤ centralizer (S : Set H) := by
  rw [zpowers_le, mem_centralizer_iff]
  intro x _
  exact h.central x

include h in
theorem mem_sup {x : H} (hx : x ∈ Ab ⊔ zpowers zb) : ∃ a ∈ Ab, ∃ w ∈ zpowers zb, x = a * w :=
  exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_centralizer Ab) hx

include h in
theorem central_of_mem {w : H} (hw : w ∈ zpowers zb) : ∀ g : H, g * w = w * g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  intro g
  exact (Commute.zpow_right (show Commute g zb from h.central g) k).eq

include h in
theorem le_of_commutators_mem {V : Subgroup H}
    (hV : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y * x⁻¹ * y⁻¹ ∈ V) : Ab ≤ V := by
  obtain ⟨e⟩ := h.iso
  have hs6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥Ab := e.isSimpleGroup
  have hA6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hcomm : commutator ↥Ab = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥Ab) with h0 | h0
    · exfalso
      have hc : ∀ x y : ↥Ab, x * y = y * x := fun x y => by
        have hcm := (commutator_self_eq_bot_iff (H := (⊤ : Subgroup ↥Ab))).1 h0
        have := hcm.is_comm.comm (⟨x, mem_top x⟩ : (⊤ : Subgroup ↥Ab)) ⟨y, mem_top y⟩
        exact congrArg Subtype.val this
      have hc6 : ∀ a b : alternatingGroup (Fin 6), a * b = b * a := fun a b => by
        have := hc (e.symm a) (e.symm b)
        apply e.symm.injective
        rw [map_mul, map_mul]
        exact this
      have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊤ :=
        eq_top_iff.2 fun a _ => mem_center_iff.2 fun b => hc6 b a
      rw [hA6] at hcen
      exact bot_ne_top hcen
    · exact h0
  intro a ha
  have h1 : (⊤ : Subgroup ↥Ab) ≤ V.comap Ab.subtype := by
    rw [← hcomm, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hV x x.2 y y.2
  exact h1 (mem_top (⟨a, ha⟩ : ↥Ab))

include h in
theorem eq_one_of_central_mem {a : H} (ha : a ∈ Ab) (hac : ∀ y : H, y * a = a * y) : a = 1 := by
  obtain ⟨e⟩ := h.iso
  have hA6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hmem : e ⟨a, ha⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro b
    apply e.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact Subtype.ext (hac (e.symm b : ↥Ab))
  rw [hA6, mem_bot] at hmem
  have : (⟨a, ha⟩ : ↥Ab) = 1 := e.injective (by rw [hmem, map_one])
  exact congrArg Subtype.val this

include h in
theorem center_le {m : H} (hm : ∀ y : H, y * m = m * y) : m ∈ zpowers zb := by
  have case1 : ∀ x : H, (∀ y : H, y * x = x * y) → x ∈ Ab ⊔ zpowers zb → x ∈ zpowers zb := by
    intro x hx hxM
    obtain ⟨a, ha, w, hw, rfl⟩ := h.mem_sup hxM
    have hwc := h.central_of_mem hw
    have hac : ∀ y : H, y * a = a * y := by
      intro y
      calc y * a = y * (a * w) * w⁻¹ := by group
        _ = (a * w) * y * w⁻¹ := by rw [hx y]
        _ = a * (w * y) * w⁻¹ := by group
        _ = a * (y * w) * w⁻¹ := by rw [hwc y]
        _ = a * y := by group
    rw [h.eq_one_of_central_mem ha hac, one_mul]
    exact hw
  by_cases hmM : m ∈ Ab ⊔ zpowers zb
  · exact case1 m hm hmM
  · exfalso
    have hmm : m * m ∈ Ab ⊔ zpowers zb := by
      rw [Subgroup.mul_mem_iff_of_index_two h.index_two]
    have hc2 : ∀ y : H, y * (m * m) = (m * m) * y := fun y => by
      calc y * (m * m) = (y * m) * m := by group
        _ = (m * y) * m := by rw [hm y]
        _ = m * (y * m) := by group
        _ = m * (m * y) := by rw [hm y]
        _ = m * m * y := by group
    exact hmM (h.no_outer m (case1 _ hc2 hmm))

include h in
theorem exists_outer_sq (hU : ∃ U : Subgroup H, Disjoint U (zpowers zb) ∧ U ⊔ zpowers zb = ⊤) :
    ∃ u : H, u ∉ Ab ⊔ zpowers zb ∧ u * u ∈ Ab := by
  obtain ⟨U, hUd, hUt⟩ := hU
  set M := Ab ⊔ zpowers zb with hM
  have hidx : M.index = 2 := h.index_two
  have hAbM : Ab ≤ M := le_sup_left
  have hwM : ∀ w ∈ zpowers zb, w ∈ M := fun w hw => mem_sup_right hw
  have hdecomp : ∀ x : H, ∃ u ∈ U, ∃ w ∈ zpowers zb, x = u * w := fun x =>
    exists_mul_of_mem_sup_of_le_centralizer (h.zpowers_le_centralizer U) (hUt ▸ mem_top x)
  have hnotTop : M ≠ ⊤ := fun h1 => by
    rw [h1, index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨x, hxM⟩ : ∃ x, x ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hnotTop (eq_top_iff.2 fun x _ => hcon x)
  obtain ⟨u, huU, w, hw, hxuw⟩ := hdecomp x
  have huM : u ∉ M := fun huM => hxM (hxuw ▸ mul_mem huM (hwM w hw))
  refine ⟨u, huM, ?_⟩
  set V := U ⊓ M with hV
  have hAbV : Ab ≤ V := by
    apply h.le_of_commutators_mem
    intro x hx y hy
    obtain ⟨u₁, hu₁, w₁, hw₁, hxe⟩ := hdecomp x
    obtain ⟨u₂, hu₂, w₂, hw₂, hye⟩ := hdecomp y
    have hu₁M : u₁ ∈ M := by
      have : u₁ = x * w₁⁻¹ := by rw [hxe]; group
      rw [this]
      exact mul_mem (hAbM hx) (inv_mem (hwM w₁ hw₁))
    have hu₂M : u₂ ∈ M := by
      have : u₂ = y * w₂⁻¹ := by rw [hye]; group
      rw [this]
      exact mul_mem (hAbM hy) (inv_mem (hwM w₂ hw₂))
    have hcomm : x * y * x⁻¹ * y⁻¹ = u₁ * u₂ * u₁⁻¹ * u₂⁻¹ := by
      rw [hxe, hye]
      exact commutator_mul_central (h.central_of_mem hw₁) (h.central_of_mem hw₂)
    rw [hcomm]
    exact Subgroup.mem_inf.2
      ⟨U.mul_mem (U.mul_mem (U.mul_mem hu₁ hu₂) (U.inv_mem hu₁)) (U.inv_mem hu₂),
        M.mul_mem (M.mul_mem (M.mul_mem hu₁M hu₂M) (M.inv_mem hu₁M)) (M.inv_mem hu₂M)⟩
  have hVAb : V ≤ Ab := by
    intro v hv
    obtain ⟨a, ha, w, hw, hvaw⟩ := h.mem_sup hv.2
    have hw1 : w ∈ V := by
      have : w = a⁻¹ * v := by rw [hvaw]; group
      rw [this]
      exact mul_mem (inv_mem (hAbV ha)) hv
    have hw0 : w = 1 := by
      have h1 : w ∈ U ⊓ zpowers zb := ⟨hw1.1, hw⟩
      rw [hUd.eq_bot, mem_bot] at h1
      exact h1
    rw [hvaw, hw0, mul_one]
    exact ha
  have huuM : u * u ∈ M := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
  exact hVAb ⟨mul_mem huU huU, huuM⟩

end A6Pair

end CFSG.EvenSporadicStandard.Fin76b
