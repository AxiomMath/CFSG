module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplStep2C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplCompl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

namespace S8Data

variable {P : Type} [Group P] {V1 V2 : Subgroup P} {φ1 φ2 : (Fin 5 → ZMod 2) → P}
  {α β : P →* S8A5}

theorem H_disj (h : S8Data V1 V2 φ1 φ2 α β) : s8H V2 ⊓ s8H V1 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hx1, hx2⟩
  have hb : β x = 1 := by
    have := h.H_le_cent hx1
    rw [h.cent_V2] at this; exact MonoidHom.mem_ker.mp this
  have ha : α x = 1 := by
    have := h.swap.H_le_cent hx2
    rw [h.cent_V1] at this; exact MonoidHom.mem_ker.mp this
  have hxV : x ∈ V1 ⊔ V2 := h.ker x ha hb
  have hxV1 : x ∈ V1 := by
    have : x ∈ s8H V2 ⊓ (V1 ⊔ V2) := ⟨hx1, hxV⟩
    rwa [h.H_inf_V] at this
  have hxV2 : x ∈ V2 := by
    have : x ∈ s8H V1 ⊓ (V2 ⊔ V1) := ⟨hx2, by rwa [sup_comm]⟩
    rwa [h.swap.H_inf_V] at this
  have : x ∈ V1 ⊓ V2 := ⟨hxV1, hxV2⟩
  rwa [h.disj, Subgroup.mem_bot] at this

theorem H_comm (h : S8Data V1 V2 φ1 φ2 α β) :
    ∀ x ∈ s8H V2, ∀ y ∈ s8H V1, x * y = y * x := by
  intro x hx y hy
  haveI := h.H_normal
  haveI := h.swap.H_normal
  exact Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
    (disjoint_iff.mpr h.H_disj) x y hx hy

theorem H_sup (h : S8Data V1 V2 φ1 φ2 α β) : s8H V2 ⊔ s8H V1 = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨x1, hx1, hx1a⟩ := h.alpha_surj_H (α g)
  have hg1 : α (x1⁻¹ * g) = 1 := by simp [hx1a]
  obtain ⟨y, hy, hyb⟩ := h.swap.alpha_surj_H (β (x1⁻¹ * g))
  have hya : α y = 1 := by
    have := h.swap.H_le_cent hy
    rw [h.cent_V1] at this; exact MonoidHom.mem_ker.mp this
  have hrest : y⁻¹ * (x1⁻¹ * g) ∈ V1 ⊔ V2 := by
    refine h.ker _ ?_ ?_
    · rw [map_mul, map_inv, hya, hg1]; simp
    · rw [map_mul, map_inv, hyb]; simp
  have hVle : V1 ⊔ V2 ≤ s8H V2 ⊔ s8H V1 :=
    sup_le (h.V1_le_H.trans le_sup_left) (h.swap.V1_le_H.trans le_sup_right)
  have e : g = x1 * y * (y⁻¹ * (x1⁻¹ * g)) := by group
  rw [e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hx1) (Subgroup.mem_sup_right hy)) (hVle hrest)

theorem H_compl [Finite P] (h : S8Data V1 V2 φ1 φ2 α β) :
    ∃ C : Subgroup P, C ≤ s8H V2 ∧ V1 ⊓ C = ⊥ ∧ V1 ⊔ C = s8H V2 := by
  refine s8_complement h.coord1 h.V1_le_H h.normal1 α (fun a => h.alpha_surj_H a) ?_ h.act1
  intro x hx hax
  have hb : β x = 1 := by
    have := h.H_le_cent hx
    rw [h.cent_V2] at this; exact MonoidHom.mem_ker.mp this
  have : x ∈ s8H V2 ⊓ (V1 ⊔ V2) := ⟨hx, h.ker x hax hb⟩
  rwa [h.H_inf_V] at this

end S8Data

end CFSG.OddStandard.SmallF3.Omega
