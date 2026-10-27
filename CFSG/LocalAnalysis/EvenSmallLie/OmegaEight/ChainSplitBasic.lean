module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1Setup

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type} [Group G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
include hS

theorem sp : SplitC.ShapeSplit t L H₀ := hS.inputs.setting.shape

theorem L_le_H₀ : L ≤ H₀ := hS.sp.L_le

theorem S₀_le_K : U ⊔ zpowers x₀ ≤ P ⊔ zpowers x₀ := sup_le_sup_right hS.rad.U_le_P _

theorem S₀_le_H₀ : U ⊔ zpowers x₀ ≤ H₀ := hS.S₀_le_K.trans hS.K_le_H₀

theorem pgroup_S₀ : IsPGroup 2 (U ⊔ zpowers x₀ : Subgroup G) := hS.inputs.setting.data.pgroup

theorem sylow_TH : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V →
    U ⊔ zpowers x₀ ⊔ zpowers t ≤ V → V = U ⊔ zpowers x₀ ⊔ zpowers t :=
  hS.inputs.setting.data.sylow

theorem commute_of_mem_H₀ {x : G} (hx : x ∈ H₀) : x * t = t * x := hS.sp.commute_of_mem hx

theorem commute_of_mem_K {x : G} (hx : x ∈ P ⊔ zpowers x₀) : x * t = t * x :=
  hS.commute_of_mem_H₀ (hS.K_le_H₀ hx)

theorem t_not_mem_H₀ : t ∉ H₀ := hS.sp.not_mem

theorem mem_Q_of_mem_H₀ {x : G} (hx : x ∈ H₀) (hc : ∀ q ∈ Q, x * q = q * x) : x ∈ Q := by
  have h : x ∈ Q ⊔ zpowers t := by
    rw [← hS.shape.centralizer_eq]
    exact ⟨mem_centralizer_singleton_iff.2 (hS.commute_of_mem_H₀ hx),
      mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩
  obtain ⟨q, hq, h1 | h1⟩ := (hS.shape.mem_sup_iff hS.rad.Q_le_L).1 h
  · exact h1 ▸ hq
  · exfalso
    apply hS.t_not_mem_H₀
    have h2 : q⁻¹ * x ∈ H₀ := H₀.mul_mem (H₀.inv_mem (hS.L_le_H₀ (hS.rad.Q_le_L hq))) hx
    rwa [h1, ← mul_assoc, inv_mul_cancel, one_mul] at h2

theorem mem_supT_iff {X : Subgroup G} (hX : X ≤ H₀) {x : G} :
    x ∈ X ⊔ zpowers t ↔ ∃ y ∈ X, x = y ∨ x = y * t := hS.sp.mem_sup_iff hX

theorem commute_of_mem_TH {h : G} (hh : h ∈ U ⊔ zpowers x₀ ⊔ zpowers t) : h * t = t * h := by
  obtain ⟨y, hy, rfl | rfl⟩ := (hS.mem_supT_iff hS.S₀_le_H₀).1 hh
  · exact hS.commute_of_mem_H₀ (hS.S₀_le_H₀ hy)
  · have hc := hS.commute_of_mem_H₀ (hS.S₀_le_H₀ hy)
    calc y * t * t = t * y * t := by rw [hc]
      _ = t * (y * t) := mul_assoc _ _ _

theorem isPGroup_TH : IsPGroup 2 (U ⊔ zpowers x₀ ⊔ zpowers t : Subgroup G) :=
  hS.sp.isPGroup_sup hS.S₀_le_H₀ hS.pgroup_S₀

theorem TH_le_centralizer : U ⊔ zpowers x₀ ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
  sup_le (hS.S₀_le_K.trans hS.K_le_centralizer)
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))

theorem KT_le_centralizer : P ⊔ zpowers x₀ ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
  sup_le hS.K_le_centralizer (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))

theorem card_KT [Finite G] :
    Nat.card (P ⊔ zpowers x₀ ⊔ zpowers t : Subgroup G) =
      2 * Nat.card (P ⊔ zpowers x₀ : Subgroup G) :=
  hS.sp.card_sup hS.K_le_H₀

end CFSG.EvenSmallLie.OmegaEight.SplitIn.SetupX
