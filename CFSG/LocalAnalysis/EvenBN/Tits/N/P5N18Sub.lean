module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5N18D
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5S25

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalAnalysis.EvenBN.Tits.N
  CFSG.LocalAnalysis.EvenBN.Tits.N.P4

section Transport

variable {Γ : Type*} [Group Γ] {H U : Subgroup Γ} {x v t : Γ}

theorem n18_isF20_subgroupOf (hUH : U ≤ H) (hxH : x ∈ H) (hvH : v ∈ H) (hF : IsF20 U x v) :
    IsF20 (U.subgroupOf H) (⟨x, hxH⟩ : ↥H) (⟨v, hvH⟩ : ↥H) where
  comm a ha b hb := Subtype.ext (hF.comm a ha b hb)
  sq a ha := Subtype.ext (hF.sq a ha)
  card := by
    rw [← hF.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv
  x_norm := (mem_normalizer_subgroupOf_iff_coe_mem hUH _).2 hF.x_norm
  v_norm := (mem_normalizer_subgroupOf_iff_coe_mem hUH _).2 hF.v_norm
  x5 := Subtype.ext hF.x5
  v4 := Subtype.ext hF.v4
  vx := by
    rcases hF.vx with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  fpf a ha h := Subtype.ext (hF.fpf a ha (congrArg Subtype.val h))

theorem n18_map_Pgrp (hUH : U ≤ H) (hxH : x ∈ H) (hvH : v ∈ H) :
    (IsF20.Pgrp (U.subgroupOf H) (⟨x, hxH⟩ : ↥H) (⟨v, hvH⟩ : ↥H)).map H.subtype =
      IsF20.Pgrp U x v := by
  unfold IsF20.Pgrp
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hUH,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

end Transport

section Main


theorem delta_surj_sub (hTop : TopStatement) {Γ : Type} [Group Γ] [Finite Γ] {H U : Subgroup Γ}
    {x v t : Γ} (rk : Γ → ℕ) (hUH : U ≤ H) (hxH : x ∈ H) (hvH : v ∈ H) (htH : t ∈ H)
    (hF : IsF20 U x v) (htt : t * t = 1) (htnU : t ∉ U)
    (hcomm : ∀ p ∈ IsF20.Pgrp U x v, t * p = p * t) (hinf : zpowers t ⊓ IsF20.Pgrp U x v = ⊥)
    (hCt : ∀ g ∈ H, g * t = t * g → g ∈ zpowers t ⊔ IsF20.Pgrp U x v)
    (hnotU : ∀ g ∈ H, g * t * g⁻¹ ∉ U) (h66 : ∃ u ∈ U, u ≠ 1 ∧ ∃ g ∈ H, g * t * g⁻¹ = t * u)
    (h67 : ∃ w g : Γ, w ∈ H ∧ g ∈ H ∧ w ∈ normalizer (U : Set Γ) ∧ w * t = t * w ∧
      w * x * w⁻¹ = x⁻¹ ∧ g * t * g⁻¹ = t * w)
    (hrk_conj : ∀ g ∈ H, ∀ y ∈ H, rk (g * y * g⁻¹) = rk y)
    (hrk3 : ∃ u ∈ U, u ≠ 1 ∧ rk u ≤ 8)
    (hrk4 : ∀ y ∈ H, ∀ g ∈ H, y * y = 1 → y * (g * x * g⁻¹) * y⁻¹ = (g * x * g⁻¹)⁻¹ →
      16 ≤ rk y) :
    ∀ u ∈ U, ∃ g ∈ H, g * t * g⁻¹ = t * u := by
  classical
  have hF' := n18_isF20_subgroupOf hUH hxH hvH hF
  have hmap := n18_map_Pgrp hUH hxH hvH
  have hmapC : (zpowers (⟨t, htH⟩ : ↥H) ⊔ IsF20.Pgrp (U.subgroupOf H) (⟨x, hxH⟩ : ↥H)
      (⟨v, hvH⟩ : ↥H)).map H.subtype = zpowers t ⊔ IsF20.Pgrp U x v := by
    rw [Subgroup.map_sup, hmap, MonoidHom.map_zpowers]
    rfl
  have hres := delta_surj hTop (X := ↥H) (U := U.subgroupOf H) (x := ⟨x, hxH⟩) (v := ⟨v, hvH⟩)
    (t := ⟨t, htH⟩) (fun y => rk y.1) hF' (Subtype.ext htt) (fun h => htnU h)
    (fun p hp => by
      have hp' : (p : Γ) ∈ IsF20.Pgrp U x v := by
        rw [← hmap]
        exact ⟨p, hp, rfl⟩
      exact Subtype.ext (hcomm p hp'))
    (by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
      have h1 : (y : Γ) ∈ zpowers t ⊓ IsF20.Pgrp U x v := by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h2 : (y : Γ) ∈ (zpowers (⟨t, htH⟩ : ↥H)).map H.subtype := ⟨y, hy1, rfl⟩
          rw [MonoidHom.map_zpowers] at h2
          exact h2
        · rw [← hmap]
          exact ⟨y, hy2, rfl⟩
      rw [hinf] at h1
      exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 h1)))
    (fun g hg => by
      have h1 := hCt g g.2 (congrArg Subtype.val hg)
      rw [← hmapC] at h1
      obtain ⟨s, hs, hsg⟩ := h1
      have hsg' : s = g := Subtype.ext hsg
      rw [← hsg']
      exact hs)
    (fun g hg => hnotU g g.2 hg)
    (by
      obtain ⟨u, hu, hu1, g, hg, hgt⟩ := h66
      exact ⟨⟨u, hUH hu⟩, hu, fun h => hu1 (congrArg Subtype.val h), ⟨g, hg⟩, Subtype.ext hgt⟩)
    (by
      obtain ⟨w, g, hwH, hgH, hwN, hwt, hwx, hgt⟩ := h67
      exact ⟨⟨w, hwH⟩, ⟨g, hgH⟩, (mem_normalizer_subgroupOf_iff_coe_mem hUH _).2 hwN,
        Subtype.ext hwt, Subtype.ext hwx, Subtype.ext hgt⟩)
    (fun g y => hrk_conj g.1 g.2 y.1 y.2)
    (by
      obtain ⟨u, hu, hu1, hr⟩ := hrk3
      exact ⟨⟨u, hUH hu⟩, hu, fun h => hu1 (congrArg Subtype.val h), hr⟩)
    (fun y g hy hyg => hrk4 y.1 y.2 g.1 g.2 (congrArg Subtype.val hy) (congrArg Subtype.val hyg))
  intro u hu
  obtain ⟨g, hg⟩ := hres ⟨u, hUH hu⟩ hu
  exact ⟨g.1, g.2, congrArg Subtype.val hg⟩

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
