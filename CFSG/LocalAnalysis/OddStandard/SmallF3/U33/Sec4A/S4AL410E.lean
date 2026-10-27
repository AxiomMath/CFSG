module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL410D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem false_of_tM_twelve (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) (h2 : 2 ∣ S.index) (hG2 : 2 ^ 11 ∣ Nat.card G)
    (htau : ∃ g : G, g * t * g⁻¹ = tau) (httau : ∃ g : G, g * t * g⁻¹ = t * tau)
    (htz : ∃ g : G, g * t * g⁻¹ = t * (x₁ * x₂) ^ 2) (𝒮 : Sylow 2 G)
    (h𝒮 : S < (𝒮 : Subgroup G)) {E : Subgroup G} (hE𝒮 : E ≤ (𝒮 : Subgroup G))
    (hEn : (E.subgroupOf (𝒮 : Subgroup G)).Normal) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEc : Nat.card E = 8) : False := by
  obtain ⟨hC, -, -⟩ := sylow_facts_of_l42 h h2 𝒮 h𝒮
  have htS : t ∈ S := by
    have := h.center_ge (Subgroup.subset_closure (by simp) : t ∈ closure {t, (x₁ * x₂) ^ 2})
    exact this.1
  have hno : ∀ g : G, ∀ e ∈ E, g * t * g⁻¹ ≠ e := by
    intro g e he hge
    refine false_of_mem_normal_E8 hE𝒮 hEn hEc hG2 he ?_
    intro Q hQ hQc
    rw [← hge] at hQc
    exact card_le_of_isPGroup_le_centralizer_conj (S := S) (t := t) h.toCtx0.le_invCent
      h.toCtx0.isPGroup h.toCtx0.relIndex_odd (card_S_of h h43) g hQ hQc
  by_cases hES : E ≤ S
  ·
    have hEnS : NormalIn E S := by
      refine ⟨hES, fun s hs k hk => ?_⟩
      have hs𝒮 : s ∈ (𝒮 : Subgroup G) := h𝒮.le hs
      have hk𝒮 : k ∈ (𝒮 : Subgroup G) := hE𝒮 hk
      have hkmem : (⟨k, hk𝒮⟩ : ↥(𝒮 : Subgroup G)) ∈ E.subgroupOf (𝒮 : Subgroup G) := hk
      exact hEn.conj_mem _ hkmem ⟨s, hs𝒮⟩
    obtain ⟨g, c, hcE, hgc⟩ := exists_mem_tG_of_normal_E8 h h43 h44 htau httau hEnS hEe hEc
    exact hno g c hcE hgc
  · have hCE : 4 ≤ Nat.card ↥(E ⊓ invCent t) :=
      four_le_card_inf_centralizer hE𝒮 hEn hEe hEc (h𝒮.le htS) (t_mul_self h.hyp)
    have hEF : E ⊓ S = fourGrp x₁ x₂ :=
      inf_S_eq_fourGrp_of h h43 h44 h2 h𝒮.le hC hE𝒮 hEn hEe hEc hno hES hCE
    obtain ⟨u, hu, hucent⟩ :=
      exists_u_centralizes_E h h43 h44 h𝒮.le hC hE𝒮 hEn hEe hEc hES hEF
    obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, g₀ * t * g₀⁻¹ = u := by
      rcases hu with rfl | rfl
      · exact htau
      · exact httau
    let f : G →* G := (MulAut.conj g₀⁻¹).toMonoidHom
    have hf : ∀ x, f x = g₀⁻¹ * x * g₀ := by
      intro x
      simp [f, MulAut.conj_apply]
    have hE'H : E.map f ≤ invCent t := by
      rintro _ ⟨e, he, rfl⟩
      rw [mem_invCent_iff, hf]
      have hue := hucent e he
      have h1 : g₀ * t * g₀⁻¹ * e = e * (g₀ * t * g₀⁻¹) := by
        rw [hg₀]
        calc u * e = (u * e * u⁻¹) * u := by group
          _ = e * u := by rw [hue]
      calc g₀⁻¹ * e * g₀ * t = g₀⁻¹ * (e * (g₀ * t * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * (g₀ * t * g₀⁻¹ * e) * g₀ := by rw [h1]
        _ = t * (g₀⁻¹ * e * g₀) := by group
    have hE'e : CFSG.Open.IsElemAbelian 2 (E.map f) := hEe.map f
    have hE'c : Nat.card (E.map f) = 8 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective, hEc]
    have hno' : ∀ g : G, ∀ e ∈ E.map f, g * t * g⁻¹ ≠ e := by
      rintro g _ ⟨e, he, rfl⟩ hge
      rw [hf] at hge
      apply hno (g₀ * g) e he
      calc g₀ * g * t * (g₀ * g)⁻¹ = g₀ * (g * t * g⁻¹) * g₀⁻¹ := by group
        _ = g₀ * (g₀⁻¹ * e * g₀) * g₀⁻¹ := by rw [hge]
        _ = e := by group
    exact false_of_E8_avoiding_tG h h43 h44 htau httau htz hE'H hE'e hE'c hno'

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
