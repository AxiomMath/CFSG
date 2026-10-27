module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

namespace TwoRu

@[expose] def FourthPowerDichotomy (L : Type*) [Group L] (z : L) : Prop :=
  (∀ u : L, u ^ 4 ≠ z) ∧ ∀ x : L, x ^ 2 = 1 → x ≠ 1 → x ≠ z → ∃ w : L, w ^ 4 = x

end TwoRu

open TwoRu

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem StdHyp.false_of_fourthPowerDichotomy (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h2 : Nat.card (center L) = 2)
    (hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q)
    (hfac : ∀ z : L, z ∈ center L → z ≠ 1 → FourthPowerDichotomy L z) : False := by
  have := h.simple
  obtain ⟨z, hz2, hZz, -, hCz⟩ := h.exists_standard_form_of_inner hS h2 hinn
  obtain ⟨g, hgz, hcomm⟩ := exists_fused_commuting_involution h.nonabelian hz2
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  obtain ⟨zL, hzLc, hzL⟩ : z ∈ (center L).map L.subtype := hZz ▸ mem_zpowers z
  have hzL' : (zL : G) = z := hzL
  have hzLne : zL ≠ 1 := fun h1 => hz1 (by rw [← hzL', h1]; rfl)
  obtain ⟨hfour, hinv⟩ := hfac zL hzLc hzLne
  have hz2' : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hmemL : ∀ y : G, y * z = z * y → y ∈ L := fun y hy => by
    rw [← hCz]
    exact mem_centralizer_singleton_iff.2 hy
  have hxL : g * z * g⁻¹ ∈ L := hmemL _ hcomm
  have hx2 : (⟨g * z * g⁻¹, hxL⟩ : L) ^ 2 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, conj_pow, hz2', OneMemClass.coe_one]; group)
  have hx1 : (⟨g * z * g⁻¹, hxL⟩ : L) ≠ 1 := fun h1 => hz1 (by
    have := congrArg Subtype.val h1
    simpa using this)
  have hxz : (⟨g * z * g⁻¹, hxL⟩ : L) ≠ zL := fun h1 => hgz (by
    have := congrArg Subtype.val h1
    rwa [hzL'] at this)
  obtain ⟨w, hw⟩ := hinv _ hx2 hx1 hxz
  have hu : (g⁻¹ * (w : G) * g) ^ 4 = z := by
    have := congrArg Subtype.val hw
    rw [SubgroupClass.coe_pow] at this
    rw [show g⁻¹ * (w : G) * g = g⁻¹ * (w : G) * g⁻¹⁻¹ by rw [inv_inv], conj_pow, this]
    group
  have huL : g⁻¹ * (w : G) * g ∈ L := hmemL _ (by
    have hc : Commute (g⁻¹ * (w : G) * g) ((g⁻¹ * (w : G) * g) ^ 4) := (Commute.refl _).pow_right 4
    rw [hu] at hc
    exact hc.eq)
  exact hfour ⟨_, huL⟩ (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hu.trans hzL'.symm))

end CFSG.EvenSporadicStandard
