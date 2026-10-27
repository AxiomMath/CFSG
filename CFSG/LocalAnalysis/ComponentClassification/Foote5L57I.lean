module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L56L

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_of_card_four {X F : Subgroup G} (hFX : F ≤ X) (hF2 : ∀ x ∈ F, x * x = 1)
    (hF4 : Nat.card F = 4) : 2 ≤ CFSG.pRank 2 ↥X := by
  have hF : CFSG.Open.IsElemAbelian 2 (F.subgroupOf X) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact commute_of_sq_eq_one hF2 a.2 b.2
    · rw [SubgroupClass.coe_pow, OneMemClass.coe_one, sq]
      exact hF2 _ ha
  have hFcard : Nat.card (F.subgroupOf X) = 2 ^ 2 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hFX).symm.toEquiv, hF4]
    norm_num
  have h3 := SectionRank.le_pRank one_lt_two (le_top : F.subgroupOf X ≤ ⊤) hF hFcard
  rw [← SectionRank.pRank_eq_open_pRank_top] at h3
  exact h3

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem footeF_conjugate_data (hQ4 : Nat.card Q = 4) (hQsq : ∀ q ∈ Q, q * q = 1) {s v : G}
    (hv : v ∈ conjugate Q s) (hv1 : v ≠ 1) :
    IsTwoComponentAt v (footeF L₀ v) ∧ footeF L₀ v ∈ footeFamilyOf L₀ ∧
      conjugate Q s ≤ coreActionKernel (footeF L₀ v) ∧
      IsSylowOf 2 (conjugate Q s) (coreActionKernel (footeF L₀ v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set w := s * v * s⁻¹ with hw
  have hwQ : w ∈ Q := mem_conjugate_iff.mp hv
  have hw1 : w ≠ 1 := fun h1 => hv1 (by
    calc v = s⁻¹ * w * s := by rw [hw]; group
      _ = 1 := by rw [h1]; group)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hQsq w hwQ) hw1
  obtain ⟨-, hLw, hLwF, -, -, -⟩ := h.footeF_data hwQ hw2
  have hvw : s⁻¹ * w * s = v := by rw [hw]; group
  have hF : footeF L₀ v = conjugate (footeF L₀ w) s := by
    rw [← footeF_conj h.sec4.huniq w s, hvw]
  have hL₁ : IsTwoComponentAt v (footeF L₀ v) := by
    have h1 := isTwoComponentAt_map_mulEquiv (MulAut.conj s⁻¹) hLw
    rw [MulAut.conj_apply, inv_inv, hvw] at h1
    rw [hF]
    exact h1
  have hL₁F : footeF L₀ v ∈ footeFamilyOf L₀ := by
    rw [hF]
    exact conjugate_mem_footeFamilyOf hLwF s
  have hQsC : conjugate Q s ≤ coreActionKernel (footeF L₀ v) := by
    intro x hx
    rw [hF]
    refine mem_coreActionKernel_conjugate ?_
    exact h.mem_coreActionKernel_footeF_of_commute hwQ hw2 (mem_conjugate_iff.mp hx)
      (commute_of_sq_eq_one hQsq hwQ (mem_conjugate_iff.mp hx))
  refine ⟨hL₁, hL₁F, hQsC, ?_⟩
  have hQs4 : Nat.card (conjugate Q s) = 4 := by rw [card_conjugate_eq_card, hQ4]
  have hrank : CFSG.pRank 2 ↥(coreActionKernel (footeF L₀ v)) = 2 :=
    le_antisymm (h.rankC _ hL₁F)
      (two_le_pRank_of_card_four hQsC (fun c hc => conjugate_sq_eq_one hQsq hc) hQs4)
  refine isSylowOf_of_twoPart_le ?_ hQsC ?_
  · exact IsPGroup.of_card (n := 2) (by rw [hQs4]; norm_num)
  · rw [card_conjugate_eq_card]
    exact h.maxQ _ hL₁F hrank

end Sec5

end CFSG.ComponentClassification.Foote5
