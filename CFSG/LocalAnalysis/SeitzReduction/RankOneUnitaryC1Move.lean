module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallChar

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates



theorem exists_move_of_inv_of_le_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hT : T ≤ szT₁ L T ⊔ zpowers t) :
    ∃ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G), ∃ r ∈ R₂, r ∉ szA₁ (szT₁ L T) ∧
      y * t * y⁻¹ = r * t := by
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hcyc : ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T := by
    refine ⟨t, htT, fun s hs => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ (hT hs)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    refine ⟨k, ?_⟩
    have hc : t ^ k * y = y * t ^ k :=
      (Commute.zpow_left (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy).symm k)
    rw [show (t ^ k)⁻¹ * (y * t ^ k) = (t ^ k)⁻¹ * (t ^ k * y) by rw [hc], inv_mul_cancel_left]
    exact hy
  have hnS := h.not_isSylow_S₁_of_isCyclic_of_card_sylow hS2 hR hcyc
  have hN := h.normalizer_le_of_forall_le_of_card_sylow hS2 hR fun B hB hBc hcard =>
    h.charInput_of_le_of_card_sylow hS2 hR hT hB hBc hcard
  exact h.exists_move_of_inv_of_not_isSylow hS2 hR hinv hnS hN

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
