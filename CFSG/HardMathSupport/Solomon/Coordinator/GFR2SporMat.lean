module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporRed
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

theorem card_bound_of_model {G : Type*} [Group G] [Finite G] (P : Subgroup G) {S : Type*} [Group S]
    (ψ : ↥P ≃* S) (N : ℕ)
    (h : ∀ x ∈ P, orderOf x = 3 → Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ P) ≤ N) :
    ∀ s : S, orderOf s = 3 → Nat.card ↥(Subgroup.centralizer ({s} : Set S)) ≤ N := by
  intro s hs
  have hs' : orderOf (ψ.symm s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
  have h1 := h (ψ.symm s) (ψ.symm s).2 (by rw [Subgroup.orderOf_coe]; exact hs')
  rw [← map_centralizer_subtype P (ψ.symm s),
    Subgroup.card_map_of_injective P.subtype_injective] at h1
  have h2 := map_centralizer_mulEquiv ψ (ψ.symm s)
  rw [MulEquiv.apply_symm_apply] at h2
  rw [← h2, Subgroup.card_map_of_injective ψ.injective] at *
  exact h1

theorem sporNoPumpup_M12 (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    SporNoPumpup .M12 := by
  refine sporNoPumpup_of_card_bound hSpM hOG hOut 54 (by norm_num) ?_
  refine card_bound_of_model NativeSporadic.M12 (hbr .M12).some 54 ?_
  intro x hx hx3
  obtain ⟨c, hc, hcard⟩ := check_card_sound m12S3Data rep_m12A rep_m12B
    Certificates.certificate13511.2.1 x hx hx3
  have : ∀ c < m12S3Data.cases.size, m12S3Data.cases[c]!.card ≤ 54 := by decide +kernel
  exact (le_of_eq hcard).trans (this c hc)

theorem sporNoPumpup_M22 (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    SporNoPumpup .M22 := by
  refine sporNoPumpup_of_card_bound hSpM hOG hOut 54 (by norm_num) ?_
  refine card_bound_of_model NativeSporadic.M22 (hbr .M22).some 54 ?_
  intro x hx hx3
  obtain ⟨c, hc, hcard⟩ := check_card_sound m22S3Data rep_m22A rep_m22B
    Certificates.certificate13511.2.2.1 x hx hx3
  have : ∀ c < m22S3Data.cases.size, m22S3Data.cases[c]!.card ≤ 54 := by decide +kernel
  exact (le_of_eq hcard).trans (this c hc)

end CFSG.HardMathSupport.Solomon.Coordinator
