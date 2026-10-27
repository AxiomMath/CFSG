module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidU4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM123
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitaryLevi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUSym

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

theorem rigidLeviChoice_unitary : RigidLeviChoiceFor .unitary := by
  intro G _ _ A D hD hA hZ hq p hp
  cases D with
  | unitary n f hn hf K hK e =>
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    have hf2 : 2 ≤ f := by
      have hq' : 2 ^ 2 ≤ 2 ^ f := hq
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hq'
    have hk : 2 ≤ k := by omega
    have : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hK
    have h := unitaryFieldData_of_card hK hf
    have hp' : IsInvolutionOfRank e p 1 := hp
    obtain ⟨θ, hker, hθ, hα, hpA, c, Mp, hc0, hc, hMp, hθp⟩ := exists_uLeviTheta_spec hk h e hp'
    obtain ⟨hpo, M, ⟨hpA', hMH, he⟩, hM2, hr⟩ := hp'
    have hp2 : p ^ 2 = 1 := by rw [← hpo, pow_orderOf_eq_one]
    obtain ⟨hS, hconj, hcen⟩ := URigid.unitary_m123 h hf2 hk (M := M) hMH hM2 hr
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    ·
      have hchoice := leviChoice_unitary_of hn hf hK e hZ hf2 hker hθ hα le_sup_right
        (sup_le (liftSub_mono uBarT_le_centralizer_uBarL)
          (levLift_le_liftSub.trans (liftSub_mono uBarW_le_centralizer_uBarL)))
        (noInv_u_two hA.1 hker hθ hK hf2)
        (fun _ σ _ hfix => outerFree_u_two hker hθ hK hf2 σ hfix)
        (fun hL4 => by
          have h' : 2 + 2 = 4 ∧ f = 2 := hL4
          obtain rfl : f = 2 := h'.2
          exact sym_u_four hA.1 hker hθ hZ hK)
      refine ⟨uLeviW θ, liftSub θ (uBarT K f) ⊔ uLeviW θ, hchoice, ?_⟩
      exact leviRigid_of_model e hZ hpA' hp2 hMH he hM2 hS hconj hcen
        (hchoice.Y_le.trans inf_le_right)
        (URigid.rigidCore_unitary_four h hf2 hker hθ hZ hpA hp2 hc0 hc hMp hθp)
    ·
      have hchoice := leviChoice_unitary_of hn hf hK e hZ hf2 hker hθ hα le_rfl
        (levLift_le_liftSub.trans (liftSub_mono uBarW_le_centralizer_uBarL))
        (noInv_u_of_three_le hA.1 hker hθ hK hf2 hk3)
        (fun h4 => by
          have h' : 2 + k = 4 ∧ f = 2 := h4
          omega)
        (fun h4 => by
          have h' : 2 + k = 4 ∧ f = 2 := h4
          omega)
      refine ⟨uLeviW θ, uLeviW θ, hchoice, ?_⟩
      exact leviRigid_of_model e hZ hpA' hp2 hMH he hM2 hS hconj hcen
        (hchoice.Y_le.trans inf_le_right)
        (URigid.rigidCore_unitary h hf2 hk3 hker hθ hZ hpA hp2 hc0 hc hMp hθp)
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
