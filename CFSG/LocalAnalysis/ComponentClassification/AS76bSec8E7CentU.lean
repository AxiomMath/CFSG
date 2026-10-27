module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentLevel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUBruhat

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem oddDerivE7UFrame_orth :
    oddDerivE7UFrame.Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel

theorem uPsi_eq_append : E7Pilot.uPsi = oddDerivE7UFrame ++ (E7Pilot.uLow ++ E7Pilot.uHigh) := by
  rw [E7Pilot.uPsi, E7Pilot.uFrame, List.append_assoc]

theorem e7FrameElt_conj_wordU
    [CharP K 2] (d : K) :
    e7WeylRep K ((coxeterSystem .E7).wordProd e7WordU) * e7FrameElt K oddDerivE7UFrame d *
        (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordU))⁻¹ = e7FrameElt K e7FrameU d := by
  rw [e7FrameElt_conj_word e7WordU (fun σ hσ => (E7Pilot.pos_of_mem_uPsi
    (by rw [E7Pilot.uPsi, E7Pilot.uFrame]; simp_all)).1), e7WordU_map]

section Certs


theorem commute_e7FrameLine_uAS [CharP K 2] :
    ∀ z ∈ e7FrameLine K oddDerivE7UFrame, ∀ g ∈ Exc.cent (e7FramePt K oddDerivE7UFrame),
      z * g = g * z := by
  have hlev : ∀ j ∈ E7Pilot.uNodes, E7Pilot.uLevel (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = 0 := by
    intro j hj
    simp only [E7Pilot.uNodes, Set.mem_ofPred_eq] at hj
    simp only [E7Pilot.uLevel]
    rw [Pi.single_eq_of_ne (Ne.symm hj)]
  refine commute_e7FrameLine_of_le_parabolic (J := E7Pilot.uNodes)
    (l' := E7Pilot.uLow ++ E7Pilot.uHigh) ?_ ?_ ?_ oddDerivE7UFrame_orth ?_ ?_ ?_
  · rw [← uPsi_eq_append]
    exact E7Pilot.uPsi_nodup
  · rw [← uPsi_eq_append]
    exact fun β hβ => E7Pilot.pos_of_mem_uPsi hβ
  · rw [← uPsi_eq_append]
    exact E7Pilot.uPsi_comm
  · intro α hα β hβ
    rw [← uPsi_eq_append] at hβ ⊢
    exact E7Pilot.conj_hyp_of_uLevel_nonneg (E7Pilot.uLevel_nonneg_of_pos hα.1) β hβ
  · intro j hj β hβ
    rw [← uPsi_eq_append] at hβ ⊢
    refine ⟨E7Pilot.conj_hyp_of_uLevel_nonneg (hlev j hj).ge β hβ,
      E7Pilot.conj_hyp_of_uLevel_nonneg ?_ β hβ⟩
    simp only [E7Pilot.uLevel_neg, hlev j hj, neg_zero, le_refl]
  · intro g hg
    have hg' : g ∈ centralizer ({E7Pilot.e7ASRep K 3} : Set (adjointGroup .E7 K)) := hg
    exact mem_subgroupOf.1 (E7Pilot.centralizer_e7ASRep_three_le_parabolic hg')

theorem commute_e7FrameLine_U [CharP K 2] :
    ∀ z ∈ e7FrameLine K e7FrameU, ∀ g ∈ Exc.cent (e7FramePt K e7FrameU), z * g = g * z :=
  commute_e7FrameLine_of_conj e7FrameElt_conj_wordU commute_e7FrameLine_uAS

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
