module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentLevel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVBruhat

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem oddDerivE7VFrame_orth :
    oddDerivE7VFrame.Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel

theorem vPsi_eq_append : E7Pilot.vPsi = oddDerivE7VFrame ++ (E7Pilot.vLow ++ E7Pilot.vHigh) := by
  rw [E7Pilot.vPsi, E7Pilot.vFrame, List.append_assoc]

theorem e7FrameElt_conj_wordV
    [CharP K 2] (d : K) :
    e7WeylRep K ((coxeterSystem .E7).wordProd e7WordV) * e7FrameElt K oddDerivE7VFrame d *
        (e7WeylRep K ((coxeterSystem .E7).wordProd e7WordV))⁻¹ = e7FrameElt K e7FrameV d := by
  rw [e7FrameElt_conj_word e7WordV (fun σ hσ => (E7Pilot.pos_of_mem_vPsi
    (by rw [E7Pilot.vPsi, E7Pilot.vFrame]; simp_all)).1), e7WordV_map]

section Certs


theorem commute_e7FrameLine_vAS [CharP K 2] :
    ∀ z ∈ e7FrameLine K oddDerivE7VFrame, ∀ g ∈ Exc.cent (e7FramePt K oddDerivE7VFrame),
      z * g = g * z := by
  have hlev : ∀ j ∈ E7Pilot.vNodes, E7Pilot.vLevel (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = 0 := by
    intro j hj
    simp only [E7Pilot.vNodes, Set.mem_ofPred_eq] at hj
    simp only [E7Pilot.vLevel]
    rw [Pi.single_eq_of_ne (Ne.symm hj.1), Pi.single_eq_of_ne (Ne.symm hj.2), add_zero]
  refine commute_e7FrameLine_of_le_parabolic (J := E7Pilot.vNodes)
    (l' := E7Pilot.vLow ++ E7Pilot.vHigh) ?_ ?_ ?_ oddDerivE7VFrame_orth ?_ ?_ ?_
  · rw [← vPsi_eq_append]
    exact E7Pilot.vPsi_nodup
  · rw [← vPsi_eq_append]
    exact fun β hβ => E7Pilot.pos_of_mem_vPsi hβ
  · rw [← vPsi_eq_append]
    exact E7Pilot.vPsi_comm
  · intro α hα β hβ
    rw [← vPsi_eq_append] at hβ ⊢
    exact E7Pilot.conj_hyp_of_vLevel_nonneg (E7Pilot.vLevel_nonneg_of_pos hα.1) β hβ
  · intro j hj β hβ
    rw [← vPsi_eq_append] at hβ ⊢
    refine ⟨E7Pilot.conj_hyp_of_vLevel_nonneg (hlev j hj).ge β hβ,
      E7Pilot.conj_hyp_of_vLevel_nonneg ?_ β hβ⟩
    simp only [E7Pilot.vLevel_neg, hlev j hj, neg_zero, le_refl]
  · intro g hg
    have hg' : g ∈ centralizer ({E7Pilot.e7ASRep K 4} : Set (adjointGroup .E7 K)) := hg
    exact mem_subgroupOf.1 (E7Pilot.centralizer_e7ASRep_four_le_parabolic hg')

theorem commute_e7FrameLine_V [CharP K 2] :
    ∀ z ∈ e7FrameLine K e7FrameV, ∀ g ∈ Exc.cent (e7FramePt K e7FrameV), z * g = g * z :=
  commute_e7FrameLine_of_conj e7FrameElt_conj_wordV commute_e7FrameLine_vAS

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
