module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Cover
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.Vacuous
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup TauCeti
open CFSG.LocalAnalysis.RankThreeTheoremC (IsLinThreeCover3)

@[expose] def IsOpenIndex : LieTypeIndex → Prop
  | .A _ _ | .twistedA _ _ | .B _ _ | .C _ _ | .D _ _ | .twistedD _ _ | .G2 _ | .trialityD4 _
  | .reeF4 _ => True
  | _ => False

@[expose] def CentRankOpen : Prop :=
  ∀ d : ValidLieTypeIndex, d.1.characteristic ≠ 3 → ¬ IsLinThreeCover3 d → IsOpenIndex d.1 →
    CentRankAt d

section Dispatch


theorem centRankAt_of_open (hO : CentRankOpen) (d : ValidLieTypeIndex)
    (hch : d.1.characteristic ≠ 3) (hL3 : ¬ IsLinThreeCover3 d) : CentRankAt d := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q => exact hO _ hch hL3 trivial
  | twistedA r q => exact hO _ hch hL3 trivial
  | B r q => exact hO _ hch hL3 trivial
  | C r q => exact hO _ hch hL3 trivial
  | D r q => exact hO _ hch hL3 trivial
  | twistedD r q => exact hO _ hch hL3 trivial
  | G2 q => exact hO _ hch hL3 trivial
  | trialityD4 q => exact hO _ hch hL3 trivial
  | reeF4 k => exact hO _ hch hL3 trivial
  | E6 q => exact centRankAt_excBig (d := ⟨.E6 q, hv⟩) trivial
  | E7 q => exact centRankAt_excBig (d := ⟨.E7 q, hv⟩) trivial
  | E8 q => exact centRankAt_excBig (d := ⟨.E8 q, hv⟩) trivial
  | F4 q => exact centRankAt_excBig (d := ⟨.F4 q, hv⟩) trivial
  | twistedE6 q => exact centRankAt_excBig (d := ⟨.twistedE6 q, hv⟩) trivial
  | suzuki k => exact centRankAt_suzuki k hv
  | reeG2 k => exact absurd (LieTypeIndex.characteristic_reeG2 k) hch
  | tits => exact centRankAt_tits hv

end Dispatch

section Main


theorem t29ChevOther_of_inputs (hL3 : T29LThreeEpsCase) (hO : CentRankOpen) : T29ChevOther := by
  intro X _ _ L x h ⟨m, hch, ⟨e⟩⟩
  by_cases hZ : center ↥L = ⊥
  · by_cases hm : IsLinThreeCover3 m
    · refine concl_of_lThreeEps hL3 h (isLThreeEps_of_isLinThreeCover3 hm e) ?_
      rw [hZ, Subgroup.card_bot]
      exact one_dvd 3
    · exact (false_of_centRankAt h hZ e (centRankAt_of_open hO m hch hm)).elim
  · obtain ⟨hm, hc⟩ := isLinThreeCover3_of_center_ne_bot
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.AGLEmbedding.KFactProofs.CoverThree.coverE6RankFour h hZ hch e
    exact concl_of_lThreeEps hL3 h (isLThreeEps_of_isLinThreeCover3 hm e) (by rw [hc])

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
