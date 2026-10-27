module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Setup
public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)


theorem K372Setting.false_of_lie (hSR : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {X : Type} [Group X] [Finite X] {p : ℕ} {K E S : Subgroup X} (h : K372Setting X p K E S)
    (d : TauCeti.ValidLieTypeIndex) (hdp : d.1.characteristic ≠ p)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hnd : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) : False := by
  obtain ⟨e⟩ := hd
  apply h.seitzHyperGamma_ne_top
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hpd : p ≠ d.1.characteristic := fun h' => hdp h'.symm
  have hperf : commutator ↥K = ⊤ := Group.isPerfect_def.mp h.quasi.1
  have hE := h.isElemAbelian_autIm
  have hcard := h.card_autIm
  by_cases hz : p ∣ Nat.card (Subgroup.center ↥K)
  · have hci := QuasiHigh.coverIndex_of_dvd_card_center hGA h.prime hp2
      ⟨hperf, h.quasi.2.1⟩ d e hpd hz
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A m q =>
      exact QuasiHigh5.seitzHyperGamma_eq_top_linear h.prime hp2 hperf e (by simpa using hpd) hci
        (fun h3 => by omega) hE hcard
    | twistedA m q =>
      refine QuasiHigh5.seitzHyperGamma_eq_top_unitary h.prime hp2 hperf e (by simpa using hpd)
        hci hE hcard (Or.inl fun hx => ?_)
      rcases hx with ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega
    | E6 q => exact absurd hci.1 (by omega)
    | twistedE6 q => exact absurd hci.1 (by omega)
    | _ => exact False.elim hci
  · have : Fact p.Prime := ⟨h.prime⟩
    have hZ : Subgroup.center ↥K = ⊥ := by
      rcases h.isPGroup_center.card_eq_or_dvd with h1 | h1
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd h1 hz
    exact InputsSeitz3.seitzHyperGamma_eq_top_of_plane hSR h.prime hp2 hZ d e hpd hnd hE hcard

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
