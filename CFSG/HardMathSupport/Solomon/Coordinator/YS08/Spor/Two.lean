module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fusion
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Ru
public import CFSG.RankThree.PartTwo.KFacts.K426J3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier
  CFSG.EvenSporadicStandard.RuStd.S2

theorem noL3Eq_50232960 : NoL3Eq 50232960 :=
  noL3Eq_of_check (B := 40) (by norm_num) (by decide +kernel)

theorem noL3Eq_145926144000 : NoL3Eq 145926144000 :=
  noL3Eq_of_check (B := 40) (by norm_num) (by decide +kernel)

theorem sporL3DownInner_J3
    (hbr : SporadicBridges) : SporL3DownInner .J3 :=
  sporL3DownInner_of_fusion j3P ⟨j3PermEquiv.symm.trans (hbr .J3).some⟩
    (by rw [card_j3P]; exact noL3Eq_50232960)
    (fun c => c = j3tXA ∨ c = j3tXB)
    (fun c hc => by
      rcases hc with rfl | rfl
      · exact ⟨(j3tReps_spec (c := 0) (by norm_num)).2, by
          rw [← j3t_caseA.1, j3t_caseA.2]; norm_num⟩
      · exact ⟨(j3tReps_spec (c := 1) (by norm_num)).2, by
          rw [← j3t_caseB.1, j3t_caseB.2]; norm_num⟩)
    (fun x hx hxo => j3t_fusion hx hxo)

theorem sporL3DownInner_Ru
    (hbr : SporadicBridges) : SporL3DownInner .Ru := by
  haveI : Finite ruP := Nat.finite_of_card_ne_zero (by
    rw [card_ruP']; norm_num)
  refine sporL3DownInner_of_model _ ⟨ruEquivP.symm.trans (hbr .Ru).some⟩
    (by rw [card_ruP']; exact noL3Eq_145926144000) ?_
  intro x hx
  obtain ⟨c, hc⟩ := exists_conj_ruThree x hx
  rw [← centralizer_singleton_eq_of_zpowers_eq hc, ← MulAut.conj_apply,
    ← map_centralizer_mulEquiv (MulAut.conj c) ruThreeX0,
    Subgroup.card_map_of_injective (MulAut.conj c).injective,
    card_centralizer_ruThreeX0]
  norm_num

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
