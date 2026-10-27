module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.RankThree.PartTwo.Sec4.Census (TripleCoverLieIndex)

theorem lieSTwoAt_B (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge) :
    LieSTwoAt fun d => ∃ n q, d = .B n q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α hα hα3 hα1
  have hq : q.card = 2 := hf
  obtain ⟨hp2, -⟩ := I1431C2.cl_primePower_card_two hq
  have hrange := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
  simp only [] at hr
  rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
  · haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hn := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
    have hcard : Nat.card (Y ⧸ Subgroup.center Y) = 1451520 := by
      rw [hLO ⟨_, hv⟩ _ ⟨e⟩]
      show orderBC 3 q.card = 1451520
      rw [hq]
      decide +kernel
    have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp2
      (le_refl 3) e
    have hinn := I1431C2.sp_mem_inner_of_statedModel hmodel hα hα3
    exact lieSTwo_of_no_pump hLO fun J hJ h4 =>
      lieSTwo_false_of_inner (I1431C2.cl_center_eq_bot_of_simple hn) hα3 hα1 hJ h4 hinn
        (by rw [hcard]; norm_num)
  · have hcard : Nat.card (Y ⧸ Subgroup.center Y) = 47377612800 := by
      rw [hLO ⟨_, hv⟩ _ ⟨e⟩]
      show orderBC 4 q.card = 47377612800
      rw [hq]
      decide +kernel
    exact ⟨fun _ => Or.inl hq, lieSTwo_not_sp48_of_not_dvd hLO (by rw [hcard]; norm_num)⟩
  · refine (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.B n q, hv⟩) ?_ e
      (I1431C2.local81_B n q hv hp2 h5)).elim
    intro h
    simp only [TripleCoverLieIndex] at h
    omega

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
