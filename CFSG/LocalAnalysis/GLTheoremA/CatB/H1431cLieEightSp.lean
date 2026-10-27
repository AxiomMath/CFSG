module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.RankThree.PartTwo.Sec4.Census (TripleCoverLieIndex)

theorem lieSEightNoAt_B2 (hLO : LieOrderBridge) : LieSEightNoAt fun d => ∃ q, d = .B 2 q := by
  rintro Y _ _ - - - ⟨d, hv⟩ ⟨q, rfl⟩ - hf ⟨e⟩ α - - hα1
  have hq8 : q.card = 8 := hf
  refine lieSEight_false_of_card_le hLO hα1 ?_
  rw [hLO ⟨_, hv⟩ (Y ⧸ Subgroup.center Y) ⟨e⟩]
  show orderBC 2 q.card ≤ 1056706560
  rw [hq8]
  decide +kernel

theorem lieSEightAt_B_of_four (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge)
    (h4 : LieSEightAt fun d => ∃ q, d = .B 4 q) : LieSEightAt fun d => ∃ n q, d = .B n q := by
  rintro Y _ _ hY hcore hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq8 : q.card = 8 := hf
  have hp2 : q.p = 2 := (TauCeti.LieTypeIndex.characteristic_B n q).symm.trans hc
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
  · exact lieSEightAt_of_noAt (lieSEightNoAt_B2 hLO) Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he ξ h3
      h1 hin J hJ hT hτ
  · exact hq8
  · exact h4 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he ξ h3 h1 hin J hJ hT hτ
  · obtain ⟨e⟩ := he
    exact (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.B n q, hv⟩) (fun h => by
      simp only [TripleCoverLieIndex] at h
      omega) e (I1431C2.local81_B n q hv hp2 h5)).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
