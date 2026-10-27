module

public import CFSG.GH74.GLS.Stage2.Final.Sporadic
public import CFSG.GH74.GLS.Stage2.Final.ClassicalTop
public import CFSG.GH74.GLS.Stage1.Main.Assembly

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Main

theorem s_stage2Four_Std_of_stage1 (hno : S_noTwoAnNineTen) (hcl : ClassicalData) (h1 : Stage1OutFour)
    (hmain : Stage2Main) : S_stage2Four_Std := by
  intro G _ _ hStd h4 hT
  obtain ⟨z, S, k, hk, -, -, hout⟩ := h1 G hStd.toStd0 h4 hT
  have hctx := hout.ctxStd hStd
  have hs2 := hmain G z k S hctx
  rcases hk with hk | ⟨ε, hk⟩ | hk | hk
  · exact Or.inr (stageFiveClassical_of_stage1Out hcl hStd (Or.inl hk) hout hs2)
  · exact Or.inr (stageFiveClassical_of_stage1Out hcl hStd (Or.inr ⟨ε, hk⟩) hout hs2)
  · exact Or.inl (mcLLyData_of_stage2 hno (Or.inl hk) hctx
      (hs2.oddCore (fun ε h' => by rw [hk] at h'; cases h')))
  · exact Or.inl (mcLLyData_of_stage2 hno (Or.inr hk) hctx
      (hs2.oddCore (fun ε h' => by rw [hk] at h'; cases h')))

end CFSG.GH74.GLS.Stage2.Final
