
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43AutBase

public section

namespace CFSG.KS.U43Mod.LieOdd

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut

theorem u43AutCheck_of (hf : AutFacts) : u43AutCheck () = true := by
  simp only [u43AutCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨hf.dinv, hf.sinv⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simpa only [List.all_eq_true] using hf.conjN
  · simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
    intro i hi j hj
    obtain ⟨hinv, hk⟩ := hf.cos i hi j hj
    refine ⟨hinv, fun k hk' l hl => ?_⟩
    rcases hk k hk' l hl with ⟨rfl, rfl⟩ | h
    · simp
    · simp [h]
  · simpa only [List.all_eq_true] using hf.cen
  · simpa using hf.bases
  · simp only [List.all_eq_true, List.mem_range]
    exact hf.trans

end CFSG.KS.U43Mod.LieOdd

end
