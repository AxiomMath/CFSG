
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43F3Base

public section

namespace CFSG.KS.U43Mod.LieOdd

open CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

theorem u43OutCheck_of (hf : OutFacts) : u43OutCheck () = true := by
  simp only [u43OutCheck, Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hf.pos, hf.inv⟩, hf.dist⟩, hf.closed⟩, hf.wit⟩, ?_⟩
  rintro k₁ ⟨hk₁, h₁⟩ k₂ ⟨hk₂, h₂⟩
  exact hf.pairs k₁ hk₁ k₂ hk₂ h₁.1 (by simpa [memNA] using h₁.2) h₂.1
    (by simpa [memNA] using h₂.2)

end CFSG.KS.U43Mod.LieOdd

end
