module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.SuzukiReeTits
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSuzuki
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeG2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4Big
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTTits

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

section P3

set_option linter.unusedSectionVars false


theorem reeG2Char3Export_of_lieQ (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3) :
    ReeG2Char3Export := by
  intro S _ _ hs hna idx hF h3 he β hβ hβ1
  haveI := hs
  obtain ⟨d, hv⟩ := idx
  cases d with
  | reeG2 m =>
    by_cases hin : ∃ t : S, MulAut.conj t = β
    · obtain ⟨t, rfl⟩ := hin
      obtain ⟨x, hx, hx3, hx1⟩ :=
        CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range
          (b3Lie_center_eq_bot hna) ⟨t, rfl⟩ hβ hβ1
      have hS : IsChevOfChar 3 S :=
        ⟨⟨.reeG2 m, hv⟩, YS08.isChevIndexOfChar_of_lieIndexChar_eq rfl, he⟩
      rw [hx]
      exact Or.inr (noThreeComponents_of_conj hQ hs hna hS hx1 hx3)
    · exact Or.inl ((srtOut_reeG2_outer m hv he Nat.prime_three (by norm_num) hβ
        (fun t h => hin ⟨t, h⟩)).full hb)
  | suzuki m => exact absurd h3 (by simp [lieIndexChar])
  | reeF4 m => exact absurd h3 (by simp [lieIndexChar])
  | tits => exact absurd h3 (by simp [lieIndexChar])
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end P3

section P5

set_option linter.unusedSectionVars false


theorem lieCompsOn_suzukiReeTits {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    LieCompsOn p .suzukiReeTits := by
  intro S _ _ hs hna idx hF he β hβ hβ1 _
  haveI := hs
  obtain ⟨d, hv⟩ := idx
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  cases d with
  | suzuki m => exact (srtOut_suzuki m hv he hp hp2 hβ hβ1).comps
  | reeG2 m => exact (srtOut_reeG2 m hv he hp hp2 hp3 hβ hβ1).comps
  | reeF4 m => exact (srtOut_reeF4 m hv he hp (by omega) hβ hβ1).comps
  | tits => exact (srtOut_tits hv hna he hp hp2 hβ hβ1).comps
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end P5

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
