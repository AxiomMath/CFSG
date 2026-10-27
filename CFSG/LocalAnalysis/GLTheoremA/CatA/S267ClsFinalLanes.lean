module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseOrthAt
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB

section D4


theorem badClsAt_D_four (hGA : GriessAllModelsStatement) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 Q).Valid) : BadClsAt ⟨.D 4 Q, hv⟩ := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hSn hperf hcore hchar he hB hSB hrank hB4 hBC hp3B hHq
  by_cases hp3 : p = 3
  · subst hp3
    haveI := hSn
    have hQq : Q.p = q := by rwa [TauCeti.LieTypeIndex.characteristic_D] at hchar
    exact concl_d4_three Q hv hq2 hqp hperf hcore hQq he hB hrank hB4 hBC
      (fun h => hp3B ⟨rfl, h⟩) hHq
  · exact badClsAt_D_four_of_ne_three hGA hv p q hp hp2 hp3 hq hq2 hqp Ω hK S B hSn hperf hcore
      hchar he hB hSB hrank hB4 hBC hp3B hHq

end D4

section Lanes


theorem s267FactBadCls_of_lanes
    (hA : GriessAllModelsStatement → ∀ {n : ℕ} {Q : TauCeti.PrimePower}
      (hv : (TauCeti.LieTypeIndex.A n Q).Valid), 2 ≤ n → BadClsAt ⟨.A n Q, hv⟩)
    (h2A : GriessAllModelsStatement → ∀ {n : ℕ} {Q : TauCeti.PrimePower}
      (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid), BadClsAt ⟨.twistedA n Q, hv⟩)
    (hcore : S267FactBadExcCore) : S267FactBadCls := by
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  refine s267FactBadCls_of_at hcore fun d hcl hA1 => ?_
  obtain ⟨d, hv⟩ := d
  cases d with
  | A n Q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by have := hr.1; omega
      exact absurd rfl (hA1 Q)
    · exact hA hGA hv h
  | twistedA n Q => exact h2A hGA hv
  | B n Q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases (show n = 2 ∨ 3 ≤ n by have := hr.1; omega) with rfl | hn
    · exact badClsAt_B_two Q hv
    · exact badClsAt_B hGA hv hn
  | C n Q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    exact badClsAt_C n Q hv hr.1
  | D n Q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases (show n = 4 ∨ 5 ≤ n by have := hr; omega) with rfl | hn
    · exact badClsAt_D_four hGA Q hv
    · exact badClsAt_D hGA hv hn
  | twistedD n Q => exact badClsAt_twistedD hGA hv
  | _ => exact absurd hcl (by simp [S267ClassicalIdx])

end Lanes

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
