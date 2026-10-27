module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TriD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge lieOrderBridge_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem triD4NoOther_of_bridge (hB : LieOrderBridge) : TriD4NoOther := by
  intro S _ _ _ _ ⟨d, hv⟩ hd hc hf ⟨e⟩ _ _ _ _ _ _ _ _ J _ hT _
  exfalso
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  have hcard := hB ⟨d, hv⟩ S ⟨e⟩
  have hdvd : 174182400 ∣ Nat.card S := by
    rw [← CatDistinct.card_isD4two hB hT]
    exact (I1431C2.cl_card_psimple_dvd J).trans (Subgroup.card_subgroup_dvd_card J)
  rcases hd with ⟨n, q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | rfl
  · have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hs
    exact hr.2 ((TauCeti.LieTypeIndex.characteristic_C n q).symm.trans hc)
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    omega
  · have hq : q.card = 2 := hf
    have hS : Nat.card S = 211341312 := by
      rw [hcard]
      show orderTrialityD4 q.card = 211341312
      rw [hq]
      decide +kernel
    rw [hS] at hdvd
    exact absurd hdvd (by norm_num)
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [TauCeti.LieTypeIndex.characteristic_reeG2] at hc
    omega
  · simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hn : ¬ 174182400 ∣ lieOrderFormula TauCeti.LieTypeIndex.tits := by decide +kernel
    rw [hcard] at hdvd
    exact hn hdvd

theorem triD4NoOther_holds :
    TriD4NoOther :=
  triD4NoOther_of_bridge lieOrderBridge_holds

end CFSG.LocalAnalysis.GLTheoremA.TriD4

end
