module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1U4Elt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem e1_u4 : E1Type FU4d := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, -, hlie⟩ := hF
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := Final.lieModel_psu_unpack hlie
  have hU : UnitaryFieldData r f F := ⟨hr, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Finite F := hU.finite
  have : CharP F r := hU.charP
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) hU
  have e' : Y ≃* hypPSU hU 2 0 := e.trans (hypPSUEquivStatedProj hU hR (by norm_num)).symm
  have hBT : LieType.BorelTits.Holds Y r := holds_of_lieModel hlie (by decide)
  have hBT' : LieType.BorelTits.Holds (hypPSU hU 2 0) r :=
    LieType.BorelTits.Holds.of_mulEquiv e' hBT
  have hstd : ∀ (d : ℕ) (_ : 1 ≤ d) (hd : d ≤ 2),
      RadFixPow (r := 2) (ε := 0) hU (by norm_num) hd := fun d hd1 hd => by
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    · exact radFixPow_u4_one hU hr2
    · exact radFixPow_u4_two hU hr2
  exact E1Core.of_mulEquiv e' (e1Core_hyp hr2 hU (by norm_num) (by norm_num) hstd hBT') b hb1 hbr
    hHH E hE hinv

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
