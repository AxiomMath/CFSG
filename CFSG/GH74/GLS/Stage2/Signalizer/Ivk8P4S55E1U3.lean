module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1U3Alg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1BT
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1Types

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem e1_u3 : E1Type FU3d := by
  intro r Y _ _ hr hr2 hF b hb1 hbr hHH E hE hinv
  obtain ⟨f, hf, hlie⟩ := hF
  obtain ⟨F, iF, fF, hcard, ⟨e⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = (r ^ f) ^ 2 ∧ Nonempty (Y ≃* StatedProj (StatedSU 3 (r ^ f) F)) := by
    rcases hlie with ⟨-, -, K, iK, fK, hK, he⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · exact ⟨K, iK, fK, hK, he⟩
    all_goals exact absurd h0 (by norm_num)
  have hU : UnitaryFieldData r f F := ⟨hr, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Finite F := hU.finite
  have : CharP F r := hU.charP
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hU
  have e' : Y ≃* hypPSU hU 1 1 := e.trans (hypPSUEquivStatedProj hU hR (by norm_num)).symm
  have hBT : LieType.BorelTits.Holds Y r := holds_of_lieModel hlie (by decide)
  have hBT' : LieType.BorelTits.Holds (hypPSU hU 1 1) r :=
    LieType.BorelTits.Holds.of_mulEquiv e' hBT
  have hstd : ∀ (d : ℕ) (_ : 1 ≤ d) (hd : d ≤ 1),
      RadFixPow (r := 1) (ε := 1) hU (le_refl 1) hd := fun d hd1 hd => by
    obtain rfl : d = 1 := by omega
    exact radFixPow_u3 hr2 hU
  exact E1Core.of_mulEquiv e' (e1Core_hyp hr2 hU (le_refl 1) (le_refl 1) hstd hBT') b hb1 hbr
    hHH E hE hinv

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
