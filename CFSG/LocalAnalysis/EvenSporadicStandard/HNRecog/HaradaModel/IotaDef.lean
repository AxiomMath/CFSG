module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open CFSG.EvenSporadicStandard.HNRecog.HaradaLA

@[expose] noncomputable def uElem (i : ℕ) : ↥P1408 := ⟨elemW (uWords.getD i []), elemW_mem _⟩

@[expose] noncomputable def iotaFun (v : V6) : ↥P1408 :=
  uElem 0 ^ (v 0).val * uElem 1 ^ (v 1).val * uElem 2 ^ (v 2).val * uElem 3 ^ (v 3).val *
    uElem 4 ^ (v 4).val * uElem 5 ^ (v 5).val

@[expose] def vecOfCode (k : ℕ) : V6 := fun i => ((bitOf k i : ℕ) : ZMod 2)

@[expose] def codeOfVec (v : V6) : ℕ := ∑ i : Fin 6, (v i).val * 2 ^ (i : ℕ)

theorem codeOfVec_lt (v : V6) : codeOfVec v < 64 := by
  revert v
  decide +kernel

theorem vecOfCode_codeOfVec (v : V6) : vecOfCode (codeOfVec v) = v := by
  revert v
  decide +kernel

theorem lam_vecOfCode (k : ℕ) : lam (vecOfCode k) = (lamC k : ZMod 2) := rfl

theorem qm_vecOfCode (k : ℕ) : qm (vecOfCode k) = (qmC k : ZMod 2) := by
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  simp only [qm, vecOfCode, qmC, ZMod.natCast_mod]
  push_cast
  simp only [hsq]
  rfl

theorem typeIdx_codeOfVec_eq_iff (v w : V6) :
    typeIdx (codeOfVec v) = typeIdx (codeOfVec w) ↔ lam v = lam w ∧ qm v = qm w := by
  revert v w
  decide +kernel

theorem codeOfVec_tv : codeOfVec tv = 16 := by
  decide +kernel

theorem codeOfVec_zero : codeOfVec 0 = 0 := by
  decide +kernel

theorem codeOfVec_injective : Function.Injective codeOfVec :=
  Function.LeftInverse.injective vecOfCode_codeOfVec

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
