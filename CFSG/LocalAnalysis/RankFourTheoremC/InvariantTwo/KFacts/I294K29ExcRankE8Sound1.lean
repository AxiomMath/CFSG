module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.PrimeChar
public meta import CFSG.Blueprint.ChevalleyRootsInputs
public meta import CFSG.Blueprint.Chevalley

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.ExcRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg

section Linear

variable {τ : Tag} {p : ℕ}

theorem pReflect_add (i : Fin τ.rank) (a b : Fin τ.rank → ZMod p) :
    pReflect i (a + b) = pReflect i a + pReflect i b := by
  funext j
  simp only [pReflect, Pi.add_apply]
  ring

theorem pReflect_smul (i : Fin τ.rank) (c : ZMod p) (a : Fin τ.rank → ZMod p) :
    pReflect i (c • a) = c • pReflect i a := by
  funext j
  simp only [pReflect, Pi.smul_apply, smul_eq_mul]
  ring

theorem pAct_add (ω : List (Fin τ.rank)) (a b : Fin τ.rank → ZMod p) :
    pAct ω (a + b) = pAct ω a + pAct ω b := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    show pReflect i (pAct ω (a + b)) = pReflect i (pAct ω a) + pReflect i (pAct ω b)
    rw [ih, pReflect_add]

theorem pAct_smul (ω : List (Fin τ.rank)) (c : ZMod p) (a : Fin τ.rank → ZMod p) :
    pAct ω (c • a) = c • pAct ω a := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    show pReflect i (pAct ω (c • a)) = c • pReflect i (pAct ω a)
    rw [ih, pReflect_smul]

theorem pAct_zero (ω : List (Fin τ.rank)) : pAct ω (0 : Fin τ.rank → ZMod p) = 0 := by
  have h := pAct_smul ω (0 : ZMod p) (0 : Fin τ.rank → ZMod p)
  simpa using h

theorem pPairing_smul_left (c : ZMod p) (a : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    pPairing (c • a) v = c * pPairing a v := by
  simp only [pPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pPairing_single (b : Fin τ.rank → ZMod p) (j : Fin τ.rank) :
    pPairing b (Pi.single j 1) = b j := by
  have h := pPairing_zsmul_single b 1 j
  rwa [one_smul, Int.cast_one, mul_one] at h

end Linear

section Weyl

variable {τ : Tag} {p : ℕ}

theorem pPairing_pAct (ω : List (Fin τ.rank)) (b : Fin τ.rank → ZMod p) (v : Fin τ.rank → ℤ) :
    pPairing (pAct ω b) v = pPairing b (((coxeterSystem τ).wordProd ω)⁻¹ • v) := by
  have h := pChar_pAct ω b v
  rw [pChar_apply, pChar_apply] at h
  exact Zp.ofAdd_eq_ofAdd_iff.1 h

theorem pPairing_of_pAct (ω : List (Fin τ.rank)) (z : Fin τ.rank → ZMod p) (q : ZMod p)
    (h : pAct ω z = q • z) (v : Fin τ.rank → ℤ) :
    pPairing z ((((coxeterSystem τ).wordProd ω)⁻¹) • v) = q * pPairing z v := by
  rw [← pPairing_pAct, h, pPairing_smul_left]

theorem exists_word_of_premise (x : Fin τ.rank → ZMod p) (q : ZMod p) (w : WeylGroup τ)
    (h : ∀ v, pPairing x (w • v) = q * pPairing x v) :
    ∃ ω : List (Fin τ.rank), pAct ω x = q • x := by
  obtain ⟨ω₀, -, rfl⟩ := (coxeterSystem τ).exists_reduced_word w
  refine ⟨ω₀.reverse, funext fun j => ?_⟩
  have h1 := pPairing_pAct ω₀.reverse x (Pi.single j 1)
  rw [CoxeterSystem.wordProd_reverse, inv_inv, pPairing_single] at h1
  rw [h1, h, pPairing_single, Pi.smul_apply, smul_eq_mul]

end Weyl

end CFSG.LocalAnalysis.RankFourTheoremC.ExcRank
