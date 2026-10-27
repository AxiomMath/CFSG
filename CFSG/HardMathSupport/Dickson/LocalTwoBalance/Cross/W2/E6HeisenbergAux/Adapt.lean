module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_triData {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ) (ha : ∀ i, a i ^ 3 = 1)
    {w : WeylGroup Tag.E6} (hw : w ∈ rootCharStabilizer a) (hsh : rootChar a (e6Shift w) ≠ 1) :
    ∃ b : Fin Tag.E6.rank → ZMod 3, (∀ β, β ∈ rootCharKernel a ↔ β ∈ kernelRoots (triChar b)) ∧
      w ∈ charStabilizer (triChar b) ∧ triPairing b (e6Shift w) ≠ 0 := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha)
  set b : Fin Tag.E6.rank → ZMod 3 := fun j => Z3.toAdd (χ' (Multiplicative.ofAdd (Pi.single j 1)))
    with hb
  have hχ' : χ' = triChar b := eq_triChar χ'
  have hker' : ∀ x, rootCharHom3 a x = 1 ↔ triChar b x = 1 := fun x => hχ' ▸ hker x
  refine ⟨b, fun β => ?_, ?_, ?_⟩
  · rw [← kernelRoots_congr_ker hker']
    exact Iff.rfl
  · have : w ∈ charStabilizer (rootCharHom3 a) := hw
    rwa [charStabilizer_congr_ker hker'] at this
  · intro h0
    apply hsh
    have h1 : triChar b (Multiplicative.ofAdd (e6Shift w)) = 1 := by
      rw [triChar_apply, h0, Z3.ofAdd_zero]
    exact (hker' (Multiplicative.ofAdd (e6Shift w))).2 h1

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
