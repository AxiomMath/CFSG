module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.GOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.OutputInputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem lemma27Exists_of_inputs
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog)
    (hL : SmallSimpleLookup) : Lemma27Exists := by
  intro G _ _ _ hK t z z₁ ι zv R0 F h hzt htz hCz
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc⟩ := isConj_iff.mp htz
    have hct : c * t * c⁻¹ = t := by
      rw [hcon c t, mul_assoc, mul_inv_cancel, mul_one]
    have hz : t * z = t := hc.symm.trans hct
    exact h.z_ne_one (mul_eq_left.mp hz)
  exact lemma27Out_of_inputs hnonab hK hS hL h hzt htz hCz

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
