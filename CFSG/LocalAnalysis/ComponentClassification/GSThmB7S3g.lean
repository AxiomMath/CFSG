module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddTimesTwoTransport
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Seven

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conjugate_eq_of_le_centralizer {M : Subgroup X} {a : X}
    (hM : M ≤ centralizer ({a} : Set X)) : conjugate M a = M := by
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro hx
    have h1 : a * x * a⁻¹ * a = a * (a * x * a⁻¹) := mem_centralizer_singleton_iff.mp (hM hx)
    have h2 : x = a * x * a⁻¹ := by
      calc x = a⁻¹ * (a * x * a⁻¹ * a) := by group
        _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [h1]
        _ = a * x * a⁻¹ := by group
    rw [h2]
    exact hx
  · intro hx
    have h1 : x * a = a * x := mem_centralizer_singleton_iff.mp (hM hx)
    rw [← h1, mul_inv_cancel_right]
    exact hx

end Seven

end CFSG.ComponentClassification.GSThmB
