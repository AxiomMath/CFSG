module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

theorem inf_centralizer_eq_bot_of_gsUnbalancingTriple [IsSimpleGroup X]
    (hS : SchreierFor Blueprint.Catalog) (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) {a x u : X} {J : Subgroup X}
    (hmax : GSMaximalUnbalancingTriple a x J) (hiso : GSIsoAt a J)
    (hU : GSUnbalancingTriple a u J) {B : Subgroup X} (hB2 : IsPGroup 2 B)
    (hBa : B ≤ centralizer ({a} : Set X)) (hBJ : B ≤ coreActionKernel J)
    (hcl : conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X))) =
      layerIn (normalizer (B : Set X)))
    (hcomm : ⁅layerIn (normalizer (B : Set X)), zpowers a⁆ =
      layerIn (normalizer (B : Set X))) :
    B ⊓ centralizer ({u} : Set X) = ⊥ := by
  have h1 := inf_conjugate_eq_bot hS hnonab hK ⟨hU, hmax.2⟩ hiso hB2 hBa hBJ hcl hcomm
  refine eq_bot_iff.mpr fun b hb => ?_
  obtain ⟨hbB, hbu⟩ := mem_inf.mp hb
  have hbu' : b ∈ conjugate B u := by
    rw [mem_conjugate_iff, ← mem_centralizer_singleton_iff.mp hbu, mul_inv_cancel_right]
    exact hbB
  rw [← h1]
  exact mem_inf.mpr ⟨hbB, hbu'⟩

namespace Hyp52

theorem inf_centralizer_eq_bot [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J) {u : X}
    (hU : GSUnbalancingTriple h.a u h.J) : h.B ⊓ centralizer ({u} : Set X) = ⊥ :=
  inf_centralizer_eq_bot_of_gsUnbalancingTriple hS hnonab h.kProper hmax hiso hU
    (B5a.isPGroup_B h) ((h.B_le.trans inf_le_left).trans (h.S_le.trans inf_le_left))
    (h.B_le.trans inf_le_right) h.conjClosure_eq h.commutator_eq

theorem secB0_inf_centralizer_eq_bot [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J) (hiso : GSIsoAt h.a h.J) {u : X}
    (hU : GSUnbalancingTriple h.a u h.J) (y : X) :
    h.secB0 y ⊓ centralizer ({u} : Set X) = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right _ (h.secB0_le_B y)).trans
    (h.inf_centralizer_eq_bot hS hnonab hmax hiso hU).le)

end Hyp52

end CFSG.ComponentClassification.GSThmB
