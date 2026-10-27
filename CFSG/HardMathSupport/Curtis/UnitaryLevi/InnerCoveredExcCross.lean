module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.HardMathSupport.Curtis.Proving.E27RankKill

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Foote.E27 CFSG.LieType.SeitzGeneration TauCeti
open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
open CFSG.HardMathSupport.Curtis.Proving

@[expose] def InnerCoveredExcCross (i : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, q.p ≠ 3 ∧ (i = .G2 q ∨ i = .F4 q ∨ i = .E6 q ∨ i = .twistedE6 q ∨
    i = .E7 q ∨ i = .E8 q ∨ i = .trialityD4 q)) ∨ (∃ m, i = .reeF4 m) ∨ (∃ m, i = .suzuki m) ∨
    i = .tits


theorem false_of_exc_cross_G2 {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (q : TauCeti.PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hq : q.p ≠ 3)
    (e : Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie ⟨LieTypeIndex.G2 q, hv⟩).Group)) : False := by
  obtain ⟨e⟩ := e
  exact false_of_E27_rankLE2 h hz
    (RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_three_cat_G2 q hv (Ne.symm hq)))

end CFSG.HardMathSupport.Curtis.UnitaryLevi
