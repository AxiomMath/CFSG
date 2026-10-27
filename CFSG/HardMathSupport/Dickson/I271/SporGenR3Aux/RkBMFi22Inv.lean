module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMCoverReps
public import Certificates.Certificate17373

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three CFSG.Sporadic.Fi22
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native CFSG.F3.Native

section Reps

theorem rkBMInvAt_xRep (k : Fin 4) : RkBMInvAt (xRep k.val) :=
  Certificates.certificate17373 k.val k.isLt

theorem rkBMInv_Fi22 : RkBMInv NativeSporadic.Fi22 :=
  rkBMInv_Fi22_of_reps rkBMInvAt_xRep

theorem rkAut_Fi22_cover_holds (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {T : Type} [Group T]
    [Finite T] (hq : CFSG.Open.IsQuasisimple T) (hZ : IsPGroup 3 (Subgroup.center T))
    (e : T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) : RkAut 3 T :=
  rkAut_Fi22_cover hOut hSpM hBr rkBMInv_Fi22 hq hZ e

theorem rkSpor_Fi22_three_of_quasisimple (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {T : Type} [Group T]
    [Finite T] (hq : CFSG.Open.IsQuasisimple T) (hZ : IsPGroup 3 (Subgroup.center T))
    (hA6 : Nonempty ((T ⧸ Subgroup.center T) ≃* ↥(alternatingGroup (Fin 6))) →
      Subgroup.center T = ⊥) :
    RkSpor 3 [.Fi22] T := by
  rintro (⟨-, ⟨f⟩⟩ | ⟨S, hS, ⟨f⟩⟩)
  · exact rkAut_of_equiv ((rkBMQuotBot (hA6 ⟨f⟩)).trans f).symm rkAut_three_alt6
  · obtain rfl := List.mem_singleton.1 hS
    exact rkAut_Fi22_cover_holds hOut hSpM hBr hq hZ f

end Reps

end CFSG.HardMathSupport.Dickson.I271
