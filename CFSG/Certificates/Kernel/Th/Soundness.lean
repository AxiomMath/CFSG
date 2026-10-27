module


public import CFSG.Sporadic.Th.KernelInputs
import CFSG.Certificates.Kernel.Th.SoundnessGen

public section

namespace CFSG.KC.Th.Soundness

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier
  Pointwise CFSG.KC.Th.Gen

theorem dceStruct_sound (D : DceStructData) (_h : dceStructChk D = true) : DceFacts :=
  DceStructGen.inst (dceStruct_sound_gen _ isHsw_th D _h)

theorem dce_sound (D : DceData) (_h : dceChk D = true) : Finite P ∧ Nat.card P ≤ thOrder :=
  dce_sound_gen _ isHsw_th D _h

theorem sylow2_sound (D : Sylow2Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : sylow2Chk D = true) :
    2 ^ 15 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th :=
  sylow2_sound_gen _ _ D (seedA_eq.symm.trans _hA) (seedB_eq.symm.trans _hB) _h

theorem sylow3_sound (D : Sylow3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : sylow3Chk D = true) :
    3 ^ 10 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th :=
  sylow3_sound_gen _ _ D (seedA_eq.symm.trans _hA) (seedB_eq.symm.trans _hB) _h

theorem sylow5_sound (D : Sylow5Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : sylow5Chk D = true) :
    5 ^ 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th :=
  sylow5_sound_gen _ _ D (seedA_eq.symm.trans _hA) (seedB_eq.symm.trans _hB) _h

theorem sylow7_sound (D : Sylow7Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : sylow7Chk D = true) :
    7 ^ 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th :=
  sylow7_sound_gen _ _ D (seedA_eq.symm.trans _hA) (seedB_eq.symm.trans _hB) _h

theorem orders_sound (D : OrdersData) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : ordersChk D = true) :
    13 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th ∧
      19 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th ∧
      31 ∣ Nat.card CFSG.Blueprint.NativeSporadic.Th ∧
      (a * b) ^ 19 = 1 :=
  OrdersGen.inst (thSeeds_subst (G := fun tA tB => OrdersGen Native.seedA Native.seedB tA tB)
    (orders_sound_gen _ _ D _hA _hB _h))

theorem fwd_sound (D : FwdData) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : fwdChk D = true) :
    (∃ ψ : P →* J, (∀ i < 7, ψ (gen i) ∈ H ∧ ψ (gen i) • Wset = Wset) ∧
      ψ (gen 0) ^ 2 = 1 ∧ a ∈ ψ.range ∧ b ∈ ψ.range) ∧
    xJ • Wset = Wset ∧ yJ • Wset = Wset ∧ b • Wset ≠ Wset :=
  FwdGen.inst (thSeeds_subst
    (G := fun tA tB => FwdGen Native.seedA Native.seedB tA tB TauCeti.SporadicName.Th.presentation)
    (fwd_sound_gen _ _ _ isHsw_th D _hA _hB _h))

theorem gen_sound (D : GenData) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : genChk D = true) :
    GenFact fusionWord0' (Max3.q 0) ∧ GenFact fusionWord1' Max3.x :=
  GenGen.inst (thSeeds_subst (G := fun tA tB => GenGen Native.seedA Native.seedB tA tB)
    (gen_sound_gen _ _ D _hA _hB _h))

end CFSG.KC.Th.Soundness
