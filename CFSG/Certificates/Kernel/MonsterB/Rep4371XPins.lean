module

public import Certificates.Data.Kernel.MonsterB.Rep4371XGen
public import Certificates.Data.CFSGNative.MonsterB.PacketCheck
public import CFSG.Monster.B.Rep4371.Model

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.Monster.B

theorem pauli_pins : ∀ i < 23, qsT i = (Model.qPauli i).s.toNat ∧ f12 QA i = (Model.qPauli i).a ∧
    f12 QD i = (Model.qPauli i).d := by
  decide +kernel

theorem perm_pins : ∀ r < 12, (Model.recPerms[r]!).size = 24 ∧ pP r < 2 ^ 120 ∧
    (∀ i < 24, pe (pP r) i = (Model.recPerms[r]!)[i]!) ∧ betaTabT (pP r) = pBT r ∧
    kappaT (pBT r) 63 = pK r := by
  decide +kernel

theorem sign_pins : ∀ r < 11, f12 SA r = CFSG.Monster.B.Rep4371.Native.signCodes[r]! ∧ f12 SA r < 4096 ∧
    wordT (f12 SA r) = sW r ∧ thetaT (f12 SA r) = f12 STT r ∧ pT (f12 SA r) = bitN SP r := by
  decide +kernel

theorem xi_pins : f16 XS 0 = 0 ∧ f16 XK 0 = 0 ∧ f16 XK 9 = 4371 ∧ ∀ c < 9, f16 XS c ≤ f16 XS (c + 1) := by
  decide +kernel

end CFSG.KC.Rep4371X

end
