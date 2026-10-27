module

public import Certificates.Data.Kernel.Co1FiveK
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.LocalCompCo1EndSound
public import CFSG.Sporadic.Co1.Module.InvSpec

public section

namespace CFSG.KC.Co1FiveK

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native

theorem pow_unpack (M : Nat) : ∀ e : Nat, pow (unpack 24 24 M) e = unpack 24 24 (pwK M e)
  | 0 => MatL.unpack_idM.symm
  | e + 1 => by
    have h : pwK M (e + 1) = CFSG.KC.Co1B.mulWK (pwK M e) M := MatL.strictN_eq _ _
    rw [pow, pow_unpack M e, mul_unpackW, h]

theorem a0Row_eq {rs : List Rows} {D : Nat → Nat}
    (hD : ∀ i < 3, Timmesfeld.Co1Five.rowAt rs (Timmesfeld.Co1Five.idxD.getD i 0) =
      unpack 24 24 (D i)) (k : Nat) :
    Timmesfeld.Co1Five.a0Row rs k = unpack 24 24 (a0K D k) := by
  unfold Timmesfeld.Co1Five.a0Row a0K
  rw [hD 0 (by norm_num), hD 1 (by norm_num), hD 2 (by norm_num), pow_unpack, pow_unpack,
    pow_unpack, mul_unpackW, mul_unpackW]
  rfl

theorem ne_of_eqK {X Y : Nat} (h : CFSG.KC.Co1End.eqK X Y = false) :
    CFSG.Sporadic.Co1.InvNative.rowsKey (unpack 24 24 X) ≠
      CFSG.Sporadic.Co1.InvNative.rowsKey (unpack 24 24 Y) := by
  intro e
  have e' := CFSG.Sporadic.Co1.Module.rowsKey_inj (CFSG.KC.Co1End.validRows_unpack X)
    (CFSG.KC.Co1End.validRows_unpack Y) e
  have hb := CFSG.KC.Co1End.beq_unpack X Y
  rw [e', beq_self_eq_true] at hb
  rw [← hb] at h
  exact absurd h (by decide)

end CFSG.KC.Co1FiveK

end
