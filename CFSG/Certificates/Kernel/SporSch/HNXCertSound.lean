module

public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Certificates.Data.Kernel.SporSch.HNXBind
public import Certificates.Data.CFSGNative.HN.F5Cert

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.HNSchreier.Native

@[expose] def HNXChecks (D : F5Data) (T CNT SGT : Nat → Nat) (MS CM3 M GA GB W1 W2 V0C : Nat)
    (cs1 cs2 cr : List Char) : Prop :=
  D.d = 133 ∧ D.n = 1140000 ∧ D.seedA = String.ofList cs1 ∧ D.seedB = String.ofList cs2 ∧
    D.root = String.ofList cr ∧
    CFSG.KC.Ord.andB (constsOK CM3 M) (masksOK MS) = true ∧
    seedRK W1 cs1 = true ∧ seedRK W2 cs2 = true ∧
    Nat.beq (trM W1) GA = true ∧ Nat.beq (trM W2) GB = true ∧
    (∀ b < 17813, Nat.beq (coreLeaf T 464 1140000 MS CM3 M GA GB b (hnxC b)) (CNT b) = true) ∧
    Nat.beq (sumK CNT) 1139999 = true ∧
    (∀ m < 17813, sortChunk T 464 1140000 (SGT m) (hnxS m) = true) ∧ linkK SGT = true ∧
    Nat.beq (Nat.land (getRec T 464 0) M) V0C = true ∧ rootK V0C cr = true

theorem hnxBindK_of {T : Nat → Nat} {P : PackedOrbitData} (hs : hnxShapeK P = true)
    (hv : walkOK (vecAt T) P.vectors (nat_lit 0) = true)
    (ha : walkOK (imgAt T (nat_lit 0)) P.alpha (nat_lit 0) = true)
    (hb : walkOK (imgAt T (nat_lit 1)) P.beta (nat_lit 0) = true)
    (hp : walkOK (parAt T) P.parents (nat_lit 0) = true)
    (hl : walkOK (labAt T) P.labels (nat_lit 0) = true) : hnxBindK T P = true := by
  unfold hnxBindK
  rw [hs, hv, ha, hb, hp, hl]

end CFSG.KS.SporSch

end
