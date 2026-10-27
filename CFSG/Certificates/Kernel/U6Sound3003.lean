module

public import Certificates.Data.Kernel.U6.HuntK
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntRankData
import CFSG.Certificates.Kernel.U6Hunt.Search
import CFSG.Certificates.Kernel.U6Hunt.Count
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.Sporadic.Th.Native
  CFSG.ComponentClassification.WittDesign

theorem sound3003C {PS PSI LR TR TRI : Nat → Nat} {kS BP chunks : Nat}
    {S : Array (Array Nat)} {base : Array Nat} {W : Array (List ℤ)} {g₁ g₂ : Equiv.Perm (Fin 22)}
    {k8 k0 kY : Nat} {L8 L0 LY : List Nat} {V : Nat → Nat}
    (hb : CFSG.KS.Raw.Binds 22 5 PS kS 5 BP S base)
    (hp : CFSG.KC.Enum.allN kS (fun j => CFSG.KC.Enum.permOK 22 5 (CFSG.KS.mask 5) (22 * 5) (PS j)
      (PSI j)) = true)
    (hl : CFSG.KS.Raw.LevelsOK 22 5 PS PSI LR TR TRI kS 5 BP)
    (hraw : CFSG.Certificates.Native.rawChainOK 22 (S.extract 0 2) S base W chunks = true)
    (hg : CFSG.Monster.B.Co2.Rep 22 S[0]! g₁ ∧ CFSG.Monster.B.Co2.Rep 22 S[1]! g₂)
    (hsz : ∀ i < 5, CFSG.KS.Raw.rcnt (LR i) = [22, 21, 20, 16, 3].getD i 0)
    (hd : ∀ k ∈ [k8, k0, kY], ∀ i < 22, fget (unkey k) i 5 < 22)
    (hL : ∀ k ∈ L8 ++ L0 ++ LY, k < 2 ^ 110)
    (hk : ∀ a < 22, chunkK (unkey k8) (unkey k0) (unkey kY) L8 L0 LY TR
      (sumN 5 fun i => Nat.shiftLeft (CFSG.KS.Raw.roff 22 (22 * 5) (LR i)) (Nat.mul 32 i)) a =
        V a)
    (hc : 0 < chunks) :
    let G := Subgroup.closure ({g₁, g₂} : Set (Equiv.Perm (Fin 22)))
    let N := fun k => fget (sumN 22 V) k 20
    Nat.card {x : G // (missOut (tf (decodeT k8)) (L8.map decodeT) ⇑(x : Equiv.Perm (Fin 22)) ||
        missOut (tf (decodeT k0)) (L0.map decodeT) ⇑(x : Equiv.Perm (Fin 22)) ||
        missIn (tf (decodeT kY)) (LY.map decodeT) ⇑(x : Equiv.Perm (Fin 22))) = true} = N 0 ∧
      Nat.card {x : G // sqMulB (tf (decodeT k8)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 1 ∧
      Nat.card {x : G // (sqB ⇑(x : Equiv.Perm (Fin 22)) &&
        !eqB id ⇑(x : Equiv.Perm (Fin 22))) = true} = N 2 ∧
      Nat.card {x : G // commB (tf (decodeT k8)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 3 ∧
      Nat.card {x : G // commB (tf (decodeT k0)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 4 ∧
      Nat.card {x : G // commB (tf (decodeT kY)) ⇑(x : Equiv.Perm (Fin 22)) = true} = N 5 :=
  CountPf.sound3003C' hb hp hl hraw hg hsz hd hL hk hc

theorem sound3003R {B k : Nat} {L : List Nat} (hd : ∀ i < 22, fget (unkey k) i 5 < 22)
    (hL : ∀ x ∈ L, x < 2 ^ 110 ∧ ∀ i < 22, fget (unkey x) i 5 < 22)
    (hk : rootK B k L = true) : rootCheck B (decodeT k) (L.map decodeT) = true :=
  HuntPf.sound3003R' hd hL hk

theorem sound3003P {L : List Nat} (hs : L.Pairwise (· < ·)) (hL : ∀ x ∈ L, x < 2 ^ 110) :
    (L.map decodeT).Pairwise (fun a b => keyT a < keyT b) :=
  HuntPf.sound3003P' hs hL

end CFSG.KC.U6

end
