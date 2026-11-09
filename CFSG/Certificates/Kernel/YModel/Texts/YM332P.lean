module

public import CFSG.Certificates.Kernel.YModel.TextSplit
public import Certificates.Data.CFSGNative.YGroups.ExactData

public section

#ym_text_parts CFSG.KD.YM332P CFSG.YGroups.ModelNative.y332PermText "CFSG/YGroups/Data/y332-perm.txt" 1420650 13824552538483679138 32 0 1024


theorem CFSG.KD.YM332P.okP0 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 0) CFSG.KD.YM332P.CH))) K
      (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 0) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 0)))) (nat_lit 0)) (nat_lit 0) (List.drop (nat_lit 1) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 0))) =
    K (nat_lit 0) (nat_lit 15505) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 484) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 0)))) (nat_lit 544)) (nat_lit 17) (List.drop (nat_lit 485) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 0))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP1 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 80) CFSG.KD.YM332P.CH))) K
      (nat_lit 0) (nat_lit 15505) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 484) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 0)))) (nat_lit 544)) (nat_lit 17) (List.drop (nat_lit 485) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 0))) =
    K (nat_lit 1) (nat_lit 1420) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 44) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1)))) (nat_lit 384)) (nat_lit 12) (List.drop (nat_lit 45) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP2 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 160) CFSG.KD.YM332P.CH))) K
      (nat_lit 1) (nat_lit 1420) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 44) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1)))) (nat_lit 384)) (nat_lit 12) (List.drop (nat_lit 45) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1))) =
    K (nat_lit 1) (nat_lit 16503) (nat_lit 2) (nat_lit 14) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 515) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1)))) (nat_lit 736)) (nat_lit 23) (List.drop (nat_lit 516) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP3 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 240) CFSG.KD.YM332P.CH))) K
      (nat_lit 1) (nat_lit 16503) (nat_lit 2) (nat_lit 14) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 515) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1)))) (nat_lit 736)) (nat_lit 23) (List.drop (nat_lit 516) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 1))) =
    K (nat_lit 2) (nat_lit 2618) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 81) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2)))) (nat_lit 832)) (nat_lit 26) (List.drop (nat_lit 82) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP4 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 320) CFSG.KD.YM332P.CH))) K
      (nat_lit 2) (nat_lit 2618) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 81) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2)))) (nat_lit 832)) (nat_lit 26) (List.drop (nat_lit 82) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2))) =
    K (nat_lit 2) (nat_lit 17501) (nat_lit 4) (nat_lit 1570) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 546) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2)))) (nat_lit 928)) (nat_lit 29) (List.drop (nat_lit 547) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP5 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 400) CFSG.KD.YM332P.CH))) K
      (nat_lit 2) (nat_lit 17501) (nat_lit 4) (nat_lit 1570) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 546) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2)))) (nat_lit 928)) (nat_lit 29) (List.drop (nat_lit 547) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 2))) =
    K (nat_lit 3) (nat_lit 3816) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 119) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3)))) (nat_lit 256)) (nat_lit 8) (List.drop (nat_lit 120) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP6 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 480) CFSG.KD.YM332P.CH))) K
      (nat_lit 3) (nat_lit 3816) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 119) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3)))) (nat_lit 256)) (nat_lit 8) (List.drop (nat_lit 120) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3))) =
    K (nat_lit 3) (nat_lit 18500) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 578) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3)))) (nat_lit 128)) (nat_lit 4) (List.drop (nat_lit 579) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP7 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 560) CFSG.KD.YM332P.CH))) K
      (nat_lit 3) (nat_lit 18500) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 578) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3)))) (nat_lit 128)) (nat_lit 4) (List.drop (nat_lit 579) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 3))) =
    K (nat_lit 4) (nat_lit 5014) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 156) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4)))) (nat_lit 704)) (nat_lit 22) (List.drop (nat_lit 157) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP8 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 640) CFSG.KD.YM332P.CH))) K
      (nat_lit 4) (nat_lit 5014) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 156) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4)))) (nat_lit 704)) (nat_lit 22) (List.drop (nat_lit 157) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4))) =
    K (nat_lit 4) (nat_lit 19498) (nat_lit 2) (nat_lit 20) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 609) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4)))) (nat_lit 320)) (nat_lit 10) (List.drop (nat_lit 610) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP9 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 720) CFSG.KD.YM332P.CH))) K
      (nat_lit 4) (nat_lit 19498) (nat_lit 2) (nat_lit 20) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 609) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4)))) (nat_lit 320)) (nat_lit 10) (List.drop (nat_lit 610) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 4))) =
    K (nat_lit 5) (nat_lit 6212) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 194) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5)))) (nat_lit 128)) (nat_lit 4) (List.drop (nat_lit 195) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP10 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 800) CFSG.KD.YM332P.CH))) K
      (nat_lit 5) (nat_lit 6212) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 194) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5)))) (nat_lit 128)) (nat_lit 4) (List.drop (nat_lit 195) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5))) =
    K (nat_lit 5) (nat_lit 20496) (nat_lit 4) (nat_lit 2119) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 640) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5)))) (nat_lit 512)) (nat_lit 16) (List.drop (nat_lit 641) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP11 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 880) CFSG.KD.YM332P.CH))) K
      (nat_lit 5) (nat_lit 20496) (nat_lit 4) (nat_lit 2119) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 640) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5)))) (nat_lit 512)) (nat_lit 16) (List.drop (nat_lit 641) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 5))) =
    K (nat_lit 6) (nat_lit 7410) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 231) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6)))) (nat_lit 576)) (nat_lit 18) (List.drop (nat_lit 232) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP12 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 960) CFSG.KD.YM332P.CH))) K
      (nat_lit 6) (nat_lit 7410) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 231) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6)))) (nat_lit 576)) (nat_lit 18) (List.drop (nat_lit 232) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6))) =
    K (nat_lit 6) (nat_lit 21495) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 671) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6)))) (nat_lit 736)) (nat_lit 23) (List.drop (nat_lit 672) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP13 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 1040) CFSG.KD.YM332P.CH))) K
      (nat_lit 6) (nat_lit 21495) (nat_lit 0) (nat_lit 0) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 671) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6)))) (nat_lit 736)) (nat_lit 23) (List.drop (nat_lit 672) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 6))) =
    K (nat_lit 7) (nat_lit 8580) (nat_lit 5) (nat_lit 10429) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 268) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7)))) (nat_lit 128)) (nat_lit 4) (List.drop (nat_lit 269) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP14 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 1120) CFSG.KD.YM332P.CH))) K
      (nat_lit 7) (nat_lit 8580) (nat_lit 5) (nat_lit 10429) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 268) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7)))) (nat_lit 128)) (nat_lit 4) (List.drop (nat_lit 269) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7))) =
    K (nat_lit 7) (nat_lit 22493) (nat_lit 2) (nat_lit 23) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 702) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7)))) (nat_lit 928)) (nat_lit 29) (List.drop (nat_lit 703) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP15 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 1200) CFSG.KD.YM332P.CH))) K
      (nat_lit 7) (nat_lit 22493) (nat_lit 2) (nat_lit 23) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 702) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7)))) (nat_lit 928)) (nat_lit 29) (List.drop (nat_lit 703) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 7))) =
    K (nat_lit 8) (nat_lit 9670) (nat_lit 1) (nat_lit 9) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 302) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8)))) (nat_lit 192)) (nat_lit 6) (List.drop (nat_lit 303) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP16 : ∀ K : Nat → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → Bool,
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.take (nat_lit 80) (List.drop (nat_lit 1280) CFSG.KD.YM332P.CH))) K
      (nat_lit 8) (nat_lit 9670) (nat_lit 1) (nat_lit 9) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 302) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8)))) (nat_lit 192)) (nat_lit 6) (List.drop (nat_lit 303) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8))) =
    K (nat_lit 8) (nat_lit 23491) (nat_lit 4) (nat_lit 2227) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 734) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8)))) (nat_lit 96)) (nat_lit 3) (List.drop (nat_lit 735) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8))) :=
  fun _ => by ymKernelRfl

theorem CFSG.KD.YM332P.okP17 :
    CFSG.KC.YModel.decRunWith (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9) (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El)
      (CFSG.KC.YModel.bytesOf (List.drop (nat_lit 1360) CFSG.KD.YM332P.CH)) (CFSG.KC.YModel.ymBase CFSG.KD.YM332P.lines)
      (nat_lit 8) (nat_lit 23491) (nat_lit 4) (nat_lit 2227) (nat_lit 0) (Nat.shiftRight (CFSG.KC.YModel.lhead (List.drop (nat_lit 734) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8)))) (nat_lit 96)) (nat_lit 3) (List.drop (nat_lit 735) ((CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (nat_lit 8))) = true := by
  ymQuickRfl

theorem CFSG.KD.YM332P.ok :
    CFSG.KC.YModel.decBind (CFSG.KC.YModel.bytesOf CFSG.KD.YM332P.CH) (nat_lit 32) CFSG.KD.YM332P.lines (nat_lit 9)
      (CFSG.KC.YModel.lgetL CFSG.KD.YM332P.Cl) (CFSG.KC.YModel.lget CFSG.KD.YM332P.El) = true :=
  CFSG.KC.YModel.ym_ok (by ymQuickRfl)
    ((CFSG.KC.YModel.decRun_eq_with _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP0 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP1 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP2 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP3 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP4 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP5 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP6 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP7 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP8 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP9 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP10 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP11 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP12 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP13 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP14 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP15 rfl _).trans
    ((CFSG.KC.YModel.ym_step CFSG.KD.YM332P.okP16 rfl _).trans
    CFSG.KD.YM332P.okP17))))))))))))))))))


end
