module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsData

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def eBits : ℕ → Array ℕ
  | 0 => #[17, 34, 4, 8, 16, 32, 64, 128]
  | 1 => #[1, 2, 68, 136, 16, 32, 64, 128]
  | 2 => #[65, 130, 20, 40, 16, 32, 64, 128]
  | _ => #[129, 194, 52, 24, 16, 32, 64, 128]

@[expose] def eWord : ℕ → List (Fin 3)
  | 0 => [2, 0, 2, 2, 0, 1, 1, 1, 0, 1, 1, 0, 1]
  | 1 => [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]
  | 2 => [2, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1]
  | _ => [0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0]

@[expose] def nuBits : ℕ → Array ℕ
  | 0 => #[68, 136, 17, 34, 64, 128, 16, 32]
  | _ => #[168, 252, 91, 173, 176, 208, 48, 16]

@[expose] def nuInvBits : ℕ → Array ℕ
  | 0 => #[68, 136, 17, 34, 64, 128, 16, 32]
  | _ => #[122, 159, 115, 145, 128, 192, 240, 80]

@[expose] def nuWord : ℕ → List (Fin 3)
  | 0 => [2, 0, 1]
  | _ => [1, 0, 2, 2]

@[expose] def nuInvWord : ℕ → List (Fin 3)
  | 0 => [2, 0, 1]
  | _ => [1, 1, 0, 2]

@[expose] def wordCheck : Bool :=
  (List.range 4).all (fun m => wordBits (eWord m) == eBits m) &&
  (List.range 2).all fun j => wordBits (nuWord j) == nuBits j &&
    wordBits (nuInvWord j) == nuInvBits j && bIsId 8 (bmul 8 8 (nuBits j) (nuInvBits j))

@[expose] def unitBits (a b : ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun r => if (r : ℕ) = a then 2 ^ b else 0

@[expose] def blk16Bits (A C : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun r =>
    if (r : ℕ) < 8 then A.getD r 0 % 256 ||| (C.getD r 0 % 256) <<< 8
    else (A.getD (r - 8) 0 % 256) <<< 8

@[expose] def tBits16 : Array ℕ := blk16Bits id8 id8

@[expose] def embedCheck : Bool :=
  (List.range 4).all (fun m => rho16 (eBits m) == bxor 16 id16 (embed16 (aBits m))) &&
  (List.range 8).all (fun a => (List.range 8).all fun b =>
    (List.range 2).all (fun j =>
      bmul 16 16 (bmul 16 16 (rho16 (nuBits j)) (embed16 (unitBits a b))) (rho16 (nuInvBits j)) ==
        embed16 (bmul 8 8 (bmul 8 8 (n0Bits j) (unitBits a b)) (n1Bits j))) &&
    bmul 16 16 (bmul 16 16 tBits16 (embed16 (unitBits a b))) tBits16 ==
      embed16 (bmul 8 8 (bmul 8 8 tBits (unitBits a b)) tBits)) &&
  (List.range 2).all fun j => bmul 8 8 tBits (n0Bits j) == bmul 8 8 (n0Bits j) tBits &&
    bmul 8 8 tBits (n1Bits j) == bmul 8 8 (n1Bits j) tBits

@[expose] def aKerCheck : Bool :=
  (List.range 256).all fun w => w == 0 || (List.range 4).any fun m => bmulVec 8 8 (aBits m) w != 0

@[expose] def candCols (z : ℕ) : Array ℕ :=
  Array.ofFn (n := 8) fun c =>
    packBlks 1 fun _ => if (c : ℕ) < 4 then aBits c else candBits z ((c : ℕ) - 4)

@[expose] def indepCheck : Bool :=
  (List.range 8).all fun z => injCheck 8 64 (btr 8 64 (candCols z))

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
