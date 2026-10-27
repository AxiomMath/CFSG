module

public import CFSG.YGroups.Y443.Native.CoverFactsWords
public import CFSG.YGroups.Y443.Native.Align

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native

@[expose] def denseZWord : List Native.Gen :=
  [.rho (false, 0, 62), .tau, .rho (false, 0, 62), .rho (false, 2532, 716), .tau,
   .rho (false, 470, 1556), .rho (false, 0, 3903), .rho (false, 0, 18),
   .perm #[22, 23, 12, 13, 2, 5, 0, 6, 8, 19, 9, 18, 15, 21, 20, 14, 17, 16, 11, 10, 4, 3, 1, 7],
   .xi, .rho (false, 0, 34),
   .perm #[0, 7, 18, 19, 1, 6, 20, 21, 2, 4, 10, 11, 5, 3, 12, 13, 15, 8, 22, 16, 14, 9, 17, 23],
   .xi, .rho (false, 0, 36),
   .perm #[1, 5, 9, 17, 13, 20, 18, 19, 3, 6, 16, 8, 12, 21, 10, 11, 23, 0, 15, 2, 14, 7, 4, 22],
   .tau, .xi, .xi, .rho (false, 0, 8),
   .perm #[0, 7, 16, 17, 1, 6, 22, 23, 2, 4, 8, 9, 5, 3, 14, 15, 13, 10, 20, 18, 12, 11, 19, 21],
   .xi, .rho (false, 0, 18),
   .perm #[0, 2, 10, 21, 11, 23, 12, 15, 4, 5, 9, 22, 20, 8, 16, 19, 1, 14, 7, 17, 6, 18, 13, 3],
   .tau, .xi, .xi, .rho (false, 0, 20),
   .perm #[0, 5, 10, 11, 1, 4, 14, 15, 2, 6, 17, 16, 7, 3, 21, 20, 22, 19, 12, 8, 23, 18, 9, 13],
   .xi, .xi, .rho (false, 0, 2),
   .perm #[10, 11, 14, 22, 15, 23, 19, 18, 8, 17, 6, 1, 5, 3, 16, 9, 7, 4, 12, 21, 20, 13, 0, 2],
   .tau, .xi, .xi, .rho (false, 0, 2),
   .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
   .xi, .rho (false, 0, 46),
   .perm #[4, 5, 6, 13, 7, 12, 14, 15, 2, 8, 21, 16, 18, 22, 9, 3, 20, 19, 0, 10, 11, 1, 17, 23],
   .tau, .xi, .rho (false, 0, 24),
   .perm #[0, 4, 10, 11, 1, 5, 15, 14, 2, 7, 19, 18, 6, 3, 22, 23, 21, 17, 13, 8, 20, 16, 9, 12],
   .xi, .xi, .rho (false, 0, 24),
   .perm #[4, 6, 9, 11, 16, 22, 21, 17, 5, 10, 7, 8, 12, 1, 3, 14, 13, 15, 0, 2, 19, 23, 18, 20],
   .rho (false, 0, 62), .tau, .rho (false, 0, 62), .xi, .xi, .rho (false, 0, 2),
   .perm #[0, 6, 20, 21, 1, 7, 19, 18, 2, 5, 14, 15, 4, 3, 9, 8, 10, 12, 17, 22, 11, 13, 23, 16],
   .xi, .rho (false, 0, 4),
   .perm #[6, 7, 9, 15, 10, 13, 19, 18, 3, 23, 4, 17, 16, 5, 2, 22, 8, 14, 1, 0, 20, 21, 12, 11],
   .rho (false, 0, 62), .tau, .rho (false, 0, 62), .xi, .rho (false, 0, 58),
   .perm #[0, 2, 11, 12, 1, 4, 22, 17, 3, 6, 19, 20, 7, 5, 14, 9, 21, 15, 10, 23, 18, 8, 16, 13],
   .xi]

@[expose] def densePairs : List (ℕ × ℕ) := [(0, 5), (6, 7), (8, 0), (9, 10), (0, 1), (2, 3)]

@[expose] def denseAlignCheck (v : Native.DVec) : Bool :=
  eqWords (EdgeNoncomm.pairsWord densePairs ++ omegaWord) (omegaWord ++ denseZWord ++ coverPHat) v

@[expose] def denseMoveCheck (v : Native.DVec) : Bool :=
  denseZWord.all Native.Gen.validB && (Native.evalWord tWord v).eqv v &&
    EdgeNoncomm.moveCheck tWord (Native.evalWord (powL 17 denseZWord) v)

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
