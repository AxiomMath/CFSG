module

import CFSG.RankThree.Native.HSMcLFiveCheckInputs
public meta import CFSG.RankThree.Native.HSMcLFiveCheckInputs

public section

namespace CFSG.AGLEmbedding.KFactProofs.OrbitsCube

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Schreier CFSG.RankThree.Native

@[expose] def mclFiveNormArr : Array ℕ :=
  #[
    176, 250, 72, 23, 231, 234, 41, 150, 171, 89, 79, 247, 241, 61, 105, 122, 187, 140, 15, 11,
    257, 141, 2, 227, 36, 67, 269, 178, 179, 25, 181, 129, 236, 95, 54, 188, 81, 13, 8, 273, 138,
    222, 107, 254, 158, 239, 224, 84, 85, 39, 252, 51, 219, 29, 213, 263, 255, 142, 225, 45, 44,
    201, 191, 42, 268, 27, 157, 256, 82, 172, 203, 56, 52, 229, 154, 0, 170, 123, 31, 272, 145,
    168, 208, 69, 14, 245, 99, 73, 43, 101, 212, 162, 184, 116, 12, 195, 50, 215, 128, 238, 70,
    16, 240, 182, 206, 47, 26, 86, 175, 244, 143, 270, 126, 190, 155, 209, 76, 90, 260, 4, 18,
    163, 262, 174, 131, 71, 167, 183, 57, 80, 274, 118, 92, 83, 216, 180, 103, 132, 135, 149, 66,
    194, 125, 9, 166, 223, 49, 199, 189, 1, 156, 117, 102, 30, 207, 111, 211, 17, 264, 10, 139,
    133, 259, 33, 110, 249, 165, 121, 220, 63, 159, 173, 87, 200, 21, 19, 22, 55, 198, 48, 226,
    38, 160, 148, 146, 74, 35, 164, 53, 127, 113, 62, 204, 185, 251, 112, 261, 108, 258, 197, 153,
    37, 265, 32, 6, 120, 242, 68, 193, 243, 40, 96, 151, 100, 230, 114, 97, 232, 169, 75, 248,
    115, 152, 109, 28, 253, 214, 267, 46, 161, 210, 65, 205, 58, 59, 88, 34, 7, 218, 130, 192,
    202, 94, 221, 78, 228, 5, 147, 196, 3, 136, 266, 237, 60, 235, 98, 186, 106, 119, 124, 271,
    24, 217, 20, 233, 104, 77, 144, 64, 177, 134, 91, 93, 137, 246
  ]

@[expose] def mclFiveWord (i j k : ℕ) : Array ℕ :=
  compA 275 (compA 275 (powArr 275 (mcl275FiveArr 0) i) (powArr 275 (mcl275FiveArr 1) j))
    (powArr 275 (commutatorA 275 (mcl275FiveArr 0) (mcl275FiveArr 1)) k)

@[expose] def mclFiveNormCheck : Bool :=
  validA 275 (mcl275FiveArr 0) && validA 275 (mcl275FiveArr 1) && validA 275 mclFiveNormArr &&
    siftA 275 mcl275PLevels PairMcL.baseArr 0 mclFiveNormArr &&
    !(eqA 275 (commutatorA 275 (mcl275FiveArr 0) (mcl275FiveArr 1)) (idA 275)) &&
    eqA 275 (conjA 275 mclFiveNormArr (mcl275FiveArr 0)) (mclFiveWord 1 2 0) &&
    eqA 275 (conjA 275 mclFiveNormArr (mcl275FiveArr 1)) (mclFiveWord 1 4 0)

end CFSG.AGLEmbedding.KFactProofs.OrbitsCube
