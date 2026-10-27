module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public import Certificates.Data.G23RecogWordsInputs
public meta import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCensusInputs
public meta import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabThNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative CFSG.GH74.QTGen4.Recog.G23

set_option compiler.extract_closed false

@[expose] def progE : List Op := prog3 ++ [
  .mul 1 0 15, .pow 3 10 16, .pow 6 10 17, .mul 16 15 18, .mul 18 17 19, .mul 19 15 20,
  .mul 20 10 21, .pow 3 21 22, .mul 22 12 23, .pow 2 23 24, .mul 24 22 25, .mul 25 24 26,
  .mul 26 22 27, .mul 27 24 28, .mul 28 22 29, .mul 29 24 30, .mul 30 22 31, .mul 31 24 32,
  .mul 32 22 33, .mul 33 23 34, .mul 34 22 35, .mul 35 23 36, .mul 36 22 37, .mul 37 23 38,
  .mul 38 22 39, .mul 39 23 40, .mul 40 22 41, .mul 41 23 42, .mul 42 22 43, .mul 22 23 44,
  .mul 44 22 45, .mul 45 24 46, .mul 46 22 47, .mul 47 24 48, .mul 48 22 49, .mul 49 23 50,
  .mul 50 22 51, .mul 51 23 52, .mul 52 22 53, .mul 53 23 54, .mul 54 22 55, .mul 55 24 56,
  .mul 56 22 57, .mul 57 24 58, .mul 58 22 59, .mul 59 24 60, .mul 60 22 61, .mul 61 24 62,
  .mul 62 22 63, .mul 63 24 64, .mul 64 22 65, .mul 65 23 66, .mul 66 22 67, .mul 67 24 68,
  .mul 68 22 69, .mul 69 23 70, .mul 70 22 71, .mul 71 24 72, .mul 72 22 73, .mul 22 23 74,
  .mul 74 22 75, .mul 75 24 76, .mul 76 22 77, .mul 77 24 78, .mul 78 22 79, .mul 79 24 80,
  .mul 80 22 81, .mul 81 23 82, .mul 82 22 83, .mul 83 23 84, .mul 84 22 85, .mul 85 23 86,
  .mul 86 22 87, .mul 87 24 88, .mul 88 22 89, .mul 89 24 90, .mul 90 22 91, .mul 91 23 92,
  .mul 92 22 93, .mul 93 23 94, .mul 94 22 95, .mul 95 23 96, .mul 96 22 97, .mul 97 23 98,
  .mul 98 22 99, .mul 99 24 100, .mul 100 22 101, .mul 101 24 102, .mul 102 22 103,
  .mul 103 24 104, .mul 104 22 105, .mul 105 24 106, .mul 106 22 107, .mul 107 23 108,
  .mul 22 24 109, .mul 109 22 110, .mul 110 24 111, .mul 111 22 112, .mul 112 23 113,
  .mul 113 22 114, .mul 114 23 115, .mul 115 22 116, .mul 116 23 117, .mul 117 22 118,
  .mul 118 24 119, .mul 119 22 120, .mul 120 24 121, .mul 121 22 122, .mul 122 23 123,
  .mul 123 22 124, .mul 124 23 125, .mul 125 22 126, .mul 126 24 127, .mul 127 22 128,
  .mul 128 24 129, .mul 129 22 130, .mul 130 24 131, .mul 131 22 132, .mul 132 23 133,
  .mul 133 22 134, .mul 134 23 135, .mul 22 24 136, .mul 136 22 137, .mul 137 24 138,
  .mul 138 22 139, .mul 139 24 140, .mul 140 22 141, .mul 141 24 142, .mul 142 22 143,
  .mul 143 24 144, .mul 144 22 145, .mul 145 23 146, .mul 146 22 147, .mul 147 23 148,
  .mul 148 22 149, .mul 149 23 150, .mul 150 22 151, .mul 151 23 152, .mul 152 22 153,
  .mul 153 23 154, .mul 154 22 155, .mul 22 23 156, .mul 156 22 157, .mul 157 23 158,
  .mul 158 22 159, .mul 159 24 160, .mul 160 22 161, .mul 161 23 162, .mul 162 22 163,
  .mul 163 24 164, .mul 164 22 165, .mul 165 24 166, .mul 166 22 167, .mul 167 24 168,
  .mul 168 22 169, .mul 169 24 170, .mul 170 22 171, .mul 171 24 172, .mul 172 22 173,
  .mul 173 23 174, .mul 174 22 175, .mul 175 23 176, .mul 176 22 177, .mul 177 24 178,
  .mul 178 22 179, .mul 179 23 180, .mul 180 22 181, .mul 181 24 182, .mul 182 22 183,
  .mul 183 23 184, .mul 184 22 185, .mul 185 23 186, .mul 186 22 187, .mul 187 24 188,
  .mul 188 22 189, .mul 189 23 190, .mul 190 22 191, .mul 191 24 192, .mul 192 22 193,
  .pow 2 43 194, .pow 2 73 195, .pow 2 108 196, .pow 2 135 197, .pow 7 193 198
  ]

@[expose] def eIdx (k : Nat) : Nat := [43, 73, 108, 135, 155, 193].getD k 0

@[expose] def eiIdx (k : Nat) : Nat := [194, 195, 196, 197, 155, 198].getD k 0

end CFSG.HardMathSupport.Dickson.I271.TabThNative
