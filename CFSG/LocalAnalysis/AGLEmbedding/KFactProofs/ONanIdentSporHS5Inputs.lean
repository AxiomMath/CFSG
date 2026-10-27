module

public import CFSG.RankThree.PartOne.CTP.FusionDefs

public section

namespace CFSG.RankThree.PartOne.CTP.Fus

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def fusHSFive : Spec where
  p := 5
  rA := 0
  oA := 2
  rB := 1
  oB := 5
  rx := 46
  ry := 105
  tx := 0
  gens :=
    [⟨142, 20, [(46, 1)], [(46, 1)], 0⟩,
     ⟨202, 10, [(105, 1)], [(105, 1)], 0⟩]
  wA :=
    [(142, 18), (202, 3), (142, 1), (202, 1), (142, 1), (202, 3), (142, 2), (202, 9), (142, 17),
     (202, 7), (142, 17), (202, 7), (142, 19), (202, 9), (142, 3), (202, 9), (142, 2), (202, 9),
     (142, 17), (202, 7), (142, 19)]
  wB :=
    [(142, 1), (202, 1), (142, 2), (202, 9), (142, 19), (202, 1), (142, 1), (202, 9), (142, 18),
     (202, 9), (142, 19)]

@[expose] def fusHSFiveN : Nat := 203

@[expose] def fusHSFiveProg : List Op :=
    [.pow 4 1 2, .mul 0 1 3, .mul 3 1 4, .mul 4 0 5, .mul 5 1 6, .mul 6 1 7, .mul 7 0 8, .mul 8 1 9,
     .mul 9 0 10, .mul 10 1 11, .mul 11 1 12, .mul 12 0 13, .mul 13 2 14, .mul 14 0 15,
     .mul 15 2 16, .mul 16 0 17, .mul 17 2 18, .mul 18 0 19, .mul 19 1 20, .mul 20 0 21,
     .mul 21 1 22, .mul 22 1 23, .mul 23 0 24, .mul 24 2 25, .mul 25 0 26, .mul 26 2 27,
     .mul 27 2 28, .mul 28 0 29, .mul 29 1 30, .mul 30 1 31, .mul 31 0 32, .mul 32 2 33,
     .mul 33 2 34, .mul 34 0 35, .mul 35 1 36, .mul 36 1 37, .mul 37 0 38, .mul 38 2 39,
     .mul 39 0 40, .mul 40 1 41, .mul 41 1 42, .mul 42 0 43, .mul 43 2 44, .mul 44 0 45,
     .mul 45 2 46, .mul 0 2 47, .mul 47 0 48, .mul 48 2 49, .mul 49 2 50, .mul 50 0 51,
     .mul 51 2 52, .mul 52 0 53, .mul 53 1 54, .mul 54 0 55, .mul 55 1 56, .mul 56 0 57,
     .mul 57 1 58, .mul 58 1 59, .mul 59 0 60, .mul 60 1 61, .mul 61 0 62, .mul 62 1 63,
     .mul 63 1 64, .mul 64 0 65, .mul 65 1 66, .mul 66 1 67, .mul 67 0 68, .mul 68 1 69,
     .mul 69 1 70, .mul 70 0 71, .mul 71 1 72, .mul 72 0 73, .mul 73 2 74, .mul 74 2 75,
     .mul 75 0 76, .mul 76 1 77, .mul 77 0 78, .mul 78 1 79, .mul 79 0 80, .mul 80 2 81,
     .mul 81 0 82, .mul 82 2 83, .mul 83 0 84, .mul 84 2 85, .mul 85 1 86, .mul 86 0 87,
     .mul 87 1 88, .mul 88 0 89, .mul 89 1 90, .mul 90 0 91, .mul 91 1 92, .mul 92 0 93,
     .mul 93 2 94, .mul 94 2 95, .mul 95 0 96, .mul 96 2 97, .mul 97 2 98, .mul 98 0 99,
     .mul 99 1 100, .mul 100 1 101, .mul 101 0 102, .mul 102 2 103, .mul 103 2 104, .mul 104 0 105,
     .mul 0 1 106, .mul 106 1 107, .mul 107 0 108, .mul 108 1 109, .mul 109 1 110, .mul 110 0 111,
     .mul 111 1 112, .mul 112 1 113, .mul 113 0 114, .mul 114 2 115, .mul 115 0 116, .mul 116 1 117,
     .mul 117 0 118, .mul 118 2 119, .mul 119 2 120, .mul 120 0 121, .mul 121 2 122, .mul 122 0 123,
     .mul 123 2 124, .mul 124 2 125, .mul 125 0 126, .mul 126 2 127, .mul 127 0 128, .mul 128 1 129,
     .mul 129 0 130, .mul 130 1 131, .mul 131 0 132, .mul 132 1 133, .mul 133 1 134, .mul 134 0 135,
     .mul 135 1 136, .mul 136 0 137, .mul 137 1 138, .mul 138 1 139, .mul 139 0 140, .mul 140 2 141,
     .mul 141 0 142, .mul 0 1 143, .mul 143 1 144, .mul 144 0 145, .mul 145 2 146, .mul 146 2 147,
     .mul 147 0 148, .mul 148 1 149, .mul 149 1 150, .mul 150 0 151, .mul 151 2 152, .mul 152 2 153,
     .mul 153 0 154, .mul 154 1 155, .mul 155 1 156, .mul 156 0 157, .mul 157 2 158, .mul 158 0 159,
     .mul 159 2 160, .mul 160 2 161, .mul 161 0 162, .mul 162 1 163, .mul 163 0 164, .mul 164 2 165,
     .mul 165 2 166, .mul 166 0 167, .mul 167 2 168, .mul 168 0 169, .mul 169 2 170, .mul 170 0 171,
     .mul 171 1 172, .mul 172 0 173, .mul 173 2 174, .mul 174 0 175, .mul 175 2 176, .mul 176 0 177,
     .mul 177 2 178, .mul 178 0 179, .mul 179 2 180, .mul 180 0 181, .mul 181 1 182, .mul 182 1 183,
     .mul 183 0 184, .mul 184 2 185, .mul 185 2 186, .mul 186 0 187, .mul 187 2 188, .mul 188 2 189,
     .mul 189 0 190, .mul 190 2 191, .mul 191 0 192, .mul 192 1 193, .mul 193 1 194, .mul 194 0 195,
     .mul 195 1 196, .mul 196 1 197, .mul 197 0 198, .mul 198 2 199, .mul 199 0 200, .mul 200 2 201,
     .mul 201 2 202]

end CFSG.RankThree.PartOne.CTP.Fus
