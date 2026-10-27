
module

public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import CFSG.Sporadic.Th.Max3.InvolutionsInputsBase
public meta import Lean
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.TcS
public import CFSG.Sporadic.Th.Max3.CoreBase
public import CFSG.Sporadic.Th.Max3.QuotientBase
public import CFSG.Sporadic.Th.Max3.RelationsBase

public noncomputable section

namespace CFSG.KC.Th.Max3S

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.Sporadic.Th.Max3

open Lean Meta Elab Tactic in
elab "max3s_kernel_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (_, a, _) := t.eq? | throwError "max3s_kernel_rfl: the goal is not an equality"
  g.assign (← mkEqRefl a)
  replaceMainGoal []

@[expose] def balF : ℕ → List Bool → Bool
  | 0, l => l.all id
  | _ + 1, [] => true
  | _ + 1, [a] => a
  | f + 1, a :: b :: t =>
    andB (balF f ((a :: b :: t).take ((t.length + 2) / 2)))
      (balF f ((a :: b :: t).drop ((t.length + 2) / 2)))

@[expose] def bal (l : List Bool) : Bool := balF 13 l

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem balF_true : ∀ (f : ℕ) (l : List Bool), balF f l = true → ∀ b ∈ l, b = true
  | 0, l, h, b, hb => by
    rw [balF, List.all_eq_true] at h
    exact h b hb
  | _ + 1, [], _, _, hb => absurd hb List.not_mem_nil
  | _ + 1, [a], h, b, hb => by
    rw [List.mem_singleton] at hb
    subst hb
    exact h
  | f + 1, a :: c :: t, h, b, hb => by
    rw [balF] at h
    obtain ⟨h1, h2⟩ := andB_eq_true h
    rw [← List.take_append_drop ((t.length + 2) / 2) (a :: c :: t), List.mem_append] at hb
    rcases hb with hb | hb
    · exact balF_true f _ h1 b hb
    · exact balF_true f _ h2 b hb

theorem bal_true {l : List Bool} (h : bal l = true) : ∀ b ∈ l, b = true :=
  balF_true 13 l h

variable (D : Max3Data)

@[expose] def hbit (k : ℕ) : ℕ :=
  if k < 4 then 1 else if k < 8 then 2 else if k < 16 then 3 else if k < 32 then 4 else
  if k < 64 then 5 else if k < 128 then 6 else if k < 256 then 7 else 8

@[expose] def nfReg (k : Fin 512) : Bool :=
  if k.val = 0 then eqN (D.ThM3_RB 25) D.ThS_ONE
  else if k.val = 1 then eqN (D.ThM3_RB 26) (D.ThM3_RB 16)
  else eqN (D.ThM3_RB (25 + k.val))
    (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (25 + (k.val - 2 ^ hbit k.val))) (D.ThM3_RB (16 + hbit k.val)))

@[expose] def qqChk (i : Fin 8) : Bool :=
  eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (17 + i.val)) (D.ThM3_RB (17 + i.val))) D.ThS_ONE

@[expose] def zqChk (i : Fin 8) : Bool :=
  eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB (17 + i.val)))
    (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (17 + i.val)) (D.ThM3_RB 16))

@[expose] def zPow (i j : Fin 8) : ℕ :=
  if (c i j).val = 0 then D.ThS_ONE else BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 16) 1 1

@[expose] def qcChk (i j : Fin 8) : Bool :=
  eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (17 + i.val)) (D.ThM3_RB (17 + j.val)))
    (mulB D.ThS_c D.ThS_rm (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (17 + j.val)) (D.ThM3_RB (17 + i.val)))
      (zPow D i j))

@[expose] def nfIdx (s : ℕ) (e : Fin 8 → ℕ) : ℕ :=
  s + 2 * e 0 + 4 * e 1 + 8 * e 2 + 16 * e 3 + 32 * e 4 + 64 * e 5 + 128 * e 6 + 256 * e 7

@[expose] def xqChk (i : Fin 8) : Bool :=
  eqN (mulB D.ThS_c D.ThS_rm (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB (17 + i.val)))
      (D.ThM3_RB 13))
    (D.ThM3_RB (25 + nfIdx (xz i).val fun j => (xv i j).val))

@[expose] def yqChk (i : Fin 8) : Bool :=
  eqN (mulB D.ThS_c D.ThS_rm (mulB D.ThS_c D.ThS_rm (D.ThM3_RB 14) (D.ThM3_RB (17 + i.val)))
      (D.ThM3_RB 15))
    (D.ThM3_RB (25 + nfIdx (yz i).val fun j => (yv i j).val))

@[expose] def ndChain : List ℕ :=
  [165,
    296,
    78,
    291,
    354,
    271,
    502,
    462,
    404,
    348,
    350,
    453,
    289,
    238,
    129,
    55,
    250,
    162,
    222,
    272,
    401,
    439,
    48,
    45,
    468,
    450,
    66,
    376,
    460,
    103,
    149,
    365,
    4,
    68,
    102,
    393,
    288,
    183,
    465,
    117,
    125,
    220,
    84,
    339,
    97,
    57,
    400,
    156,
    216,
    334,
    208,
    315,
    335,
    119,
    422,
    478,
    333,
    133,
    336,
    410,
    307,
    467,
    290,
    342,
    481,
    135,
    239,
    255,
    65,
    409,
    279,
    396,
    146,
    19,
    488,
    27,
    416,
    11,
    63,
    172,
    95,
    511,
    137,
    224,
    392,
    7,
    470,
    200,
    41,
    449,
    373,
    370,
    61,
    438,
    72,
    64,
    154,
    147,
    197,
    113,
    110,
    107,
    487,
    120,
    29,
    258,
    232,
    70,
    99,
    24,
    94,
    43,
    79,
    189,
    69,
    362,
    177,
    331,
    361,
    225,
    194,
    145,
    91,
    87,
    251,
    109,
    281,
    265,
    214,
    509,
    126,
    260,
    407,
    479,
    434,
    320,
    13,
    330,
    417,
    505,
    38,
    375,
    369,
    277,
    452,
    175,
    73,
    463,
    363,
    495,
    210,
    31,
    321,
    316,
    269,
    205,
    192,
    489,
    292,
    193,
    241,
    124,
    485,
    280,
    16,
    295,
    206,
    215,
    6,
    21,
    164,
    76,
    85,
    5,
    398,
    305,
    377,
    472,
    324,
    309,
    151,
    240,
    236,
    213,
    93,
    448,
    209,
    490,
    201,
    190,
    118,
    351,
    311,
    431,
    301,
    184,
    74,
    494,
    101,
    420,
    142,
    383,
    185,
    60,
    246,
    323,
    394,
    12,
    249,
    44,
    187,
    454,
    179,
    108,
    294,
    169,
    127,
    451,
    379,
    49,
    158,
    395,
    77,
    319,
    2,
    166,
    380,
    504,
    461,
    168,
    144,
    483,
    186,
    1,
    62,
    313,
    199,
    415,
    318,
    53,
    386,
    174,
    235,
    349,
    0,
    212,
    328,
    141,
    384,
    327,
    499,
    389,
    371,
    293,
    507,
    35,
    442,
    247,
    159,
    9,
    267,
    496,
    347,
    477,
    17,
    261,
    170,
    385,
    30,
    136,
    259,
    178,
    237,
    421,
    263,
    138,
    298,
    302,
    229,
    430,
    425,
    506,
    176,
    83,
    89,
    469,
    173,
    218,
    317,
    157,
    457,
    50,
    217,
    322,
    282,
    234,
    387,
    476,
    480,
    100,
    471,
    503,
    388,
    204,
    340,
    436,
    163,
    152,
    161,
    92,
    270,
    80,
    226,
    314,
    372,
    374,
    264,
    203,
    128,
    458,
    231,
    140,
    81,
    211,
    466,
    358,
    160,
    123,
    23,
    408,
    456,
    112,
    248,
    286,
    262,
    343,
    67,
    150,
    182,
    180,
    26,
    325,
    427,
    276,
    303,
    254,
    134,
    297,
    40,
    198,
    498,
    356,
    114,
    181,
    14,
    42,
    332,
    207,
    96,
    341,
    54,
    346,
    155,
    482,
    253,
    233,
    196,
    268,
    139,
    284,
    464,
    492,
    82,
    58,
    148,
    510,
    143,
    202,
    243,
    130,
    390,
    501,
    10,
    493,
    131,
    266,
    405,
    411,
    424,
    413,
    51,
    344,
    252,
    345,
    440,
    47,
    429,
    71,
    98,
    257,
    445,
    382,
    329,
    228,
    18,
    426,
    432,
    278,
    245,
    56,
    86,
    88,
    46,
    20,
    132,
    285,
    497,
    397,
    366,
    459,
    25,
    455,
    3,
    153,
    304,
    283,
    230,
    105,
    34,
    191,
    399,
    443,
    15,
    273,
    381,
    121,
    37,
    75,
    312,
    227,
    475,
    437,
    242,
    22,
    287,
    52,
    368,
    486,
    8,
    59,
    484,
    414,
    115,
    367,
    391,
    111,
    359,
    256,
    167,
    474,
    491,
    403,
    274,
    423,
    508,
    473,
    406,
    357,
    378,
    418,
    306,
    188,
    219,
    116,
    244,
    402,
    337,
    500,
    412,
    428,
    353,
    104,
    308,
    447,
    355,
    444,
    435,
    171,
    338,
    364,
    39,
    352,
    446,
    441,
    360,
    36,
    310,
    32,
    90,
    122,
    433,
    326,
    275,
    33,
    195,
    106,
    221,
    28,
    419,
    300,
    299,
    223]

@[expose] def encGen : List Gen → ℕ
  | [] => 0
  | g :: w => (match g with | .x => 0 | .y => 1) + 4 * encGen w

@[expose] def conjAB (k : Fin 512) : ℕ :=
  BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15)
    (encGen (InvRep.conjWord k)) (InvRep.conjWord k).length

@[expose] def i1Chk (k : Fin 512) : Bool :=
  if k.val = 0 then eqN (D.ThM3_RB 25) D.ThS_ONE
  else if k.val = 1 then eqN (D.ThM3_RB 26) (D.ThM3_RB 16)
  else if (List.lookup k.val InvRep.conjTable).isSome then
    eqN (mulB D.ThS_c D.ThS_rm (conjAB D k) (D.ThM3_RB 17))
      (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (25 + k.val)) (conjAB D k))
  else neN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (25 + k.val)) (D.ThM3_RB (25 + k.val))) D.ThS_ONE

@[expose] def xNfB (k : Fin 512) : ℕ := mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB (25 + k.val))

@[expose] def i2Chk (k : Fin 512) : Bool :=
  if (List.lookup k.val InvRep.uTable).isSome then
    eqN (mulB D.ThS_c D.ThS_rm (D.ThM3_RB (25 + (InvRep.uIdx k).val)) (D.ThM3_RB 13))
      (mulB D.ThS_c D.ThS_rm (xNfB D k) (D.ThM3_RB (25 + (InvRep.uIdx k).val)))
  else neN (mulB D.ThS_c D.ThS_rm (xNfB D k) (xNfB D k)) D.ThS_ONE

@[expose] def dNfB (k : Fin 512) : ℕ := mulB D.ThS_c D.ThS_rm (D.ThM3_RB 547) (D.ThM3_RB (25 + k.val))

@[expose] def i3Chk (k : Fin 512) : Bool := neN (mulB D.ThS_c D.ThS_rm (dNfB D k) (dNfB D k)) D.ThS_ONE

@[expose] def segPre : List Bool :=
  [(CFSG.KC.Th.BigS.constsOK D.ThS_c D.ThS_rm D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThS_up D.ThS_dg D.ThS_ONE),
   (CFSG.KC.Th.SeedS.decOK D.ThSeed_SA D.ThSeed_LA),
   (CFSG.KC.Th.SeedS.decOK D.ThSeed_SB D.ThSeed_LB),
   (CFSG.KC.Th.SeedS.packOK D.ThSeed_SF CFSG.KC.Th.SeedS.fcRowsList),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SA) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SB D.ThSeed_SB) D.ThSeed_SB) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SA) D.ThSeed_SF) D.ThSeed_SA) D.ThSeed_SF),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.trB D.ThS_tm0 D.ThS_tm1 D.ThS_tm2 D.ThS_tm3 D.ThS_tm4 D.ThS_tm5 D.ThS_tm6 D.ThS_tm7 D.ThSeed_SB) D.ThSeed_SF) D.ThSeed_SB) D.ThSeed_SF),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 0) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA D.ThSeed_SB)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 1) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) D.ThSeed_SB)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 2) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) (D.ThM3_RB 1))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 3) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) (D.ThM3_RB 2))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 4) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA (D.ThM3_RB 3))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 5) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 3) D.ThSeed_SA)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 6) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 5) 2 2) (D.ThM3_RB 4))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 7) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 3) (D.ThM3_RB 2))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 8) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 0) (D.ThM3_RB 7))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 9) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 8) (D.ThM3_RB 1))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 10) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA (D.ThM3_RB 9))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 11) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 9) D.ThSeed_SA)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 12) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 11) 18 5) (D.ThM3_RB 10))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 13) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 12) 14 4)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 14) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 4) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 6) 9 4))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 15) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 14) 5 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 16) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 84 4) 9 4)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 17) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 4 2) 6 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 18) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 1 2) 6 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 19) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 1109 6) 6 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 20) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 1332497 11) 7 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 21) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 1301 6) 6 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 22) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 348497 10) 4 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 23) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 5204 8) 6 3)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 24) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 345425 11) 7 3))]

@[expose] def segNF : List Bool := List.ofFn (nfReg D)

@[expose] def segPost : List Bool :=
  [(CFSG.KC.Th.Gen.eqN (D.ThM3_RB 537) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 19057059582225 23)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 538) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 18985115534676 23)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 539) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 19053621298513 24)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 540) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 93549828854853 24)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 541) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 296710378821 20)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 542) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 4747353674820 22)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 543) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 23437976604948 23)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 544) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 538) 2 2)) (D.ThM3_RB 537)) (D.ThM3_RB 539)) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 540) 2 2)) (D.ThM3_RB 539)) (D.ThM3_RB 541)) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 542) 2 2)) (D.ThM3_RB 541))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 545) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 537) 2 2) (D.ThM3_RB 538)) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 539) 2 2)) (D.ThM3_RB 538)) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 540) 2 2)) (D.ThM3_RB 541)) (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 542) 2 2)) (D.ThM3_RB 543))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 546) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB 18)) (D.ThM3_RB 13)) (D.ThM3_RB 18))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 547) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 5986089550763093 27)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 548) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB D.ThS_ONE 276 5)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 549) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB D.ThS_ONE 5445 8)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 550) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 549) (D.ThM3_RB 17)) (D.ThM3_RB 548)) D.ThSeed_SA) 9 4) (D.ThM3_RB 549))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 551) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB D.ThS_ONE 17896517 13)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 552) (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE D.ThSeed_SA D.ThSeed_SB D.ThS_ONE 1461653360965 21)),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 553) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 552) (D.ThM3_RB 13)) (D.ThM3_RB 551)) D.ThSeed_SA) 9 4) (D.ThM3_RB 552))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 554) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 18) (D.ThM3_RB 19))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 555) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 18) (D.ThM3_RB 22))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 556) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 18) (D.ThM3_RB 20)) (D.ThM3_RB 21))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 557) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 23))),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 558) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 21)))]

@[expose] def seg92 : List Bool :=
  [(CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 5) 3 2) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 11) 19 5) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB 13)) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 14) 6 3) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (D.ThM3_RB 16) D.ThSeed_SA),
   (CFSG.KC.Th.Gen.neN (D.ThM3_RB 16) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB 16)) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB 13)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB 16))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 16) (D.ThM3_RB 14)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 14) (D.ThM3_RB 16)))]

@[expose] def segQQ : List Bool := (List.ofFn fun i => [qqChk D i, zqChk D i]).flatten

@[expose] def segQC : List Bool := (List.ofFn fun i => List.ofFn (qcChk D i)).flatten

@[expose] def segXY : List Bool := (List.ofFn fun i => [xqChk D i, yqChk D i]).flatten

@[expose] def segND : List Bool :=
  List.zipWith (fun a b => ltN (D.ThM3_RB (25 + a)) (D.ThM3_RB (25 + b))) ndChain ndChain.tail

@[expose] def segMid : List Bool :=
  [(CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 537) 3 2) (D.ThM3_RB 25)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 538) 3 2) (D.ThM3_RB 25)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 539) 3 2) (D.ThM3_RB 25)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 540) 3 2) (D.ThM3_RB 26)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 541) 3 2) (D.ThM3_RB 26)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 542) 3 2) (D.ThM3_RB 26)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 543) 3 2) (D.ThM3_RB 25)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (D.ThM3_RB 538)) 2 2) (D.ThM3_RB 535)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (D.ThM3_RB 539)) 2 2) (D.ThM3_RB 398)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (D.ThM3_RB 540)) 2 2) (D.ThM3_RB 274)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (D.ThM3_RB 541)) 2 2) (D.ThM3_RB 348)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (D.ThM3_RB 542)) 2 2) (D.ThM3_RB 431)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 537) (D.ThM3_RB 543)) 2 2) (D.ThM3_RB 498)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 538) (D.ThM3_RB 539)) 2 2) (D.ThM3_RB 26)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 538) (D.ThM3_RB 540)) 2 2) (D.ThM3_RB 483)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 538) (D.ThM3_RB 541)) 2 2) (D.ThM3_RB 490)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 538) (D.ThM3_RB 542)) 2 2) (D.ThM3_RB 487)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 538) (D.ThM3_RB 543)) 2 2) (D.ThM3_RB 93)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 539) (D.ThM3_RB 540)) 2 2) (D.ThM3_RB 185)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 539) (D.ThM3_RB 541)) 2 2) (D.ThM3_RB 227)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 539) (D.ThM3_RB 542)) 2 2) (D.ThM3_RB 288)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 539) (D.ThM3_RB 543)) 2 2) (D.ThM3_RB 500)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 540) (D.ThM3_RB 541)) 2 2) (D.ThM3_RB 26)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 540) (D.ThM3_RB 542)) 2 2) (D.ThM3_RB 26)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 540) (D.ThM3_RB 543)) 2 2) (D.ThM3_RB 411)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 541) (D.ThM3_RB 542)) 2 2) (D.ThM3_RB 99)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 541) (D.ThM3_RB 543)) 2 2) (D.ThM3_RB 515)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 542) (D.ThM3_RB 543)) 2 2) (D.ThM3_RB 173)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 13) (D.ThM3_RB 544)) (D.ThM3_RB 324)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 15) (D.ThM3_RB 545)) (D.ThM3_RB 226)),
   (CFSG.KC.Th.Gen.neN (D.ThM3_RB 546) D.ThS_ONE),
   (CFSG.KC.Th.Gen.neN (D.ThM3_RB 546) (D.ThM3_RB 16)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 1352160579797152663358438253090 52) (D.ThM3_RB 16)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 4473924 12) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) D.ThS_ONE)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 17895696 14) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 18) D.ThS_ONE)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 85004562 14) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 19) D.ThS_ONE)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 340018248 16) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 16))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 1413760074 16) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 21) D.ThS_ONE)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 18539942178 18) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 22) D.ThS_ONE)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 5655040296 18) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 23) D.ThS_ONE)),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThM3_RB 13) (D.ThM3_RB 14) (D.ThM3_RB 15) 74159768712 20) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 16)))]

@[expose] def seg89 : List Bool := (List.ofFn fun k => [i1Chk D k, i2Chk D k, i3Chk D k]).flatten

@[expose] def segEnd : List Bool :=
  [(CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 550) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA (D.ThM3_RB 550))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 553) (D.ThM3_RB 13)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm D.ThSeed_SA (D.ThM3_RB 553))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 17)) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 554)) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 555)) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 24)) D.ThS_ONE),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 17))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 17))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 17))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 17))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 554))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 554))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 554))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 554))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 555))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 555))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 555))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 555))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 24))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 24))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 24))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 24))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 556) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 16)) (D.ThM3_RB 556))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 16)) (D.ThM3_RB 20))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 557) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 16)) (D.ThM3_RB 557))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 558) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 16)) (D.ThM3_RB 558))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 20))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 557) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 557))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 558) (D.ThM3_RB 17)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 17) (D.ThM3_RB 558))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 556) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 556))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 557) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 557))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 558) (D.ThM3_RB 554)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 554) (D.ThM3_RB 558))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 556) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 556))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 20))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 558) (D.ThM3_RB 555)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 555) (D.ThM3_RB 558))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 556) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 556))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 20) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 20))),
   (CFSG.KC.Th.Gen.eqN (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 557) (D.ThM3_RB 24)) (CFSG.KC.Th.mulB D.ThS_c D.ThS_rm (D.ThM3_RB 24) (D.ThM3_RB 557)))]

@[expose] def leaves : List Bool :=
  segPre D ++ segNF D ++ segPost D ++ seg92 D ++ segQQ D ++ segQC D ++ segXY D ++ segND D ++
    segMid D ++ seg89 D ++ segEnd D

theorem max3Chk_eq : max3Chk D = bal (leaves D) := by max3s_kernel_rfl

theorem leaves_true (h : max3Chk D = true) : ∀ b ∈ leaves D, b = true :=
  bal_true ((max3Chk_eq D).symm.trans h)

end CFSG.KC.Th.Max3S

end
