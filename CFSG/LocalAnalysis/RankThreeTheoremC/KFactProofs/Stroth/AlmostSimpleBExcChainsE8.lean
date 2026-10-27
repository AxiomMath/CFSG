module

public import CFSG.Timmesfeld.Orders.ExceptionalWeylData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcVal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

@[expose] def excE8Step1 : OrbitCert .E8 where
  lam := 2290649240
  pts := [
    2290645160, 2290653288]
  parents := [
    1]
  table := [
    256, 0]
  lens := [
    0, 1]

@[expose] def excE8Step2 : OrbitCert .E8 where
  lam := 2290649240
  pts := [
    2290645160, 2290653288]
  parents := [
    1]
  table := [
    256, 1]
  lens := [
    0, 1]

@[expose] def excE8Step3 : OrbitCert .E8 where
  lam := 2290649480
  pts := [
    2290645639, 2290652809]
  parents := [
    2]
  table := [
    65536, 256]
  lens := [
    0, 1]

@[expose] def excE8Step4 : OrbitCert .E8 where
  lam := 2290649737
  pts := [
    2290641800, 2290652555, 2290653317]
  parents := [
    2, 16]
  table := [
    65536, 258, 131585]
  lens := [
    0, 1, 2]

@[expose] def excE8Step5 : OrbitCert .E8 where
  lam := 2290657432
  pts := [
    2290529928, 2290702776, 2290714968]
  parents := [
    3, 17]
  table := [
    16777216, 513, 33554690]
  lens := [
    0, 1, 2]

@[expose] def excE8Step6 : OrbitCert .E8 where
  lam := 2290657688
  pts := [
    2290526343, 2290641575, 2290649703, 2290648745, 2290656873, 2290772105]
  parents := [
    3, 17, 18, 34, 67]
  table := [
    16777216, 197120, 33816832, 50398208, 84017920, 67437824]
  lens := [
    0, 1, 2, 2, 3, 4]

@[expose] def excE8Step7 : OrbitCert .E8 where
  lam := 2290674874
  pts := [
    2290276488, 2290564568, 2290584888, 2290582493, 2290602813, 2290583763, 2290604083, 2290890893, 2290892163, 2290910088]
  parents := [
    3, 17, 18, 34, 48, 64, 67, 99, 130]
  table := [
    16777216, 197121, 33816834, 50398213, 117572358, 84215299,
    134612228, 67569416, 101255175, 151521545]
  lens := [
    0, 1, 2, 2, 3, 3, 4, 4, 5, 6]

@[expose] def excE8Step8 : OrbitCert .E8 where
  lam := 2290714760
  pts := [
    2289727624, 2291570824]
  parents := [
    4]
  table := [
    4294967296, 65793]
  lens := [
    0, 1]

@[expose] def excE8Step9 : OrbitCert .E8 where
  lam := 2290854040
  pts := [
    2287765128, 2291451528, 2291681992, 2291698248]
  parents := [
    4, 19, 33]
  table := [
    4294967296, 33554689, 8606712578, 12935234051]
  lens := [
    0, 1, 2, 3]

@[expose] def excE8Step10 : OrbitCert .E8 where
  lam := 2290788760
  pts := [
    2288683143, 2290526343, 2290641575, 2290649703, 2290648745, 2290656873, 2290772105, 2292615305]
  parents := [
    4, 19, 33, 34, 50, 83, 100]
  table := [
    4294967296, 33620224, 8606974720, 12935561728, 17247110400, 21575697408,
    30149051904, 25887704832]
  lens := [
    0, 1, 2, 3, 3, 4, 5, 6]

@[expose] def excE8Step11 : OrbitCert .E8 where
  lam := 2291697800
  pts := [
    2275903624, 2305394824]
  parents := [
    5]
  table := [
    1099511627776, 16843009]
  lens := [
    0, 1]

@[expose] def excE8Step12 : OrbitCert .E8 where
  lam := 2292811912
  pts := [
    2260236424, 2304473224, 2307238024]
  parents := [
    5, 20]
  table := [
    1099511627776, 8590000385, 2203318354434]
  lens := [
    0, 1, 2]

@[expose] def excE8Step13 : OrbitCert .E8 where
  lam := 2295048344
  pts := [
    2228782728, 2302510728, 2307118728, 2307406808, 2307427128]
  parents := [
    5, 20, 35, 49]
  table := [
    1099511627776, 8606712065, 2203368555010, 3311453340675, 4415293489924]
  lens := [
    0, 1, 2, 3, 4]

@[expose] def excE8Step14 : OrbitCert .E8 where
  lam := 2296167049
  pts := [
    2213054552, 2301528152, 2307057752, 2307403448, 2307424958, 2307426482]
  parents := [
    5, 20, 35, 50, 64]
  table := [
    1099511627776, 8606777345, 2203368685570, 3311453601795, 4415293685765, 5519117189124]
  lens := [
    0, 1, 2, 3, 4, 5]

@[expose] def excE8Step15 : OrbitCert .E8 where
  lam := 2292885912
  pts := [
    2259191943, 2288683143, 2290526343, 2290641575, 2290649703, 2290648745, 2290656873, 2290772105, 2292615305, 2322106505]
  parents := [
    5, 20, 35, 49, 50, 66, 99, 116, 133]
  table := [
    1099511627776, 8606777600, 2203368686080, 3311453668352, 4415293883136, 5519117059584,
    6622957274368, 7731042256640, 9925804165120, 8834899314944]
  lens := [
    0, 1, 2, 3, 4, 4, 5, 6, 7, 8]

@[expose] def excE8Step16 : OrbitCert .E8 where
  lam := 2307426440
  pts := [
    2054719624, 2526578824]
  parents := [
    6]
  table := [
    281474976710656, 4311810305]
  lens := [
    0, 1]

@[expose] def excE8Step17 : OrbitCert .E8 where
  lam := 2325252232
  pts := [
    1804044424, 2511833224, 2556070024]
  parents := [
    6, 21]
  table := [
    281474976710656, 2199040098561, 564049498735106]
  lens := [
    0, 1, 2]

@[expose] def excE8Step18 : OrbitCert .E8 where
  lam := 2343143560
  pts := [
    1552447624, 2496166024, 2555148424, 2558834824]
  parents := [
    6, 21, 36]
  table := [
    281474976710656, 2203318288641, 564062350082562, 847732055147267]
  lens := [
    0, 1, 2, 3]

@[expose] def excE8Step19 : OrbitCert .E8 where
  lam := 2378934424
  pts := [
    1049134728, 2464712328, 2553185928, 2558715528, 2559061224, 2559085608]
  parents := [
    6, 21, 36, 51, 65]
  table := [
    281474976710656, 2203335000321, 564062383505922, 847732122059523, 1130315183555844, 1412894000415749]
  lens := [
    0, 1, 2, 3, 4, 5]

@[expose] def excE8Step20 : OrbitCert .E8 where
  lam := 2559084680
  pts := [
    2810742920, 1770555528]
  parents := [
    7]
  table := [
    72057594037927936, 1103823437825]
  lens := [
    0, 1]

@[expose] def excE8Step21 : OrbitCert .E8 where
  lam := 2326440344
  pts := [
    1787332743, 2259191943, 2288683143, 2290526343, 2290641575, 2290649703, 2290648745, 2290656873, 2290772105, 2292615305, 2322106505, 2793965705]
  parents := [
    6, 21, 36, 51, 65, 66, 82, 115, 132, 149, 166]
  table := [
    281474976710656, 2203335065856, 564062383636992, 847732122256128, 1130315183949056, 1412894000874496,
    1695472800761600, 1978051617687040, 2260634679379968, 2544304417999104, 3106163466570240, 2826891824925440]
  lens := [
    0, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10]

@[expose] def excE8Step22 : OrbitCert .E8 where
  lam := 2559084680
  pts := [
    2810742920, 1770555528]
  parents := [
    7]
  table := [
    72057594037927936, 1103823438081]
  lens := [
    0, 1]

@[expose] def excE8Step23 : OrbitCert .E8 where
  lam := 2844297352
  pts := [
    3094907016, 1534625928, 2242414728]
  parents := [
    7, 22]
  table := [
    72057594037927936, 562954265231617, 144396671676187138]
  lens := [
    0, 1, 2]

@[expose] def excE8Step24 : OrbitCert .E8 where
  lam := 3130558600
  pts := [
    3364325512, 1283950728, 2227669128, 2286651528]
  parents := [
    7, 22, 37]
  table := [
    72057594037927936, 564049481892097, 144399961621135874, 217019406117700355]
  lens := [
    0, 1, 2, 3]

@[expose] def excE8Step25 : OrbitCert .E8 where
  lam := 3416885384
  pts := [
    3632822408, 1032353928, 2212001928, 2285729928, 2290337928]
  parents := [
    7, 22, 37, 52]
  table := [
    72057594037927936, 564053760082177, 144399970177516034, 217019423247237891, 289360686990230532]
  lens := [
    0, 1, 2, 3, 4]

@[expose] def excE8Step26 : OrbitCert .E8 where
  lam := 3989547160
  pts := [
    4169696904, 529041032, 2180548232, 2283767432, 2290218632, 2290621944, 2290650392]
  parents := [
    7, 22, 37, 52, 67, 81]
  table := [
    72057594037927936, 564053776793857, 144399970210939394, 217019423297372931, 289360687073854468, 361700864173278725,
    434041037028066566]
  lens := [
    0, 1, 2, 3, 4, 5, 6]

@[expose] def excE8Step27 : OrbitCert .E8 where
  lam := 2863311256
  pts := [
    2827520135, 1787332743, 2259191943, 2288683143, 2290526343, 2290641575, 2290649703, 2290648745, 2290656873, 2290772105, 2292615305, 2322106505, 2793965705, 1753778313]
  parents := [
    7, 22, 37, 52, 67, 81, 82, 98, 131, 148, 165, 182, 199]
  table := [
    72057594037927936, 564053776859392, 144399970211070464, 217019423297569536, 289360687074116608, 361700864173737472,
    434041037028590848, 506381209866405888, 578721382721259264, 651061559820880128, 723402823597427200, 796022276683926272,
    939858193118137344, 868364652857068800]
  lens := [
    0, 1, 2, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11, 12]

@[expose] def excE8Step28 : OrbitCert .E8 where
  lam := 3202136713
  pts := [
    2357758040, 3301476440, 3360458840, 1221101656, 3364145240, 1280084056, 3364375704, 1283770456, 2223802456, 3364390044, 1284000920, 2227488856, 3364391060, 1284015260,
    2227719320, 2286471256, 1284016276, 2227733660, 2286701720, 2227734676, 2286716060, 2290388120, 2286717076, 2290402460, 2290403476, 2290632924, 2290633940, 2290648280]
  parents := [
    6, 21, 23, 36, 39, 67, 71, 86, 98, 103, 118, 144, 151, 166,
    181, 199, 214, 229, 262, 277, 292, 309, 324, 356, 371, 387, 418]
  table := [
    281474976710656, 216174985448849409, 360852036868243458, 72907529461628931, 505533464909709316, 146370316573409285,
    722271413146812422, 291334319119990791, 577876970659381256, 939291931694202892, 436297252085760010, 794620386523938827,
    1156312450208628745, 653317770649927696, 1011640917822603278, 1085098194574966799, 870056814187642893, 1228660336875143187,
    1302118725873565714, 1373622157528203281, 1446800171111415830, 1519143616714833941, 1591480512492732436, 1663823962424279064,
    1736164139557453847, 1808504320918355994, 1880844493756497945, 1953184666627997723]
  lens := [
    0, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 8,
    8, 8, 9, 9, 10, 10, 11, 12]

@[expose] def excE8Coat0 : List (ChainStep .E8) := [
  ⟨254, 126, excE8Step27, [(7, 1), (2, 6)]⟩,
  ⟨126, 62, excE8Step21, [(6, 1), (2, 5)]⟩,
  ⟨62, 30, excE8Step15, [(5, 1), (2, 4)]⟩,
  ⟨30, 14, excE8Step10, [(4, 1), (2, 3)]⟩,
  ⟨14, 6, excE8Step6, [(3, 1), (2, 2)]⟩,
  ⟨6, 2, excE8Step3, [(2, 1)]⟩,
  ⟨2, 0, excE8Step1, [(2, 1)]⟩]

theorem excE8Coat0_check : chainCheck excE8Coat0 254 = true := by
  decide +kernel

@[expose] def excE8Coat1 : List (ChainStep .E8) := [
  ⟨253, 189, excE8Step28, [(7, 1), (4, 2)]⟩,
  ⟨189, 61, excE8Step20, [(2, 1)]⟩,
  ⟨61, 29, excE8Step14, [(6, 1)]⟩,
  ⟨29, 13, e8Cert4, [(5, 1)]⟩,
  ⟨13, 5, e8Cert3, [(4, 1)]⟩,
  ⟨5, 1, e8Cert2, [(3, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat1_check : chainCheck excE8Coat1 253 = true := by
  decide +kernel

@[expose] def excE8Coat2 : List (ChainStep .E8) := [
  ⟨251, 123, excE8Step26, [(7, 1)]⟩,
  ⟨123, 59, excE8Step19, [(6, 1)]⟩,
  ⟨59, 27, excE8Step13, [(5, 1)]⟩,
  ⟨27, 11, excE8Step9, [(4, 1)]⟩,
  ⟨11, 3, excE8Step5, [(3, 1)]⟩,
  ⟨3, 1, excE8Step2, [(2, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat2_check : chainCheck excE8Coat2 251 = true := by
  decide +kernel

@[expose] def excE8Coat3 : List (ChainStep .E8) := [
  ⟨247, 119, excE8Step25, [(5, 1)]⟩,
  ⟨119, 55, excE8Step18, [(4, 1)]⟩,
  ⟨55, 23, excE8Step12, [(3, 1)]⟩,
  ⟨23, 7, excE8Step8, [(2, 1)]⟩,
  ⟨7, 3, excE8Step4, [(3, 1)]⟩,
  ⟨3, 1, excE8Step2, [(2, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat3_check : chainCheck excE8Coat3 247 = true := by
  decide +kernel

@[expose] def excE8Coat4 : List (ChainStep .E8) := [
  ⟨239, 111, excE8Step24, [(4, 1)]⟩,
  ⟨111, 47, excE8Step17, [(3, 1)]⟩,
  ⟨47, 15, excE8Step11, [(2, 1)]⟩,
  ⟨15, 7, excE8Step7, [(5, 1), (2, 2)]⟩,
  ⟨7, 3, excE8Step4, [(3, 1)]⟩,
  ⟨3, 1, excE8Step2, [(2, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat4_check : chainCheck excE8Coat4 239 = true := by
  decide +kernel

@[expose] def excE8Coat5 : List (ChainStep .E8) := [
  ⟨223, 95, excE8Step23, [(3, 1)]⟩,
  ⟨95, 31, excE8Step16, [(2, 1)]⟩,
  ⟨31, 29, e8Cert5, [(2, 3), (8, 1)]⟩,
  ⟨29, 13, e8Cert4, [(5, 1)]⟩,
  ⟨13, 5, e8Cert3, [(4, 1)]⟩,
  ⟨5, 1, e8Cert2, [(3, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat5_check : chainCheck excE8Coat5 223 = true := by
  decide +kernel

@[expose] def excE8Coat6 : List (ChainStep .E8) := [
  ⟨191, 63, excE8Step22, [(2, 1)]⟩,
  ⟨63, 31, e8Cert6, [(9, 1), (3, 4)]⟩,
  ⟨31, 29, e8Cert5, [(2, 3), (8, 1)]⟩,
  ⟨29, 13, e8Cert4, [(5, 1)]⟩,
  ⟨13, 5, e8Cert3, [(4, 1)]⟩,
  ⟨5, 1, e8Cert2, [(3, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat6_check : chainCheck excE8Coat6 191 = true := by
  decide +kernel

@[expose] def excE8Coat7 : List (ChainStep .E8) := [
  ⟨127, 63, e8Cert7, [(2, 5), (2, 9), (14, 1)]⟩,
  ⟨63, 31, e8Cert6, [(9, 1), (3, 4)]⟩,
  ⟨31, 29, e8Cert5, [(2, 3), (8, 1)]⟩,
  ⟨29, 13, e8Cert4, [(5, 1)]⟩,
  ⟨13, 5, e8Cert3, [(4, 1)]⟩,
  ⟨5, 1, e8Cert2, [(3, 1)]⟩,
  ⟨1, 0, e8Cert1, [(2, 1)]⟩]

theorem excE8Coat7_check : chainCheck excE8Coat7 127 = true := by
  decide +kernel

@[expose] def excE8Mask : Fin Tag.E8.rank → ℕ := ![254, 253, 251, 247, 239, 223, 191, 127]

@[expose] def excE8Fac : Fin Tag.E8.rank → List (ℕ × ℕ) := ![
  [(7, 1), (2, 6), (6, 1), (2, 5), (5, 1), (2, 4), (4, 1), (2, 3), (3, 1), (2, 2), (2, 1), (2, 1)],
  [(7, 1), (4, 2), (2, 1), (6, 1), (5, 1), (4, 1), (3, 1), (2, 1)],
  [(7, 1), (6, 1), (5, 1), (4, 1), (3, 1), (2, 1), (2, 1)],
  [(5, 1), (4, 1), (3, 1), (2, 1), (3, 1), (2, 1), (2, 1)],
  [(4, 1), (3, 1), (2, 1), (5, 1), (2, 2), (3, 1), (2, 1), (2, 1)],
  [(3, 1), (2, 1), (2, 3), (8, 1), (5, 1), (4, 1), (3, 1), (2, 1)],
  [(2, 1), (9, 1), (3, 4), (2, 3), (8, 1), (5, 1), (4, 1), (3, 1), (2, 1)],
  [(2, 5), (2, 9), (14, 1), (9, 1), (3, 4), (2, 3), (8, 1), (5, 1), (4, 1), (3, 1), (2, 1)]]

@[expose] def excE8Full : List (ℕ × ℕ) := [(2, 1), (3, 1), (4, 1), (5, 1), (2, 3), (8, 1), (9, 1), (3, 4), (2, 5), (2, 9), (14, 1), (24, 1), (2, 10), (5, 6)]

theorem chainFactors_excE8Coat0 : chainFactors excE8Coat0 = [(7, 1), (2, 6), (6, 1), (2, 5), (5, 1), (2, 4), (4, 1), (2, 3), (3, 1), (2, 2), (2, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat1 : chainFactors excE8Coat1 = [(7, 1), (4, 2), (2, 1), (6, 1), (5, 1), (4, 1), (3, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat2 : chainFactors excE8Coat2 = [(7, 1), (6, 1), (5, 1), (4, 1), (3, 1), (2, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat3 : chainFactors excE8Coat3 = [(5, 1), (4, 1), (3, 1), (2, 1), (3, 1), (2, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat4 : chainFactors excE8Coat4 = [(4, 1), (3, 1), (2, 1), (5, 1), (2, 2), (3, 1), (2, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat5 : chainFactors excE8Coat5 = [(3, 1), (2, 1), (2, 3), (8, 1), (5, 1), (4, 1), (3, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat6 : chainFactors excE8Coat6 = [(2, 1), (9, 1), (3, 4), (2, 3), (8, 1), (5, 1), (4, 1), (3, 1), (2, 1)] := rfl

theorem chainFactors_excE8Coat7 : chainFactors excE8Coat7 = [(2, 5), (2, 9), (14, 1), (9, 1), (3, 4), (2, 3), (8, 1), (5, 1), (4, 1), (3, 1), (2, 1)] := rfl

theorem excE8Mask_cover : ∀ i k : Fin Tag.E8.rank, k ≠ i → k ∈ maskSet .E8 (excE8Mask i) := by
  decide

variable [Fintype (WeylGroup .E8)]

theorem parabolicSum_E8_univ_eq (q : ℕ) :
    parabolicSum .E8 Set.univ q = (excE8Full.map fun f => geomSum f.1 f.2 q).prod := by
  rw [parabolicSum_univ, sum_length_E8]
  simp only [excE8Full, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

theorem parabolicSum_E8_coat_eq (i : Fin Tag.E8.rank) (q : ℕ) :
    parabolicSum .E8 (maskSet .E8 (excE8Mask i)) q =
      ((excE8Fac i).map fun f => geomSum f.1 f.2 q).prod := by
  fin_cases i
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat0_check
    rw [chain_prod_eq, chainFactors_excE8Coat0] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat1_check
    rw [chain_prod_eq, chainFactors_excE8Coat1] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat2_check
    rw [chain_prod_eq, chainFactors_excE8Coat2] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat3_check
    rw [chain_prod_eq, chainFactors_excE8Coat3] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat4_check
    rw [chain_prod_eq, chainFactors_excE8Coat4] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat5_check
    rw [chain_prod_eq, chainFactors_excE8Coat5] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat6_check
    rw [chain_prod_eq, chainFactors_excE8Coat6] at h
    exact h
  · have h := parabolicSum_eq_of_chainCheck q _ _ excE8Coat7_check
    rw [chain_prod_eq, chainFactors_excE8Coat7] at h
    exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
