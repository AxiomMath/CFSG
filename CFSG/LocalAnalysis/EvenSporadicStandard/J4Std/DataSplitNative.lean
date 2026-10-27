module

public import CFSG.Sporadic.J4.QTMask

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataSplit

open CFSG.Sporadic.J4.QT

@[expose] def letterOf (k : Fin 6) : Int := letters.getD k 0

@[expose] def splitWords : List (List (Fin 6)) :=
  [[0, 3], [1, 4], [2, 5], [0, 0, 1, 1, 0, 0, 2, 0, 2, 3, 2, 1, 5],
    [0, 0, 2, 2, 2, 4, 0, 4, 4, 5, 5, 1, 1, 0, 1]]

@[expose] def psiRows : List (List Nat) :=
  [[356, 352, 17, 1024, 160, 1, 10, 832, 41, 6, 784],
   [0, 512, 0, 16, 512, 48, 8, 0, 8, 8, 2],
   [0, 0, 0, 0, 0, 0, 256, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 512, 4, 1, 0, 0, 0, 0, 4, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

@[expose] def cmRows : List (List (List Nat)) :=
  [[[1853, 356, 531, 1975, 85, 1055, 1780, 1696, 248, 1548, 1803],
    [672, 1485, 1723, 597, 92, 1101, 71, 1460, 689, 758, 1138],
    [2042, 1514, 874, 700, 1236, 512, 1304, 1490, 1138, 362, 85],
    [498, 1206, 1785, 1162, 1126, 2011, 228, 1679, 454, 290, 956],
    [1788, 100, 1085, 1753, 1569, 673, 2032, 1828, 364, 1692, 804]],
   [[2018, 1697, 702, 1173, 233, 2004, 2034, 1713, 861, 531, 249],
    [1994, 27, 1484, 1208, 956, 284, 887, 767, 1773, 1723, 838],
    [454, 460, 1646, 1862, 403, 1641, 1218, 1732, 1915, 874, 608],
    [236, 1154, 857, 675, 848, 674, 119, 1049, 374, 1785, 971],
    [1757, 465, 346, 644, 1529, 773, 1168, 1939, 1183, 1085, 918]],
   [[1816, 207, 915, 1229, 1818, 347, 920, 125, 582, 248, 1196],
    [441, 1911, 1184, 1612, 1660, 1727, 1740, 829, 800, 1707, 922],
    [501, 927, 1586, 1371, 32, 1295, 1577, 756, 16, 589, 163],
    [1768, 389, 766, 1316, 298, 230, 802, 157, 671, 454, 1230],
    [1339, 1865, 1051, 682, 1170, 1268, 1026, 915, 1081, 934, 799]],
   [[665, 1855, 1220, 63, 372, 988, 327, 659, 1443, 1463, 1040],
    [993, 672, 1252, 1722, 1485, 1003, 1668, 1723, 618, 597, 1186],
    [562, 2042, 914, 1055, 1514, 118, 319, 874, 233, 700, 511],
    [396, 498, 1733, 67, 1206, 1338, 670, 1785, 237, 1162, 155],
    [749, 1788, 1189, 1288, 100, 1196, 1464, 1085, 1884, 1753, 608]],
   [[172, 1004, 2018, 1305, 1149, 1697, 482, 473, 702, 1896, 233],
    [1858, 1231, 1998, 1263, 318, 59, 786, 643, 1228, 764, 1980],
    [1208, 208, 454, 1656, 914, 460, 1630, 1514, 1646, 814, 403],
    [1965, 1441, 236, 1864, 1022, 1154, 34, 397, 857, 1428, 848],
    [440, 1227, 1757, 1003, 911, 465, 1336, 1870, 346, 221, 1529]],
   [[1971, 404, 1441, 1816, 248, 1409, 207, 1404, 1886, 1593, 1211],
    [1797, 1805, 2026, 441, 1707, 689, 1911, 7, 748, 2019, 472],
    [2023, 1309, 525, 509, 605, 1260, 991, 1653, 617, 1455, 59],
    [373, 355, 1409, 1768, 454, 1385, 389, 861, 2010, 1699, 1125],
    [1665, 1863, 1611, 1339, 934, 155, 1865, 1659, 1713, 1715, 1498]]]

@[expose] def pOne : List Nat := (List.range 11).map (2 ^ ·)

@[expose] def pZero : List Nat := List.replicate 11 0

@[expose] def pLetter (k : Fin 6) : List Nat := (List.range 11).map (letterRow (letterOf k))

@[expose] def pMul (X Y : List Nat) : List Nat :=
  (List.range 11).map fun i => rowsXor (fun j => Y.getD j 0) 11 (X.getD i 0)

@[expose] def pAdd (X Y : List Nat) : List Nat :=
  (List.range 11).map fun i => X.getD i 0 ^^^ Y.getD i 0

@[expose] def pPair (k' : Fin 6) : List (Fin 6) → List Nat × List Nat
  | [] => (pOne, pZero)
  | k :: r =>
    let p := pPair k' r
    (pMul p.1 (pLetter k), pAdd p.2 (if k' = k then p.1 else pZero))

@[expose] def dualRhs (k k' : Fin 6) : List Nat :=
  pAdd (pMul (pAdd pOne (pLetter k)) (psiRows.getD k' []))
    ((List.range 5).foldl (fun acc r =>
      pAdd acc (pMul ((cmRows.getD k []).getD r []) (pPair k' (splitWords.getD r [])).2)) pZero)

@[expose] def chkRel : Bool :=
  splitWords.all fun w => (List.range 11).all fun j => (w.map letterOf).foldr act (2 ^ j) == 2 ^ j

@[expose] def chkDual : Bool :=
  (List.finRange 6).all fun k => (List.finRange 6).all fun k' =>
    (if k = k' then pOne else pZero) == dualRhs k k'

@[expose] def chkSplit : Bool := chkRel && chkDual

end CFSG.EvenSporadicStandard.J4Std.DataSplit
