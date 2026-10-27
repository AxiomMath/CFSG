module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeKit
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Sporadic.Schreier.Co3.Native

@[expose] def hypTuples : Array (Array Nat) :=
  #[#[0, 205, 535, 388, 165, 93], #[0, 343, 916, 1779, 1047, 1303],
    #[3, 730, 473, 1020, 1009, 1186], #[0, 606, 909, 1427, 1449, 364],
    #[11, 1425, 864, 130, 1164, 506], #[0, 1075, 1573, 1202, 62, 1286],
    #[0, 1260, 1642, 253, 1373, 280], #[3, 1227, 580, 1156, 1256, 1226],
    #[11, 1066, 178, 410, 932, 667], #[1, 1688, 1639, 165, 1578, 1186],
    #[1, 1283, 1257, 230, 87, 776], #[5, 696, 1611, 308, 1025, 768],
    #[4, 1736, 764, 547, 1675, 1019], #[11, 594, 831, 451, 1393, 1111],
    #[16, 1734, 364, 1508, 426, 530], #[39, 1430, 20, 570, 1706, 179],
    #[0, 205, 810, 1195, 881, 1707], #[12, 1504, 598, 979, 47, 683],
    #[19, 1337, 233, 328, 143, 1684], #[1, 764, 541, 581, 211, 660],
    #[0, 463, 366, 331, 1258, 1102], #[12, 98, 163, 782, 1607, 783], #[0, 393, 274, 725, 282, 1692],
    #[0, 568, 736, 1760, 604, 951], #[9, 1210, 104, 173, 1058, 845],
    #[3, 870, 1252, 1071, 548, 1595], #[11, 157, 1423, 1666, 777, 994],
    #[5, 1310, 1152, 713, 337, 373], #[1, 1525, 408, 751, 861, 1509], #[1, 1525, 436, 692, 861, 10],
    #[11, 932, 383, 939, 1066, 1525], #[0, 274, 393, 1546, 267, 1700],
    #[2, 179, 89, 1466, 587, 685], #[5, 1463, 1046, 566, 1677, 733],
    #[0, 1409, 171, 1523, 1730, 238], #[6, 167, 91, 1766, 1447, 533],
    #[61, 94, 423, 1685, 1567, 998], #[0, 568, 326, 1694, 736, 511],
    #[0, 1551, 1550, 791, 1258, 132], #[19, 474, 287, 374, 1167, 1516],
    #[5, 1255, 1259, 1571, 175, 214], #[6, 874, 1643, 50, 616, 1286],
    #[6, 1447, 653, 1684, 167, 935], #[11, 1109, 927, 252, 455, 419],
    #[13, 1572, 302, 1764, 108, 844], #[12, 1519, 385, 838, 182, 865],
    #[3, 1279, 279, 1775, 47, 614], #[2, 848, 514, 469, 1172, 1724],
    #[2, 648, 1039, 1781, 1091, 233], #[2, 555, 454, 1240, 1679, 92],
    #[2, 1180, 1163, 789, 275, 1583], #[13, 793, 706, 967, 461, 853],
    #[11, 708, 1135, 266, 1714, 222], #[3, 1120, 1209, 1762, 82, 784],
    #[4, 1079, 1122, 914, 1305, 1699], #[5, 1596, 616, 1450, 1051, 96],
    #[6, 1447, 696, 857, 167, 294], #[9, 257, 135, 1297, 754, 762], #[16, 204, 20, 467, 756, 686],
    #[4, 1473, 1695, 218, 512, 786], #[3, 960, 745, 986, 1426, 815],
    #[30, 1628, 534, 1339, 419, 891], #[2, 837, 955, 1038, 1489, 1126],
    #[90, 1723, 225, 1752, 1772, 257], #[4, 1587, 1608, 1411, 1621, 222],
    #[3, 710, 730, 1537, 155, 731], #[9, 500, 286, 284, 345, 2], #[2, 367, 688, 614, 232, 787],
    #[2, 555, 454, 1722, 1679, 32], #[61, 272, 1545, 646, 1242, 1447],
    #[44, 693, 1436, 1706, 216, 573], #[9, 397, 23, 859, 449, 1405], #[3, 633, 352, 151, 473, 421],
    #[3, 870, 548, 196, 571, 852], #[61, 1242, 1143, 669, 272, 284],
    #[5, 1051, 1596, 566, 1015, 544], #[3, 854, 112, 223, 965, 1356],
    #[9, 1210, 1684, 1497, 1696, 642], #[4, 169, 931, 303, 1725, 1781],
    #[14, 444, 727, 1585, 738, 1127], #[21, 190, 116, 541, 897, 179], #[2, 179, 587, 75, 1172, 725],
    #[6, 1758, 1181, 973, 156, 70], #[44, 1451, 941, 1736, 1190, 1069],
    #[16, 204, 1455, 999, 20, 805], #[5, 278, 122, 1435, 1585, 1194],
    #[13, 1572, 538, 654, 131, 682], #[44, 1053, 1587, 869, 1520, 970],
    #[12, 1504, 431, 1406, 1753, 1721], #[6, 672, 1330, 1257, 448, 344],
    #[6, 1357, 910, 1124, 1249, 570], #[2, 1453, 1663, 436, 1276, 1470],
    #[44, 1520, 1277, 425, 1053, 260], #[2, 837, 1489, 1613, 826, 1035],
    #[9, 1210, 91, 1311, 1684, 150], #[3, 1488, 1412, 1500, 838, 1554],
    #[6, 167, 1447, 1043, 203, 1613], #[11, 927, 505, 1579, 1109, 818],
    #[2, 1054, 1281, 808, 207, 1349], #[5, 372, 226, 1073, 696, 1235],
    #[3, 960, 1426, 1500, 542, 938], #[11, 1757, 1410, 1494, 1400, 1766],
    #[4, 310, 234, 1242, 1003, 963], #[14, 337, 1077, 189, 1208, 1346],
    #[5, 738, 872, 412, 1611, 974], #[5, 1431, 1317, 991, 227, 820], #[9, 32, 577, 225, 612, 936],
    #[3, 47, 1279, 1541, 40, 847], #[13, 793, 1032, 1103, 461, 1107],
    #[39, 418, 802, 1622, 1059, 1160], #[2, 207, 222, 852, 1679, 742],
    #[2, 367, 316, 436, 232, 1031], #[4, 1695, 284, 671, 1473, 739],
    #[2, 207, 1054, 1132, 1726, 1068], #[39, 142, 523, 140, 796, 440],
    #[19, 836, 551, 1559, 233, 22], #[4, 892, 443, 110, 1725, 236], #[6, 805, 29, 1179, 867, 84],
    #[5, 1310, 1463, 406, 1237, 563], #[3, 548, 870, 753, 926, 1741],
    #[4, 1736, 1675, 977, 371, 588]]

@[expose] def hypSrc : Array (Array Nat) :=
  #[#[0, 0, 2, 0, 2, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 2, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 2, 5],
    #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 2, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 2, 2, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 2, 2, 2, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 0, 2, 5], #[0, 0, 2, 0, 2, 5],
    #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 2, 2, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 2, 0, 2, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 2, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 2, 0, 5],
    #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 2, 4, 2], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 2, 5],
    #[0, 0, 2, 0, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 2, 0, 5],
    #[0, 0, 2, 0, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 2, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 2, 0, 2, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 2, 0, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 0, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 2, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 0, 5], #[0, 0, 2, 0, 2, 5], #[0, 0, 2, 2, 2, 5],
    #[0, 0, 2, 2, 0, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 2, 0, 2, 5], #[0, 0, 2, 2, 2, 5],
    #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5], #[0, 0, 0, 3, 3, 5],
    #[0, 0, 0, 3, 3, 5]]

@[expose] def hypK : Array (Array Nat) :=
  #[#[1, 51, 1, 54, 18, 64, 27, 9, 3, 1], #[1, 84, 168, 1, 99, 0, 81, 9, 3, 1],
    #[208, 153, 208, 189, 159, 0, 189, 9, 3, 1], #[1, 222, 111, 1, 21, 0, 108, 9, 3, 1],
    #[136, 195, 85, 54, 138, 1, 81, 27, 3, 1], #[1, 201, 159, 1, 3, 0, 27, 171, 3, 1],
    #[1, 144, 207, 1, 180, 0, 27, 90, 3, 1], #[208, 207, 85, 51, 144, 85, 81, 63, 3, 1],
    #[136, 240, 64, 102, 120, 64, 189, 171, 3, 1], #[1, 111, 64, 153, 222, 64, 108, 90, 3, 1],
    #[1, 84, 36, 234, 168, 36, 81, 36, 3, 1], #[39, 208, 39, 217, 109, 0, 108, 171, 3, 1],
    #[193, 39, 1, 75, 78, 1, 189, 90, 3, 1], #[136, 153, 1, 54, 198, 1, 81, 27, 9, 1],
    #[64, 72, 202, 27, 36, 202, 27, 9, 165, 1], #[64, 156, 64, 111, 138, 0, 27, 9, 84, 1],
    #[1, 51, 66, 1, 228, 0, 81, 9, 57, 1], #[208, 105, 174, 208, 66, 136, 189, 9, 165, 1],
    #[202, 234, 202, 186, 102, 85, 108, 9, 84, 1], #[1, 141, 202, 30, 192, 202, 81, 9, 30, 1],
    #[1, 78, 39, 1, 204, 0, 108, 9, 165, 1], #[208, 144, 39, 191, 207, 85, 189, 9, 84, 1],
    #[1, 135, 189, 1, 177, 0, 81, 27, 21, 1], #[1, 141, 192, 1, 165, 0, 27, 171, 165, 1],
    #[85, 54, 85, 84, 21, 1, 27, 90, 84, 1], #[208, 78, 202, 159, 39, 64, 81, 63, 57, 1],
    #[136, 135, 136, 87, 15, 64, 189, 171, 165, 1], #[39, 154, 39, 216, 63, 0, 108, 90, 84, 1],
    #[1, 36, 193, 102, 72, 52, 81, 36, 30, 1], #[1, 36, 52, 93, 72, 208, 108, 171, 165, 1],
    #[136, 120, 1, 150, 240, 1, 189, 90, 84, 1], #[1, 189, 135, 1, 162, 202, 81, 27, 12, 1],
    #[52, 39, 1, 114, 78, 1, 27, 90, 165, 1], #[39, 200, 39, 1, 126, 1, 27, 171, 84, 1],
    #[1, 72, 36, 1, 24, 0, 81, 36, 57, 1], #[36, 136, 202, 33, 191, 202, 189, 90, 165, 1],
    #[193, 72, 193, 99, 240, 1, 108, 171, 84, 1], #[1, 141, 112, 123, 192, 112, 81, 63, 30, 1],
    #[1, 63, 45, 1, 180, 0, 108, 90, 165, 1], #[202, 213, 85, 135, 147, 85, 189, 171, 84, 1],
    #[39, 72, 36, 39, 234, 0, 81, 27, 9, 3], #[36, 110, 202, 9, 217, 193, 27, 9, 3, 163],
    #[36, 191, 85, 78, 136, 39, 27, 9, 3, 82], #[136, 171, 99, 136, 6, 0, 81, 9, 3, 55],
    #[112, 204, 156, 112, 138, 0, 189, 9, 3, 163], #[208, 15, 85, 18, 21, 85, 108, 9, 3, 82],
    #[208, 24, 112, 90, 12, 52, 81, 9, 3, 28], #[52, 240, 120, 52, 117, 0, 108, 9, 3, 163],
    #[52, 150, 210, 52, 198, 0, 189, 9, 3, 82], #[52, 87, 165, 52, 192, 0, 81, 27, 3, 19],
    #[52, 177, 102, 52, 156, 0, 27, 171, 3, 163], #[112, 90, 112, 147, 150, 52, 27, 90, 3, 82],
    #[136, 147, 213, 136, 168, 0, 81, 63, 3, 55], #[208, 105, 174, 208, 123, 0, 189, 171, 3, 163],
    #[193, 108, 216, 193, 63, 0, 108, 90, 3, 82], #[39, 173, 36, 56, 100, 193, 81, 36, 3, 28],
    #[36, 191, 39, 83, 136, 64, 108, 171, 3, 163], #[85, 36, 39, 208, 72, 64, 189, 90, 3, 82],
    #[64, 219, 114, 64, 60, 0, 81, 27, 3, 10], #[193, 237, 123, 193, 27, 0, 27, 90, 3, 163],
    #[208, 228, 112, 156, 132, 136, 27, 171, 3, 82], #[52, 36, 39, 168, 72, 39, 81, 36, 3, 55],
    #[52, 183, 202, 72, 96, 36, 189, 90, 3, 163], #[36, 6, 85, 29, 3, 85, 108, 171, 3, 82],
    #[193, 162, 81, 193, 66, 0, 81, 63, 3, 28], #[208, 198, 153, 208, 48, 0, 108, 90, 3, 163],
    #[85, 117, 234, 85, 51, 0, 189, 171, 3, 82], #[52, 36, 72, 52, 162, 0, 81, 27, 9, 7],
    #[52, 87, 165, 52, 141, 85, 27, 9, 165, 163], #[193, 9, 36, 84, 18, 36, 27, 9, 84, 82],
    #[136, 195, 64, 204, 202, 156, 81, 9, 57, 55], #[85, 231, 129, 85, 135, 0, 189, 9, 165, 163],
    #[208, 126, 225, 208, 9, 0, 108, 9, 84, 82], #[208, 78, 39, 208, 201, 0, 81, 9, 30, 28],
    #[193, 18, 85, 69, 9, 85, 108, 9, 165, 163], #[39, 100, 173, 39, 46, 0, 189, 9, 84, 82],
    #[208, 21, 15, 208, 216, 0, 81, 27, 21, 19], #[85, 54, 27, 85, 93, 0, 27, 171, 165, 163],
    #[193, 195, 138, 193, 111, 0, 27, 90, 84, 82], #[39, 55, 39, 110, 74, 0, 81, 63, 57, 55],
    #[202, 117, 52, 111, 234, 52, 189, 171, 165, 163], #[52, 39, 78, 52, 180, 0, 108, 90, 84, 82],
    #[36, 56, 28, 36, 218, 0, 81, 36, 30, 28], #[136, 60, 193, 123, 30, 36, 108, 171, 165, 163],
    #[64, 219, 36, 21, 114, 36, 189, 90, 84, 82], #[39, 64, 47, 39, 81, 0, 81, 27, 12, 10],
    #[112, 204, 112, 177, 192, 0, 27, 90, 165, 163],
    #[136, 153, 193, 54, 198, 193, 27, 171, 84, 82], #[208, 105, 208, 231, 69, 193, 81, 36, 57, 55],
    #[36, 85, 170, 36, 31, 0, 189, 90, 165, 163], #[36, 89, 166, 36, 190, 0, 108, 171, 84, 82],
    #[52, 93, 186, 52, 111, 0, 81, 63, 30, 28], #[136, 198, 85, 12, 153, 85, 108, 90, 165, 163],
    #[52, 183, 96, 52, 84, 0, 189, 171, 84, 82], #[85, 54, 202, 36, 27, 193, 81, 27, 9, 4],
    #[208, 72, 36, 208, 129, 0, 27, 9, 84, 163], #[36, 136, 191, 36, 219, 0, 27, 9, 165, 82],
    #[136, 99, 52, 111, 171, 52, 81, 9, 30, 55], #[52, 48, 202, 123, 69, 202, 189, 9, 84, 163],
    #[39, 146, 64, 91, 208, 64, 108, 9, 165, 82], #[208, 228, 132, 208, 99, 0, 81, 9, 57, 28],
    #[136, 57, 33, 136, 108, 0, 108, 9, 84, 163], #[193, 18, 9, 193, 144, 0, 189, 9, 165, 82],
    #[39, 200, 39, 46, 38, 0, 81, 27, 12, 19], #[39, 83, 163, 39, 182, 0, 27, 171, 84, 163],
    #[39, 191, 136, 39, 19, 0, 27, 90, 165, 82], #[85, 30, 60, 85, 192, 0, 81, 63, 30, 55],
    #[208, 12, 24, 208, 117, 0, 189, 171, 84, 163], #[112, 90, 180, 112, 198, 0, 108, 90, 165, 82],
    #[64, 231, 52, 195, 129, 52, 81, 36, 57, 28], #[52, 69, 52, 216, 207, 64, 108, 171, 84, 163],
    #[52, 36, 52, 102, 126, 36, 189, 90, 165, 82], #[193, 123, 85, 210, 237, 112, 81, 27, 21, 10],
    #[52, 69, 48, 52, 201, 0, 27, 90, 84, 163], #[64, 114, 64, 15, 192, 136, 27, 171, 165, 82],
    #[202, 36, 202, 147, 132, 36, 81, 36, 30, 55], #[193, 72, 36, 193, 114, 0, 189, 90, 84, 163],
    #[36, 224, 112, 36, 142, 0, 108, 171, 165, 82], #[39, 154, 200, 39, 109, 0, 81, 63, 57, 28],
    #[208, 39, 78, 208, 90, 136, 108, 90, 84, 163], #[193, 39, 78, 193, 57, 0, 189, 171, 165, 82]]

@[expose] def lineTuples : Array (Array Nat) :=
  #[#[129, 1594, 1243, 183, 486, 1377], #[19, 1335, 49, 1353, 1218, 683],
    #[8, 665, 312, 962, 225, 344], #[1256, 285, 908, 208, 1002, 956],
    #[717, 370, 443, 554, 1107, 1183], #[1439, 1389, 1218, 938, 1280, 1114],
    #[957, 815, 1262, 1131, 1445, 823], #[468, 596, 901, 900, 274, 930],
    #[1701, 1196, 1522, 917, 326, 1714], #[1206, 80, 775, 561, 1067, 350],
    #[1475, 86, 1745, 321, 530, 273], #[1663, 1100, 523, 1041, 146, 678]]

@[expose] def transTuples : Array (Array Nat) :=
  #[#[0, 455, 651, 509, 68, 301], #[0, 4, 359, 120, 1386, 1259], #[166, 1351, 520, 1652, 1322, 369],
    #[1583, 1618, 1623, 871, 724, 508], #[0, 106, 154, 1259, 1715, 262],
    #[1291, 1463, 998, 1423, 1069, 379], #[725, 107, 560, 1295, 10, 1263],
    #[1376, 1026, 916, 296, 399, 121], #[1002, 960, 481, 1749, 1301, 697],
    #[1628, 322, 511, 532, 127, 1618], #[1271, 127, 80, 1063, 332, 1613],
    #[64, 1079, 1233, 353, 389, 1742]]

@[expose] def transToD : Array Bool :=
  #[true, true, false, false, true, false, true, false, false, false, false, false]

@[expose] def yTuple : Array Nat := #[1, 2, 0, 142, 3, 667]

@[expose] def cTuples : Array (Array Nat) :=
  #[#[320, 1758, 1292, 1217, 272, 1588], #[1676, 968, 605, 1271, 273, 462]]

@[expose] def yRels : List (Nat × Nat × Nat) := [(0, 1, 1), (0, 2, 2), (3, 4, 2)]

@[expose] def cKeys : List Nat := [0, 1, 2, 3]

@[expose] def levels (_ : Unit := ()) : Array Level :=
  rawLevels 1782 smallStrongArrs smallBaseNat.toArray

@[expose] def inP (L : Array Level) (g : Array Nat) : Bool :=
  siftA 1782 L smallBaseNat.toArray 0 g

@[expose] def qGensS (_ : Unit := ()) : Array (Array Nat) := qGens suzE81

@[expose] def qCertS (_ : Unit := ()) : ArrCert := qCert suzE81

@[expose] def dGens (_ : Unit := ()) : Array (Array Nat) :=
  (suzE81.dW[0]!).map (posWord 1782 (qGensS ()))

@[expose] def digit3 (k i : Nat) : Nat := k / 3 ^ i % 3

@[expose] def dProd (dg : Array (Array Nat)) (k : Nat) : Array Nat :=
  compA 1782 (powArr 1782 dg[0]! (digit3 k 0)) (compA 1782 (powArr 1782 dg[1]! (digit3 k 1))
    (compA 1782 (powArr 1782 dg[2]! (digit3 k 2)) (compA 1782 (powArr 1782 dg[3]! (digit3 k 3))
      (powArr 1782 dg[4]! (digit3 k 4)))))

@[expose] def dElts (_ : Unit := ()) : Array (Array Nat) :=
  Array.ofFn (n := 243) fun k => dProd (dGens ()) k.val

@[expose] def dot3 (m k : Nat) : Nat :=
  (digit3 m 0 * digit3 k 0 + digit3 m 1 * digit3 k 1 + digit3 m 2 * digit3 k 2 +
    digit3 m 3 * digit3 k 3 + digit3 m 4 * digit3 k 4) % 3

@[expose] def rebuild (L : Array Level) (beta : Array Nat) : Array Nat := Id.run do
  let mut acc := idA 1782
  let mut accI := idA 1782
  for i in [0:6] do
    let k := L[i]!.pos[accI[beta[i]!]!]!
    acc := compA 1782 acc L[i]!.tr[k]!
    accI := compA 1782 L[i]!.trInv[k]! accI
  return acc

@[expose] def inD (E : Array (Array Nat)) (t : Array Nat) : Bool :=
  anyLt 243 fun k => eqA 1782 t E[k]!

@[expose] def yArr (L : Array Level) : Array Nat := rebuild L yTuple

@[expose] def cGens (L : Array Level) : Array (Array Nat) :=
  #[yArr L, rebuild L cTuples[0]!, rebuild L cTuples[1]!]

@[expose] def cCert (L : Array Level) : ArrCert := enumBfs 1782 (cGens L) cKeys 3300

@[expose] def lineArr (L : Array Level) (j : Nat) : Array Nat := rebuild L lineTuples[j]!

@[expose] def transArr (L : Array Level) (j : Nat) : Array Nat := rebuild L transTuples[j]!

@[expose] def hypG (L : Array Level) : Array (Array Nat) := hypTuples.map (rebuild L)

@[expose] def hypY (L : Array Level) (E : Array (Array Nat)) : Array (Array (Array Nat)) :=
  ((hypG L).zip hypK).map fun gk => gk.2.map fun k => conjInvA 1782 gk.1 E[k]!

@[expose] def relsOf (src : Array Nat) (ys : Array (Array Nat)) :
    Array (Option (Nat × Array Nat)) :=
  Array.ofFn (n := 6) fun l => if src[l.val]! < l.val then some (src[l.val]!, ys[l.val]!) else none

@[expose] def fltOf (src : Array Nat) (ys : Array (Array Nat)) : Array (Option (Array Nat)) :=
  Array.ofFn (n := 6) fun l => if src[l.val]! < l.val then none else some ys[l.val]!

@[expose] def predOf (ys : Array (Array Nat)) (a : Array Nat) : Bool :=
  allLt 4 fun t => commA 1782 a ys[t + 6]!

@[expose] def hleaves (L : Array Level) (src : Array Nat) (ys : Array (Array Nat)) :
    List (Array Nat) :=
  SuzT.fsearch 1782 L smallBaseNat.toArray (relsOf src ys) (fltOf src ys) (predOf ys) 6 0
    (idA 1782) (idA 1782)

@[expose] def commCount (E : Array (Array Nat)) (w : Array Nat) : Nat :=
  ((Finset.range E.size).filter fun j =>
    ((E[j]!)[w[0]!]! == w[(E[j]!)[0]!]! && commA 1782 E[j]! w) = true).card

@[expose] def qCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let gs := qGensS ()
  let c := qCertS ()
  enumOK 1782 gs suzE81.qKeys c && c.pts.size == 2187 && allLt gs.size fun k => inP L gs[k]!

@[expose] def dCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let dg := dGens ()
  let E := dElts ()
  dg.size == 5 &&
  allLt 5 (fun i => validA 1782 dg[i]! && inP L dg[i]! &&
    eqA 1782 (powArr 1782 dg[i]! 3) (idA 1782)) &&
  allLt 5 (fun i => allLt 5 fun j => commA 1782 dg[i]! dg[j]!) &&
  allLt 243 (fun k => allLt 243 fun k' => k == k' || !(eqA 1782 E[k]! E[k']!))

@[expose] def hypCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let E := dElts ()
  let G := hypG L
  let Y := hypY L E
  G.size == 121 && Y.size == 121 && hypSrc.size == 121 && hypK.size == 121 &&
  parLt 121 8 (fun j => validA 1782 G[j]! && inP L G[j]! && (hypSrc[j]!).size == 6 &&
    (hypK[j]!).size == 10 && (Y[j]!).size == 10 &&
    allLt 10 (fun t => decide ((hypK[j]!)[t]! < 243)) &&
    allLt 6 (fun l => decide ((hypSrc[j]!)[l]! ≤ l) &&
      ((Y[j]!)[l]!)[smallBaseNat.toArray[(hypSrc[j]!)[l]!]!]! == smallBaseNat.toArray[l]!) &&
    decide ((hleaves L hypSrc[j]! Y[j]!).length ≤ 243)) &&
  allLt 243 (fun m => m == 0 || anyLt 121 fun j => allLt 10 fun t => dot3 m (hypK[j]!)[t]! == 0)

@[expose] def fusCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let c := qCertS ()
  let E := dElts ()
  let Ls := Array.ofFn (n := 12) fun j => lineArr L j.val
  let Ls2 := Ls.map fun x => compA 1782 x x
  c.pts.size == 2187 &&
  allLt 2187 fun k =>
    let t := c.pts[k]!
    !(eqA 1782 (powArr 1782 t 3) (idA 1782)) || eqA 1782 t (idA 1782) || inD E t ||
      anyLt 2187 fun u =>
        let x := conjA 1782 c.pts[u]! t
        anyLt 12 fun j => eqA 1782 x Ls[j]! || eqA 1782 x Ls2[j]!

@[expose] def transCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let E := dElts ()
  let y := yArr L
  allLt 12 fun j =>
    let h := transArr L j
    let x := lineArr L j
    let z := conjA 1782 h x
    validA 1782 h && validA 1782 x && inP L h &&
      (if transToD.getD j false then inD E z else eqA 1782 z y)

@[expose] def cCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let y := yArr L
  validA 1782 y && inP L y && eqA 1782 (powArr 1782 y 3) (idA 1782) &&
    !(eqA 1782 y (idA 1782)) &&
    centOKP 3 1782 smallStrongArrs smallBaseNat.toArray y yRels (cGens L) cKeys (cCert L) 3240

@[expose] def classCheck (_ : Unit := ()) : Bool :=
  let E := (cCert (levels ())).pts
  allLt E.size fun i =>
    let w := E[i]!
    eqA 1782 w (idA 1782) ||
      !(eqA 1782 (powArr 1782 w 2) (idA 1782) || eqA 1782 (powArr 1782 w 5) (idA 1782)) ||
      decide (commCount E w < 81)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
