module

public import CFSG.Sporadic.Co1Block.TwoAData
public import CFSG.Sporadic.Co1Block.Iota
public import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Co1Block.TwoAData
public meta import CFSG.Sporadic.Co1Block.IotaData
public meta import CFSG.Sporadic.Co1Block.Iota
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2

public section

set_option compiler.extract_closed false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative

@[expose, irreducible] def dispHeis0 : List (List Int) :=
  [
    [-2], [1], [5, 2], [6, 1], [7, 4], [8, 1], [9, 4], [10, 1], [11, 2], [12, 1], [13, 4], [14,
    1], [15, 4], [16, 1], [17, 4], [18, 1], [19, 4], [20, 1], [21, 2], [22, 1], [23, 4], [24, 1],
    [25, 2], [26, 1], [27, 2], [28, 1], [29, 2], [30, 1], [31, 2], [32, 1], [33, 4], [34, 1], [35,
    4], [36, 1], [37, 2], [38, 1], [39, 2], [40, 1], [41, 2], [42, 1], [43, 2], [44, 1], [45, 4],
    [46, 1], [47, 4], [48, 1], [49, 2], [50, 1], [51, 4], [52, 1], [53, 2], [54, 1], [55, 2], [56,
    1], [57, 2], [58, 1], [59, 4], [60, 1], [61, 2], [62, 1]]

@[expose, irreducible] def dispHeis1 : List (List Int) :=
  [
    [63, 4], [64, 1], [65, 4], [66, 1], [67, 2], [68, 1], [69, 4], [70, 1], [71, 2], [72, 1], [73,
    4], [74, 1], [75, 2], [76, 1], [77, 2], [78, 1], [79, 2], [80, 1], [81, 4], [82, 1], [83, 2],
    [84, 1], [85, 4], [86, 1], [87, 2], [88, 1], [89, 2], [90, 1], [91, 4], [92, 1], [93, 2], [94,
    1], [95, 4], [96, 1], [97, 2], [98, 1], [99, 2], [100, 1], [101, 4], [102, 1], [103, 4], [104,
    1], [105, 4], [106, 1], [107, 4], [108, 1], [109, 4], [110, 1], [111, 4], [112, 1], [113, 2],
    [114, 1], [115, 2], [116, 1], [117, 2], [118, 1], [119, 2], [120, 1], [121, 4], [122, 1]]

@[expose, irreducible] def dispHeis2 : List (List Int) :=
  [
    [123, 4], [4], [125, 1], [126, 2], [127, 1], [128, 2], [129, 1], [130, 4], [131, 1], [132, 4],
    [133, 1], [134, 4], [135, 1], [136, 4], [137, 1], [138, 4], [139, 1], [140, 2], [141, 1],
    [142, 4], [143, 1], [144, 2], [145, 1], [146, 4], [147, 1], [148, 4], [149, 1], [150, 4],
    [151, 1], [152, 2], [153, 1], [154, 4], [155, 1], [156, 2], [157, 1], [158, 4], [159, 1],
    [160, 2], [161, 1], [162, 4], [163, 1], [164, 4], [165, 1], [166, 2], [167, 1], [168, 4],
    [169, 1], [170, 4], [171, 1], [172, 2], [173, 1], [174, 4], [175, 1], [176, 2], [177, 1],
    [178, 4], [179, 1], [180, 4], [181, 1], [182, 2]]

@[expose, irreducible] def dispHeis3 : List (List Int) :=
  [
    [183, 1], [184, 4], [185, 1], [186, 4], [187, 1], [188, 4], [189, 1], [190, 2], [191, 1],
    [192, 4], [193, 1], [194, 2], [195, 1], [196, 4], [197, 1], [198, 2], [199, 1], [200, 4],
    [201, 1], [202, 2], [203, 1], [204, 4], [205, 1], [206, 2], [207, 1], [208, 4], [209, 1],
    [210, 4], [211, 1], [212, 2], [213, 1], [214, 2], [215, 1], [216, 4], [217, 1], [218, 4],
    [219, 1], [220, 4], [221, 1], [222, 2], [223, 1], [224, 2], [225, 1], [226, 4], [227, 1],
    [228, 2], [229, 1], [230, 2], [231, 1], [232, 2], [233, 1], [234, 2], [235, 1], [236, 2],
    [237, 1], [238, 4], [239, 1], [240, 2], [241, 1], [242, 2]]

@[expose, irreducible] def dispHeis4 : List (List Int) :=
  [
    [243, 1], [4], [245, 1], [246, 4], [247, 1], [248, 2], [249, 1], [250, 4], [251, 1], [252, 2],
    [253, 1], [254, 2], [255, 1], [256, 2], [257, 1], [258, 2], [259, 1], [260, 2], [261, 1],
    [262, 2], [263, 1], [264, 2], [265, 1], [266, 4], [267, 1], [268, 4], [269, 1], [270, 4],
    [271, 1], [272, 2], [273, 1], [274, 4], [275, 1], [276, 2], [277, 1], [278, 2], [279, 1],
    [280, 4], [281, 1], [282, 2], [283, 1], [284, 2], [285, 1], [286, 2], [287, 1], [288, 4],
    [289, 1], [290, 2], [291, 1], [292, 2], [293, 1], [294, 2], [295, 1], [296, 4], [297, 1],
    [298, 4], [299, 1], [300, 2], [301, 1], [302, 2]]

@[expose, irreducible] def dispHeis5 : List (List Int) :=
  [
    [303, 1], [304, 2], [305, 1], [306, 2], [307, 1], [308, 2], [309, 1], [310, 2], [311, 1],
    [312, 4], [313, 1], [314, 2], [315, 1], [316, 4], [317, 1], [318, 4], [319, 1], [320, 2],
    [321, 1], [322, 2], [323, 1], [324, 4], [325, 1], [326, 4], [327, 1], [328, 2], [329, 1],
    [330, 2], [331, 1], [332, 2], [333, 1], [334, 2], [335, 1], [336, 2], [337, 1], [338, 2],
    [339, 1], [340, 2], [341, 1], [342, 4], [343, 1], [344, 2], [345, 1], [346, 4], [347, 1],
    [348, 2], [349, 1], [350, 2], [351, 1], [352, 4], [353, 1], [354, 4], [355, 1], [356, 4],
    [357, 1], [358, 4], [359, 1], [360, 2], [361, 1], [362, 2]]

@[expose, irreducible] def dispHeis6 : List (List Int) :=
  [
    [363, 1], [124, 124], [364, 244], [365, 366], [367, 367], [-368], [-124], [369, 370], [371,
    368], [372, 124], [-244], [369, 374], [375, 368], [376, 244], [-373], [-377], [378, 379],
    [380, 373], [381, 377], [124, 364], [368, 368], [377, 382], [3, 2, 2, 3, 1, -2, -1, 1, -1, 1,
    2, -2, -1, -2, 3, 1, 3, -1, 1, -1, -2, 2, -1, -2, -1, 1, -1, 3, 3, -2, -1, -1, 1, 1, -1, -1,
    -1, -1, 2, 2, -1, 3, -1, -1, -1, -2, 2, 1, 2, -2, -1, -1, 2, 1, 2, 2, 3, 3, 1, 3], [386, 384,
    -386, 3], [387, 387], [388, 386], [389, 385, -389], [389, 373, -389]]

@[expose, irreducible] def dispDihD : List (List Int) :=
  [
    [-1, -2, -1, 1, 3, -1, -2, 2, -1, 2, -2, 2, -2, -2, -1, 3, 1, 3, 3, 1, 3, 3, -2, -1, -1, 1, 2,
    2, 3, -2, 2, -2, 3, 3, 3, 1, 2, 3, -2, -2], [-2, -2, -2, -2, -2, -1, 2, 3, 3, 2, -1, 1, -1,
    -1, 3, 2, -1, 1, -2, -1, 3, 1, -1, -2, 1, 3, -1, 1, -1, -1, 1, -2, -2, 3, 3, -1, 2, 1, -1, -1]]

@[expose, irreducible] def dispHeis : List (List Int) := dispHeis0 ++ dispHeis1 ++ dispHeis2 ++ dispHeis3 ++ dispHeis4 ++ dispHeis5 ++ dispHeis6

@[expose] def dispIX : Nat := 390

@[expose] def dispIY : Nat := 391

@[noinline, expose] def dispHeisCheck (_ : Unit := ()) : Bool :=
  let D := dag [aR, bR, iotaARows] dispHeis
  let a := iotaARows
  let X := D.1.getD (dispIX - 1) one
  let Y := D.1.getD (dispIY - 1) one
  let Xi := inv X
  let Yi := inv Y
  let W := mul (mul (mul Xi Yi) X) Y
  D.2.2 && mul X Xi == one && mul Y Yi == one && pow X 5 == one && pow Y 5 == one &&
    pow W 5 == one && W != one && validRows W && mul X W == mul W X && mul Y W == mul W Y &&
    mul a a == one && mul (mul a X) a == Xi

@[expose] def dispIC : Nat := 4

@[expose] def dispIA1 : Nat := 5

@[noinline, expose] def dispDihCheck (_ : Unit := ()) : Bool :=
  let D := dag [aR, bR, iotaCRows] dispDihD
  let cC := D.1.getD (dispIC - 1) one
  let cA := D.1.getD (dispIA1 - 1) one
  let pC := mul iotaCRows (mul cC (mul iotaCRows (inv cC)))
  let pA := mul aR (mul cA (mul aR (inv cA)))
  D.2.2 && mul cC (inv cC) == one && mul cA (inv cA) == one && pow pC 13 == one && pC != one &&
    validRows pC && pow pA 13 == one && pA != one && validRows pA

@[noinline, expose] def dispCheck (_ : Unit := ()) : Bool := dispHeisCheck () && dispDihCheck ()

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
