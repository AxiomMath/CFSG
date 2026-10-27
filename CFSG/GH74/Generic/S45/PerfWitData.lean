module

public import CFSG.GH74.Generic.S45.PerfWitCheck
public meta import CFSG.GH74.Generic.S45.PerfWitCheck

public section

namespace CFSG.GH74.Generic.S45

@[expose] def j3PerfWit2A : PerfWit where
  comms := [
    ([-5, 2], [3]),
    ([-4, -4, 3], [2, 3, -5]),
    ([5, -4, -4], [-4, 5]),
    ([-2, -5, -2, 4, 3], [-2]),
    ([2, 5], [2])]
  four := [5]

@[expose] def mclPerfWitIn : PerfWit where
  comms := [
    ([2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2], [2, 2, 2, 1, -2, -2, 1, -2, -2]),
    ([-2, 1, -2, -2, 1, -2, -2, 1, -2, -2, -2, 1, 2, 1, 2], [1, -2, -2, 1])]
  four := [1, 2, 1, -2]

@[expose] def mclPerfWitOut : PerfWit where
  comms := [
    ([-3, 2, 3], [1]),
    ([3, 2, -3], [3, 4]),
    ([-3, 2, -1, 2], [1]),
    ([-3, 2, 3], [4])]
  four := [1, -4]

@[expose] def j2PerfWit2A : PerfWit where
  comms := [
    ([2, -3, 1], [2, -3]),
    ([1, 3, 2], [1, 3]),
    ([2, -3, 1, 2], [4, 3, -4]),
    ([1, -4, -3], [2, -3, 1])]
  four := [1, 2]

end CFSG.GH74.Generic.S45
