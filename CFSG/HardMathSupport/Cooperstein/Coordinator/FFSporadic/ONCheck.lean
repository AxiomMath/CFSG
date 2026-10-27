module

public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.ON.Data

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.F3.Native CFSG.Sporadic.ON.Native

set_option compiler.extract_closed false

@[expose] def onHeisProg : List (List Nat) := [
    [1, 2], [3, 2], [4, 4], [5, 5], [6, 6], [7, 7], [8, 8], [6, 9], [10, 2], [11, 5], [3, 3],
    [13, 13], [14, 14], [13, 15], [16, 1], [17, 3], [12, 12], [12, 19],
    [18, 18, 12, 18, 12, 18, 18, 18, 12, 18, 12], [21, 21], [22, 22],
    [12, 18, 12, 12, 18, 12, 12, 12, 18, 12, 12], [24, 24], [25, 25],
    [23, 23, 23, 23, 23, 23, 26, 26, 26, 26, 26, 26, 23, 26],
    [18, 18, 12, 18, 18, 12, 18, 18, 12, 12, 18],
    [20, 18, 20, 20, 20, 20, 18, 20, 20, 28, 12, 12, 18, 12, 12, 12, 12, 18, 12]]

@[expose] def onHeisX : Nat := 23

@[expose] def onHeisY : Nat := 26

@[expose] def onHeisZ : Nat := 27

@[expose] def onHeisG : Nat := 29

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
