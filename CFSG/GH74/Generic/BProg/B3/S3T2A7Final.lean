module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7Asm
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Rows
public import CFSG.GH74.Generic.BProg.B3.S3T2A7L3
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Alt
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocSpor
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocEven
public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocL34

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup

theorem lem125p2_of_open (hA9 : Cell125 Alt9) (hL2 : Cell125 OddL2) (hU33 : Cell125 U33)
    (hSp : Cell125 OddSp4) (hG2 : Cell125 OddG2) (hD4 : Cell125 Odd3D4)
    (hL4m : Cell125 OddL4m) (hL4p : Cell125 OddL4p) : Lem125p2 :=
  lem125p2_of_cells (cell125_of_locBal1For S3T2A7Loc.locBal1For_sporGH)
    (cell125_of_locBal1For S3T2A7Loc.locBal1For_even2GH) S3T2A7Loc.cell125_L34
    (cell125_of_locBal1For locBal1For_alt810) hA9 hL2 (cell125_oddL3 hU33) hSp hG2 hD4
    (cell125_oddL4_of hL4m hL4p) cell125_oddL5 cell125_ree

end CFSG.GH74.Generic.BProg.B3.S3T2A7
