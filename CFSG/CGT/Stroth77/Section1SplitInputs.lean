module

public import CFSG.CGT.Stroth77.Section1SplitModel

public section

namespace CFSG.CGT.Stroth77

open Equiv Equiv.Perm

@[expose] def spVec (v : Vec6) (h : par v = 0) : Msp := Msp.mk v 1 h

@[expose] def spX1 : Msp := spVec ![0, 0, 1, 1, 0, 0] (by decide)
@[expose] def spY1 : Msp := spVec ![1, 1, 0, 0, 0, 0] (by decide)
@[expose] def spUV : Msp := spVec ![1, 0, 1, 0, 0, 0] (by decide)
@[expose] def spT : Msp := spVec ![1, 0, 0, 0, 1, 0] (by decide)
@[expose] def spX : Msp := Msp.ofPerm (swap 0 1 * swap 4 5)
@[expose] def spY : Msp := Msp.ofPerm (swap 2 3 * swap 4 5)
@[expose] def spW : Msp := Msp.ofPerm (swap 0 1 * swap 2 3 * swap 4 5)
@[expose] def spU : Msp := Msp.ofPerm (swap 0 2 * swap 1 3)
@[expose] def spRho : Msp := Msp.ofPerm (swap 0 2 * swap 0 4 * (swap 1 3 * swap 1 5))
@[expose] def spM1 : Msp := Msp.ofPerm (swap 3 4)
@[expose] def spM2 : Msp := Msp.ofPerm (swap 1 3 * swap 1 2)

@[expose] def gensTsp : List Msp := [spX1, spY1, spUV, spT, spX, spY, spU, spW]
@[expose] def gensAsp : List Msp := [spX1, spY1, spX, spY, spW]
@[expose] def gensEsp : List Msp := [spX1, spY1, spUV, spT]
@[expose] def gensAEsp : List Msp := [spX1, spY1, spX, spY, spW, spUV, spT]
@[expose] def gensDsp : List Msp := [spUV, spT, spU]

@[expose] def Tsp : Subgroup Msp := Subgroup.closure {g | g ∈ gensTsp}
@[expose] def Asp : Subgroup Msp := Subgroup.closure {g | g ∈ gensAsp}
@[expose] def Esp : Subgroup Msp := Subgroup.closure {g | g ∈ gensEsp}
@[expose] def AEsp : Subgroup Msp := Subgroup.closure {g | g ∈ gensAEsp}
@[expose] def Dsp : Subgroup Msp := Subgroup.closure {g | g ∈ gensDsp}

@[expose] def spBasis : Fin 5 → Msp := ![spX1, spY1, spX, spY, spW]

@[expose] def spPhi (r : Nat) : Msp :=
  (if r.testBit 0 then spX1 else 1) * (if r.testBit 1 then spY1 else 1) *
    (if r.testBit 2 then spX else 1) * (if r.testBit 3 then spY else 1) *
    (if r.testBit 4 then spW else 1)

variable {G : Type*} [Group G] [DecidableEq G]

end CFSG.CGT.Stroth77
