
module

public import CFSG.Sporadic.Th.Max3.InvolutionsInputsBase

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

variable (A B : Array V4)

@[expose] def t3 : Array V4 := CFSG.Sporadic.Th.Native.mulRows A B

@[expose] def t4 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t3 A B) B

@[expose] def t5 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t3 A B) (t4 A B)

@[expose] def t6 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t3 A B) (t5 A B)

@[expose] def t7 : Array V4 := CFSG.Sporadic.Th.Native.mulRows A (t6 A B)

@[expose] def t8 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t6 A B) A

@[expose] def u : Array V4 := CFSG.Sporadic.Th.Native.mulRows (powRows (t8 A B) 2) (t7 A B)

@[expose] def s8 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t6 A B) (t5 A B)

@[expose] def s9 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t3 A B) (s8 A B)

@[expose] def s10 : Array V4 := CFSG.Sporadic.Th.Native.mulRows (s9 A B) (t4 A B)

@[expose] def s7 : Array V4 := CFSG.Sporadic.Th.Native.mulRows A (s10 A B)

@[expose] def s8' : Array V4 := CFSG.Sporadic.Th.Native.mulRows (s10 A B) A

@[expose] def v : Array V4 := CFSG.Sporadic.Th.Native.mulRows (powRows (s8' A B) 18) (s7 A B)

@[expose] def x : Array V4 := powRows (v A B) 14

@[expose] def y : Array V4 := CFSG.Sporadic.Th.Native.mulRows (t7 A B) (powRows (u A B) 9)

@[expose] def conj (k : Fin 512) : Array V4 := wordRows (x A B) (y A B) (InvRep.conjWord k)

end CFSG.KC.Th.Max3S

end
