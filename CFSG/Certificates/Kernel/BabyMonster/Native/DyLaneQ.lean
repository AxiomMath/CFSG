module

public import CFSG.Certificates.Kernel.BabyMonster.Native.F2n
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BM

open CFSG.KC.YModel

@[expose] noncomputable def lnQE (Q : List (List Nat)) (s : Nat) : List Nat :=
  if s < 18 then lgetL Q s
  else if s = 18 then dropLastL (lgetL Q 18)
  else if s < 68 then consN (lastL (lgetL Q (s - 1))) (dropLastL (lgetL Q s))
  else consN (lastL (lgetL Q 67)) (lgetL Q 68)

@[expose] noncomputable def lnQuot (f : Nat) (C Q : List (List Nat)) (s : Nat) : Bool :=
  andB (andB (Nat.beq (lenL (lgetL C s)) (rowsSn 4371 s)) (Nat.beq (lenL (lgetL Q s)) (rowsS s)))
    (quotBlk 1197 f s (lgetL C s) (lnQE Q s))

end CFSG.KC.BM

end
