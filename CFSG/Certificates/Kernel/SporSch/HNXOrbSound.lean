module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Local.HN.X.Lib

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX

theorem hnxCoreAt (T : Nat → Nat) (RB n MS CM3 M GA GB b c k b' c' k' : Nat)
    (h : Nat.beq (coreLeaf T RB n MS CM3 M GA GB b c) k = true) (e0 : b' = b) (e1 : c' = c)
    (e2 : k' = k) : Nat.beq (coreLeaf T RB n MS CM3 M GA GB b' c') k' = true := by
  subst e0 e1 e2
  exact h

theorem hnxSortAt (T : Nat → Nat) (RB n SG c SG' c' : Nat) (h : sortChunk T RB n SG c = true)
    (e0 : SG' = SG) (e1 : c' = c) : sortChunk T RB n SG' c' = true := by
  subst e0 e1
  exact h

theorem andB_left {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true := by
  revert h
  cases a <;> cases b <;> decide

theorem andB_right {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : b = true := by
  revert h
  cases a <;> cases b <;> decide

end CFSG.KS.SporSch

end
