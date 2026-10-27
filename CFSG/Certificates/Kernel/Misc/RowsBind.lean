module

public import Certificates.Data.Kernel.Misc.RowsBind
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Misc.ArrBind

public section

namespace CFSG.KC.Misc.ArrEnum

open CFSG.KS.Raw

theorem rowsBind_sound {n w : Nat} {P : Nat → Nat} : ∀ (rows : List (Array Nat)) (k : Nat),
    rowsBind n w P (rows.map Array.toList) k = true →
    rows = (List.range' k rows.length).map fun i => unpack n w (P i)
  | [], _, _ => rfl
  | r :: rs, k, h => by
    unfold rowsBind at h
    rw [List.map_cons, List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at h
    rw [List.length_cons, List.range'_succ, List.map_cons, ← rowsBind_sound rs (k + 1) h.2]
    rw [arrBind_sound (a := r) (n := n) (w := w) (P := P k) h.1]

theorem rowsBind_arr {A : Array (Array Nat)} {N n w : Nat} {P : Nat → Nat} (hN : A.size = N)
    (h : rowsBind n w P (A.toList.map Array.toList) 0 = true) :
    A = ((List.range N).map fun i => unpack n w (P i)).toArray := by
  apply Array.ext'
  rw [List.toList_toArray, List.range_eq_range', ← hN, ← Array.length_toList]
  exact rowsBind_sound _ 0 h

end CFSG.KC.Misc.ArrEnum

end
