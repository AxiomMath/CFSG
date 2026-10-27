module

public import Certificates.Data.Kernel.SporSch.Ru2254K
public import CFSG.Certificates.Kernel.SporSch.Ru2250Sound
import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit

public section

namespace CFSG.KS.Ru2254

open CFSG.KC.Enum CFSG.KS CFSG.Certificates.Native Finset

theorem fixedList_length_eq {n : Nat} {t : Array Nat} {f : Nat → Nat}
    (ht : ∀ x < n, t[x]! = f x) : (fixedList n t).length = fixCntK n f := by
  unfold fixedList fixCntK
  rw [CFSG.KS.SporSch.MBT.foldN_add' (g := fun x => if Nat.beq (f x) x = true then 1 else 0)
    (fun x s => by rw [Ru2250.nIf_eq]; rfl), Nat.zero_add, Ru2250.length_filter_range]
  refine sum_congr rfl fun x hx => ?_
  rw [ht x (mem_range.mp hx)]
  cases e : Nat.beq (f x) x
  · have : f x ≠ x := fun h => by rw [h, Nat.beq_refl] at e; exact absurd e (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true e]

end CFSG.KS.Ru2254

end
