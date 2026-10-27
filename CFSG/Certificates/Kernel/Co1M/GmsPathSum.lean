module

public import Certificates.Data.Kernel.GmsPathK

public section

namespace CFSG.KC.GmsPath

open CFSG.KLie.CT

theorem sumN_add (f : Nat → Nat) (lo : Nat) :
    ∀ cnt, sumN (lo + cnt) f = sumN lo f + sumS lo cnt f := by
  intro cnt
  induction cnt with
  | zero => rfl
  | succ c ih =>
    change f (lo + c) + sumN (lo + c) f = sumN lo f + (f (Nat.add lo c) + sumS lo c f)
    rw [ih, Nat.add_eq]
    omega

theorem sum_chain {f : Nat → Nat} {lo acc cnt c : Nat} (h1 : sumN lo f = acc)
    (h2 : Nat.beq (sumS lo cnt f) c = true) : sumN (Nat.add lo cnt) f = Nat.add acc c := by
  rw [Nat.add_eq, Nat.add_eq, sumN_add, h1, Nat.eq_of_beq_eq_true h2]

end CFSG.KC.GmsPath

end
