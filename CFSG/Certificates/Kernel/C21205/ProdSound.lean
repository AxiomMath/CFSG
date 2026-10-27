module

public import Certificates.Data.Kernel.C21205.Prod
public import CFSG.Certificates.Kernel.C21205.SylowSound

public section

namespace CFSG.KC.C21205

open CFSG.LargeExtraspecial.AS35QCo CFSG.LargeExtraspecial.AS35QCo.Native CFSG.KS.PK
  CFSG.KC.Misc.Spec CFSG.KC.Ord CFSG.KC.LQT.P

theorem beq_eq_natBeq (a b : ℕ) : (a == b) = Nat.beq a b := rfl

theorem bigOrderK_eq (x : ℕ) : bigOrderK x = bigOrder x := by
  rw [bigOrderK, bigOrder]
  simp only [mulK_eq, andB_eq, notB_eq, beq_eq_natBeq, Bool.and_assoc]

theorem prod_shape (w wi r : ℕ) :
    (andB (isSpK w) <| andB (Nat.beq (mulK w wi) idc) <| andB (Nat.beq (mulK wi w) idc)
      (bigOrderK (mulK r (mulK (mulK w r) wi)))) =
    (isSp w && mulc w wi == idc && mulc wi w == idc && bigOrder (mulc r (mulc (mulc w r) wi))) := by
  rw [bigOrderK_eq, isSpK_eq]
  simp only [mulK_eq, andB_eq, beq_eq_natBeq, Bool.and_assoc]

theorem prodOK_of_prodK {k : ℕ} (h : prodK k = true) : prodOK k = true := by
  rw [prodK, prod_shape] at h
  rw [prodOK]
  exact h

end CFSG.KC.C21205

end
