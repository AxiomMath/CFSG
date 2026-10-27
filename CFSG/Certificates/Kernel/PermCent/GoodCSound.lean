module

public import Certificates.Data.Kernel.PermCent.GoodC

public section

namespace CFSG.Certificates.Kernel.PkCV.Good

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {n : Nat} [Small n]

theorem ordAux_C (o : CV n) (fuel k : Nat) : ordAux o fuel k = ordAuxC o fuel k := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih => simp only [ordAux, ordAuxC, powOneC_eq, Bool.cond_decide, ih]

theorem ordB_C (B : Nat) (o : CV n) : ordB B o = ordC B o := ordAux_C o B 1

theorem centB_C (L : List (CV n)) (t : CV n) : centB L t = centC L t := by
  simp only [centB, centC, eq22C_eq]

theorem noOddB_C (B : Nat) (C : List (CV n)) : noOddB B C = noOddC B C := by
  simp only [noOddB, noOddC, ordB_C]

theorem goodCheck_C (B : Nat) (L : List (CV n)) : goodCheck B L = goodC B L := by
  simp only [goodCheck, goodC, centB_C, noOddB_C, powOneC_eq, pow_two, Bool.decide_and, ne_eq,
    decide_not]

end CFSG.Certificates.Kernel.PkCV.Good

end
