module

import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Census.ToMain

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert

theorem canon1_pc {n w p q : Nat} (hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w) :
    canon1 n w (pc n w p q) = true := by
  rcases Nat.eq_zero_or_pos w with rfl | hw0
  · have hm : CFSG.KS.mask 0 = 0 := rfl
    rcases (by simp at hw; omega : n = 0 ∨ n = 1) with rfl | rfl
    · rfl
    · unfold canon1 pc
      change Nat.beq (Nat.shiftRight (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight p
        (Nat.mul 0 (Nat.land (Nat.shiftRight q (Nat.mul 0 0)) (CFSG.KS.mask 0))))
        (CFSG.KS.mask 0)) (Nat.mul 0 0)) (CFSG.KS.PackFld.pcR 1 0 (CFSG.KS.mask 0) p q 31 1 0))
        (1 * 0)) 0 = true
      rw [hm]
      change Nat.beq (Nat.shiftRight (Nat.lor (Nat.shiftLeft (_ &&& 0) (Nat.mul 0 0))
        (CFSG.KS.PackFld.pcR 1 0 0 p q 31 1 0)) (1 * 0)) 0 = true
      have hz : CFSG.KS.PackFld.pcR 1 0 0 p q 31 1 0 = 0 := by
        rw [CFSG.KS.PackFld.pcR_succ]
        rfl
      rw [Nat.and_zero, hz]
      rfl
  · have h := CFSG.KS.PackFld.pcomp_shr (p := p) (q := q) hn hw0
    unfold canon1 pc
    rw [show Nat.shiftRight (pcomp n w (CFSG.KS.mask w) p q) (n * w) = 0 from h]
    rfl

end CFSG.KC.Census
