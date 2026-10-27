module

public import Certificates.Data.Kernel.ThCent.Rank
public import CFSG.Certificates.Kernel.ThCent.ListSound

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem rank7OK_sound {V : ℕ → ℕ} {Y : ℕ} {w : List ℕ} (h : rank7OK c rm ONE V Y w = true) :
    pkMat (wordR c rm ONE V w) * pkMat Y ≠ pkMat Y * pkMat (wordR c rm ONE V w) ∨
      pkMat (wordR c rm ONE V w) ^ 7 = 1 := by
  unfold rank7OK at h
  rw [strictF_eq] at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h1
  · left
    have := neB_sound hk h1
    rwa [pkMat_mulB hk, pkMat_mulB hk] at this
  · right
    rw [← pkMat_powB hk _ 7 3 (by norm_num), Nat.eq_of_beq_eq_true h1, pkMat_one hk]

theorem ord4OK_sound {V : ℕ → ℕ} {w : List ℕ} (h : ord4OK c rm ONE V w = true) :
    pkMat (wordR c rm ONE V w) ^ 4 = 1 ∧ pkMat (wordR c rm ONE V w) ^ 2 ≠ 1 := by
  unfold ord4OK at h
  rw [strictF_eq, strictF_eq] at h
  obtain ⟨h1, h2⟩ := andB_tt h
  have e2 : pkMat (mulB c rm (wordR c rm ONE V w) (wordR c rm ONE V w)) =
      pkMat (wordR c rm ONE V w) ^ 2 := by
    rw [pkMat_mulB hk, sq]
  refine ⟨?_, ?_⟩
  · have := congrArg pkMat (Nat.eq_of_beq_eq_true h1)
    rwa [pkMat_mulB hk, e2, pkMat_one hk, ← pow_add] at this
  · have := neB_sound hk h2
    rwa [e2, pkMat_one hk] at this

end CFSG.KC.ThCent

end
