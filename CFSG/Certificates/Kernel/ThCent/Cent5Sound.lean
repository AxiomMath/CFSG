module

public import Certificates.Data.Kernel.ThCent.Cent5
public import CFSG.Certificates.Kernel.ThCent.ListSound

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem letterOK_sound {R Ri X Y C i j k i' j' k' : ℕ} (hi : i < 8) (hj : j < 8) (hk' : k < 8)
    (hi' : i' < 8) (hj' : j' < 8) (hk'' : k' < 8)
    (h : letterOK c rm ONE R Ri X Y C i j k i' j' k' = true) :
    pkMat R * pkMat Ri = 1 ∧
      pkMat R * pkMat X * pkMat Ri = pkMat X ^ i * pkMat Y ^ j * pkMat C ^ k ∧
      pkMat R * pkMat Y * pkMat Ri = pkMat X ^ i' * pkMat Y ^ j' * pkMat C ^ k' := by
  unfold letterOK at h
  obtain ⟨h1, h⟩ := andB_tt h
  obtain ⟨h2, h3⟩ := andB_tt h
  have e1 := congrArg pkMat (Nat.eq_of_beq_eq_true h1)
  have e2 := congrArg pkMat (Nat.eq_of_beq_eq_true h2)
  have e3 := congrArg pkMat (Nat.eq_of_beq_eq_true h3)
  rw [pkMat_mulB hk, pkMat_one hk] at e1
  rw [pkMat_mulB hk, pkMat_mulB hk, pkMat_cubeP hk hi hj hk'] at e2
  rw [pkMat_mulB hk, pkMat_mulB hk, pkMat_cubeP hk hi' hj' hk''] at e3
  exact ⟨e1, e2, e3⟩

theorem cent5OK_sound {V : ℕ → ℕ} {X Y C : ℕ} {w : List ℕ}
    (h : cent5OK c rm ONE V X Y C w = true) :
    pkMat (wordR c rm ONE V w) * pkMat X ≠ pkMat X * pkMat (wordR c rm ONE V w) ∨
      pkMat (wordR c rm ONE V w) * pkMat Y ≠ pkMat Y * pkMat (wordR c rm ONE V w) ∨
      ∃ k < 5, pkMat (wordR c rm ONE V w) = pkMat C ^ k := by
  unfold cent5OK at h
  rw [strictF_eq] at h
  rcases Bool.or_eq_true_iff.1 h with h1 | h
  · left
    have := neB_sound hk h1
    rwa [pkMat_mulB hk, pkMat_mulB hk] at this
  rcases Bool.or_eq_true_iff.1 h with h1 | h1
  · right; left
    have := neB_sound hk h1
    rwa [pkMat_mulB hk, pkMat_mulB hk] at this
  · right; right
    obtain ⟨k, hk5, he⟩ := List.any_eq_true.1 h1
    have hk5' := List.mem_range.1 hk5
    refine ⟨k, hk5', ?_⟩
    rw [Nat.eq_of_beq_eq_true he, pkMat_powB hk _ _ 3 (by omega)]

end CFSG.KC.ThCent

end
