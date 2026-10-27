module

public import Certificates.Data.Kernel.J4ZC9686

public section

namespace CFSG.KC.J4ZC9686

open CFSG.KC.J4Q (mulJ getN wordJ)
open CFSG.KC.J4R0 (wK)
open CFSG.Sporadic.J4.ZCent (perfW perfWord)

variable {c rm one : Nat}

theorem invOK_spec {B : List Nat} (h : invOK c rm one B = true) :
    ∀ n < 16, n ≠ 3 → n ≠ 4 → mulJ c rm (getN one B n) (getN one B n) = one := by
  intro n hn h3 h4
  simp only [invOK, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  rcases h n hn with (h1 | h1) | h1
  · exact absurd (Nat.eq_of_beq_eq_true h1) h3
  · exact absurd (Nat.eq_of_beq_eq_true h1) h4
  · exact Nat.eq_of_beq_eq_true h1

theorem perfOK_spec {B BI : List Nat} (h : perfOK c rm one B BI = true) :
    ∀ i < 16, wordJ c rm one B BI (perfWord (perfW.getD i [])) = getN one B i := by
  intro i hi
  simp only [perfOK, List.all_eq_true, List.mem_range] at h
  exact Nat.eq_of_beq_eq_true (h i hi)

theorem knOK_spec {X B T : List Nat} {q : Nat} {W : List (Nat × Nat)}
    (h : knOK c rm one X B T q W = true) :
    ∀ j < 16, (W.getD j (0, 0)).1 < 60 ∧ mulJ c rm q (getN one B j) =
      mulJ c rm (mulJ c rm (getN one T (W.getD j (0, 0)).1) (wK c rm one X (W.getD j (0, 0)).2 0 15))
        q := by
  intro j hj
  simp only [knOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h j hj
  rw [Nat.blt_eq] at h1
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

end CFSG.KC.J4ZC9686
