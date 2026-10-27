module

import CFSG.HardMathSupport.Dickson.BMRows.NotSqDvd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.LocalAnalysis.GLTheoremA

theorem prime_cases_B {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := by
  by_contra h
  push_neg at h
  obtain ⟨h3, h5, h7, h11⟩ := h
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem prime_cases_M {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ 17 ≤ p := by
  by_contra h
  push_neg at h
  obtain ⟨h3, h5, h7, h11, h13, h17⟩ := h
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

section All

theorem rows_B_all (h3 : I1416Rows.I1416SporRow .B 3) (h5 : I1416Rows.I1416SporRow .B 5)
    (h7 : I1416Rows.I1416SporRow .B 7) : ∀ p, I1416Rows.I1416SporRow .B p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_B hp hp2 with rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact row_B_of_eleven_le hp h S he hp hp2

theorem qrows_B_all (h3 : I1416QRows.I1416QRow .B 3) (h5 : I1416QRows.I1416QRow .B 5)
    (h7 : I1416QRows.I1416QRow .B 7) : ∀ p, I1416QRows.I1416QRow .B p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_B hp hp2 with rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact qrow_B_of_eleven_le hp h S he hp hp2

theorem arows_B_all (h3 : I1415Rows.I1415Row .B 3) (h5 : I1415Rows.I1415Row .B 5)
    (h7 : I1415Rows.I1415Row .B 7) : ∀ p, I1415Rows.I1415Row .B p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_B hp hp2 with rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact arow_B_of_eleven_le hp h S he hp hp2

theorem rows_M_all (h3 : I1416Rows.I1416SporRow .M 3) (h5 : I1416Rows.I1416SporRow .M 5)
    (h7 : I1416Rows.I1416SporRow .M 7) (h11 : I1416Rows.I1416SporRow .M 11)
    (h13 : I1416Rows.I1416SporRow .M 13) : ∀ p, I1416Rows.I1416SporRow .M p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_M hp hp2 with rfl | rfl | rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact h11 S he hp hp2
  · exact h13 S he hp hp2
  · exact row_M_of_seventeen_le hp h S he hp hp2

theorem qrows_M_all (h3 : I1416QRows.I1416QRow .M 3) (h5 : I1416QRows.I1416QRow .M 5)
    (h7 : I1416QRows.I1416QRow .M 7) (h11 : I1416QRows.I1416QRow .M 11)
    (h13 : I1416QRows.I1416QRow .M 13) : ∀ p, I1416QRows.I1416QRow .M p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_M hp hp2 with rfl | rfl | rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact h11 S he hp hp2
  · exact h13 S he hp hp2
  · exact qrow_M_of_seventeen_le hp h S he hp hp2

theorem arows_M_all (h3 : I1415Rows.I1415Row .M 3) (h5 : I1415Rows.I1415Row .M 5)
    (h7 : I1415Rows.I1415Row .M 7) (h11 : I1415Rows.I1415Row .M 11)
    (h13 : I1415Rows.I1415Row .M 13) : ∀ p, I1415Rows.I1415Row .M p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_M hp hp2 with rfl | rfl | rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact h11 S he hp hp2
  · exact h13 S he hp hp2
  · exact arow_M_of_seventeen_le hp h S he hp hp2

end All

end CFSG.HardMathSupport.Dickson.BMRows
