module

public import CFSG.CGT.T75M23.N7Class
public import CFSG.CGT.T75M23.N7Sem
public import CFSG.CGT.T75JM.N6Sem6

public section

namespace CFSG.CGT.T75M23

open CFSG.CGT.T75JM

variable {G : Type*} [Group G] {T : Subgroup G} (c : Coords T)

theorem modelX7_lt : ∀ i, modelX7.col i < 16 := by decide
theorem modelY7_lt : ∀ i, modelY7.col i < 16 := by decide

theorem tOf_15 : tOf c 15 = tOf c 1 * tOf c 2 * tOf c 4 * tOf c 8 := by
  rw [show (15 : ℕ) = ((1 ^^^ 2) ^^^ 4) ^^^ 8 by decide, tOf_mul c (by decide) (by decide),
    tOf_mul c (by decide) (by decide), tOf_mul c (by decide) (by decide)]

theorem tOf_6 : tOf c 6 = tOf c 2 * tOf c 4 := by
  rw [show (6 : ℕ) = 2 ^^^ 4 by decide, tOf_mul c (by decide) (by decide)]

theorem tOf_3 : tOf c 3 = tOf c 1 * tOf c 2 := by
  rw [show (3 : ℕ) = 1 ^^^ 2 by decide, tOf_mul c (by decide) (by decide)]

theorem sem7_of_data (g h : Subgroup.normalizer (T : Set G)) (hg : colsOf c g = modelX7)
    (hh : colsOf c h = modelY7) (x2 : g * g = 1) (y5 : h * h * h * h * h = 1)
    (r3 : (g * h * g * h⁻¹) ^ 3 = 1) (r4 : (h⁻¹ * g) ^ 7 = 1)
    (r5 : g * h * g * (h * g * h⁻¹ * g * h) ^ 2 * h * g * h⁻¹ = 1) :
    Sem7 ![g, h, tN c 0, tN c 1, tN c 2, tN c 3] := by
  have ax := act_eq c g modelX7 hg modelX7_lt
  have ay := act_eq c h modelY7 hh modelY7_lt
  refine ⟨x2, y5, r3, r4, r5, inN_sq c _, inN_sq c _, inN_sq c _, inN_sq c _, inN_comm c _ _,
    inN_comm c _ _, inN_comm c _ _, inN_comm c _ _, inN_comm c _ _, inN_comm c _ _, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show g * tN c 0 * g⁻¹ = tN c 0 * tN c 3
    refine (ax 0).trans ?_
    show inN (tOf c 9) = _
    rw [tOf_9 c, tN_0, tN_3, ← inN_mul]
  · show g * tN c 1 * g⁻¹ = tN c 1 * tN c 3
    refine (ax 1).trans ?_
    show inN (tOf c 10) = _
    rw [tOf_10 c, tN_1, tN_3, ← inN_mul]
  · show g * tN c 2 * g⁻¹ = tN c 0 * tN c 1 * tN c 2 * tN c 3
    refine (ax 2).trans ?_
    show inN (tOf c 15) = _
    rw [tOf_15 c, tN_0, tN_1, tN_2, tN_3, ← inN_mul, ← inN_mul, ← inN_mul]
  · show g * tN c 3 * g⁻¹ = tN c 3
    exact (ax 3).trans rfl
  · show h * tN c 0 * h⁻¹ = tN c 1
    exact (ay 0).trans rfl
  · show h * tN c 1 * h⁻¹ = tN c 1 * tN c 2
    refine (ay 1).trans ?_
    show inN (tOf c 6) = _
    rw [tOf_6 c, tN_1, tN_2, ← inN_mul]
  · show h * tN c 2 * h⁻¹ = tN c 1 * tN c 3
    refine (ay 2).trans ?_
    show inN (tOf c 10) = _
    rw [tOf_10 c, tN_1, tN_3, ← inN_mul]
  · show h * tN c 3 * h⁻¹ = tN c 0 * tN c 1
    refine (ay 3).trans ?_
    show inN (tOf c 3) = _
    rw [tOf_3 c, tN_0, tN_1, ← inN_mul]

end CFSG.CGT.T75M23
