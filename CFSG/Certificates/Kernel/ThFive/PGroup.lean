module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.KC.ThFive

open CFSG.SectionRank.LocalWitness
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem y_pow_mul_x_pow {x y : G} {r : ℕ} (hr : 0 < r) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ r = 1) (i : ℕ) :
    ∀ j : ℕ, ∃ m : ℕ, y ^ j * x ^ i = x ^ i * y ^ j * ⁅x, y⁆ ^ m
  | 0 => ⟨0, by simp⟩
  | j + 1 => by
    obtain ⟨m, hm⟩ := y_pow_mul_x_pow hr hzx hzy hz i j
    refine ⟨(r - 1) * i + m, ?_⟩
    have hc : Commute (⁅x, y⁆ ^ ((r - 1) * i)) (y ^ j) := (hzy.pow_left _).pow_right _
    calc y ^ (j + 1) * x ^ i = y * (y ^ j * x ^ i) := by rw [pow_succ', mul_assoc]
      _ = (y * x ^ i) * y ^ j * ⁅x, y⁆ ^ m := by rw [hm]; simp only [mul_assoc]
      _ = x ^ i * y * (⁅x, y⁆ ^ ((r - 1) * i) * y ^ j) * ⁅x, y⁆ ^ m := by
        rw [y_mul_x_pow hr hzx hzy hz]; simp only [mul_assoc]
      _ = x ^ i * y * (y ^ j * ⁅x, y⁆ ^ ((r - 1) * i)) * ⁅x, y⁆ ^ m := by rw [hc.eq]
      _ = x ^ i * y ^ (j + 1) * ⁅x, y⁆ ^ ((r - 1) * i + m) := by
        rw [pow_succ' y j, pow_add]; simp only [mul_assoc]

theorem pair_pow {x y : G} {r : ℕ} (hr : 0 < r) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ r = 1) (i j : ℕ) :
    ∀ n : ℕ, ∃ m : ℕ, (x ^ i * y ^ j) ^ n = x ^ (i * n) * y ^ (j * n) * ⁅x, y⁆ ^ m
  | 0 => ⟨0, by simp⟩
  | n + 1 => by
    obtain ⟨m, hm⟩ := pair_pow hr hzx hzy hz i j n
    obtain ⟨m', hm'⟩ := y_pow_mul_x_pow hr hzx hzy hz i (j * n)
    refine ⟨m' + m, ?_⟩
    have hc : Commute (⁅x, y⁆ ^ m) (x ^ i * y ^ j) :=
      ((hzx.pow_right i).mul_right (hzy.pow_right j)).pow_left m
    have hc' : Commute (⁅x, y⁆ ^ m') (y ^ j) := (hzy.pow_right j).pow_left m'
    calc (x ^ i * y ^ j) ^ (n + 1) = (x ^ i * y ^ j) ^ n * (x ^ i * y ^ j) := pow_succ _ _
      _ = x ^ (i * n) * y ^ (j * n) * (⁅x, y⁆ ^ m * (x ^ i * y ^ j)) := by
        rw [hm]; simp only [mul_assoc]
      _ = x ^ (i * n) * y ^ (j * n) * ((x ^ i * y ^ j) * ⁅x, y⁆ ^ m) := by rw [hc.eq]
      _ = x ^ (i * n) * (y ^ (j * n) * x ^ i) * y ^ j * ⁅x, y⁆ ^ m := by simp only [mul_assoc]
      _ = x ^ (i * n) * (x ^ i * y ^ (j * n) * ⁅x, y⁆ ^ m') * y ^ j * ⁅x, y⁆ ^ m := by rw [hm']
      _ = x ^ (i * n) * x ^ i * y ^ (j * n) * (⁅x, y⁆ ^ m' * y ^ j) * ⁅x, y⁆ ^ m := by
        simp only [mul_assoc]
      _ = x ^ (i * n) * x ^ i * y ^ (j * n) * (y ^ j * ⁅x, y⁆ ^ m') * ⁅x, y⁆ ^ m := by rw [hc'.eq]
      _ = x ^ (i * (n + 1)) * y ^ (j * (n + 1)) * ⁅x, y⁆ ^ (m' + m) := by
        rw [mul_add i, mul_one, mul_add j, mul_one, pow_add x, pow_add y, pow_add ⁅x, y⁆]
        simp only [mul_assoc]

theorem isPGroup_closure_of_comm {p : ℕ} (hp : 0 < p) {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    IsPGroup p (Subgroup.closure ({x, y} : Set G)) := by
  have hz : ⁅x, y⁆ ^ p = 1 := by rw [commutator_pow_eq hzx, hx, commutatorElement_one_left]
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨i, j, k, -, -, -, hg⟩ := mem_closure_normalForm hp hx hy hzx hzy g.2
  obtain ⟨m, hm⟩ := pair_pow hp hzx hzy hz i j p
  have hc : Commute (x ^ i * y ^ j) (⁅x, y⁆ ^ k) :=
    (((hzx.pow_right i).mul_right (hzy.pow_right j)).pow_left k).symm
  have hgp : (g : G) ^ p = ⁅x, y⁆ ^ m := by
    rw [hg, hc.mul_pow, hm, ← pow_mul ⁅x, y⁆ k p, mul_comm k p, pow_mul ⁅x, y⁆ p k, hz,
      mul_comm i p, pow_mul x p i, hx, mul_comm j p, pow_mul y p j, hy]
    simp
  change (g : G) ^ p ^ 2 = 1
  rw [sq, pow_mul, hgp, ← pow_mul, mul_comm m p, pow_mul, hz, one_pow]

end CFSG.KC.ThFive

end
