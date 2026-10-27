module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem card_center_cj [Finite Y] (g : Y) (H : Subgroup Y) :
    Nat.card (Subgroup.center ↥(cj g H)) = Nat.card (Subgroup.center ↥H) := by
  let e : ↥H ≃* ↥(cj g H) := (MulAut.conj g).subgroupMap H
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem cj_fix_of_comm {K : Subgroup Y} {b w : Y} (hbw : b * w = w * b)
    (hbN : cj b K = K) : cj b (cj w K) = cj w K := by
  rw [← cj_mul, hbw, cj_mul, hbN]

theorem x_cube_identities {x : Y} (hx3 : x ^ 3 = 1) :
    x * (x * x) = 1 ∧ (x * x) * (x * x) = x := by
  constructor
  · calc x * (x * x) = x ^ 3 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, mul_assoc]
      _ = 1 := hx3
  · calc (x * x) * (x * x) = x ^ 4 := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = x := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hx3, one_mul]

theorem cj_xx_of_cj_x {K : Subgroup Y} (x : Y) : cj x (cj x K) = cj (x * x) K :=
  (cj_mul x x K).symm

end CFSG.LocalAnalysis.GLTheoremA.I114
