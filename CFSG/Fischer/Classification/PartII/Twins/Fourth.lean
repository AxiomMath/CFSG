module

public import CFSG.Fischer.Classification.PartII.Twins.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2Twin

variable {H : Type} [Group H] {F : Set H}

theorem mul_mul_self (hP : Pair H F) {a : H} (ha : a ∈ F) (y : H) : a * (a * y) = y := by
  rw [← mul_assoc, Pair.mul_self hP ha, one_mul]

theorem mul_mul_mul_self (hP : Pair H F) {a b : H} (ha : a ∈ F) (hb : b ∈ F)
    (hab : a * b = b * a) : a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * a * (b * b) := by rw [← hab]; simp only [mul_assoc]
    _ = 1 := by rw [Pair.mul_self hP ha, Pair.mul_self hP hb, one_mul]

theorem conj_conj_of_mul_self {s : H} (hs : s * s = 1) (x : H) : s * (s * x * s) * s = x := by
  calc s * (s * x * s) * s = s * s * x * (s * s) := by simp only [mul_assoc]
    _ = x := by rw [hs, one_mul, mul_one]

theorem exists_not_commute_of_mem (hP : Pair H F) (hZ : Subgroup.center H = ⊥) {x : H}
    (hx : x ∈ F) : ∃ b ∈ F, x * b ≠ b * x := by
  by_contra! h
  have hc : x ∈ Subgroup.center H := (Pair.mem_center_iff hP).2 fun e he => (h e he).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact Pair.ne_one hP hx hc

theorem conj_conj_eq (hP : Pair H F) {a₂ a₃ b : H} (ha₂ : a₂ ∈ F) (ha₃ : a₃ ∈ F) (hb : b ∈ F)
    (h23 : a₂ * a₃ = a₃ * a₂) (hb₂ : a₂ * b ≠ b * a₂) :
    a₂ * a₃ * b * (a₂ * a₃) * a₂ * (a₂ * a₃ * b * (a₂ * a₃)) = a₃ * b * a₃ := by
  have hga : a₂ * a₃ * a₂ * (a₂ * a₃) = a₂ := by
    simp only [mul_assoc, mul_mul_self hP ha₂, Pair.mul_self hP ha₃, mul_one]
  calc a₂ * a₃ * b * (a₂ * a₃) * a₂ * (a₂ * a₃ * b * (a₂ * a₃))
      = a₂ * a₃ * (b * (a₂ * a₃ * a₂ * (a₂ * a₃)) * b) * (a₂ * a₃) := by simp only [mul_assoc]
    _ = a₂ * a₃ * (a₂ * b * a₂) * (a₂ * a₃) := by rw [hga, Pair.mul_mul_eq hP ha₂ hb hb₂]
    _ = a₃ * a₂ * (a₂ * b * a₂) * (a₂ * a₃) := by rw [h23]
    _ = a₃ * b * a₃ := by simp only [mul_assoc, mul_mul_self hP ha₂]

end O2Twin

variable {H : Type} [Group H] {F : Set H}

