module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Coordinates

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem eq_zero_of_rootB_mul_eq {a b c d : K} (hb : h.bar b = b) {z : GL (Fin 4) K}
    (hz : z ∈ miyamotoZ h)
    (e : miyamotoXGL h 0 1 0 0 * miyamotoXGL h a b c d =
      miyamotoXGL h a b c d * miyamotoXGL h 0 1 0 0 * z) : a = 0 := by
  obtain ⟨d', -, rfl⟩ := hz
  rw [miyamotoXGL_mul h hb, miyamotoXGL_mul h (show h.bar (b + 1) = b + 1 by
    rw [map_add, hb, map_one]), miyamotoXGL_mul h (map_one _), miyamotoXGL_inj] at e
  obtain ⟨-, -, hc, -⟩ := e
  simpa using hc

theorem eq_zero_of_mul_rootA_eq {b c d : K} (hb : h.bar b = b) {z : GL (Fin 4) K}
    (hz : z ∈ miyamotoZ h)
    (e : miyamotoXGL h 0 b c d * miyamotoXGL h 1 0 0 0 =
      miyamotoXGL h 1 0 0 0 * miyamotoXGL h 0 b c d * z) : b = 0 := by
  obtain ⟨d', -, rfl⟩ := hz
  rw [miyamotoXGL_mul h hb, miyamotoXGL_mul h (map_zero _), miyamotoXGL_mul h (show
    h.bar (0 + b) = 0 + b by rw [zero_add, hb]), miyamotoXGL_inj] at e
  obtain ⟨-, -, hc, -⟩ := e
  simpa using hc

end CFSG.LocalAnalysis.EvenBN.U4
