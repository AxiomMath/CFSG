module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

theorem linearIndependent_of_pairing {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (v : ι → V) (φ : ι → Module.Dual k V)
    (hE : IsUnit (Matrix.of fun i j => φ i (v j))) : LinearIndependent k v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmul : Matrix.mulVec (Matrix.of fun i j => φ i (v j)) c
      = Matrix.mulVec (Matrix.of fun i j => φ i (v j)) 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    have h1 : φ i (∑ j, c j • v j) = φ i 0 := by rw [hc]
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h1
    have h2 : ∑ j, (Matrix.of fun i j => φ i (v j)) i j * c j = ∑ j, c j * φ i (v j) :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact h2.trans h1
  have hc0 : c = 0 := Matrix.mulVec_injective_iff_isUnit.2 hE hmul
  intro i
  simp [hc0]

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
