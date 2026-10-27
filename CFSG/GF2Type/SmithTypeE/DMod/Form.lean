module

public import CFSG.GF2Type.SmithTypeE.DMod.Code

public section

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

@[expose] def fVal (v w : V) : ZMod 2 := ∑ t : Fin 32, v t * w (Fin.rev t)

@[expose] noncomputable def fModel : LinearMap.BilinForm (ZMod 2) V :=
  LinearMap.mk₂ (ZMod 2) fVal
    (fun v v' w => by
      simp only [fVal, Pi.add_apply, add_mul, ← Finset.sum_add_distrib])
    (fun c v w => by
      simp only [fVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun v w w' => by
      simp only [fVal, Pi.add_apply, mul_add, ← Finset.sum_add_distrib])
    (fun c v w => by
      simp only [fVal, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem fModel_apply (v w : V) : fModel v w = fVal v w := rfl

theorem fModel_decode (u v : Nat) : fModel (decode32 u) (decode32 v) = bit (fB u v) := by
  rw [fModel_apply, fVal, fB, bit_foldl, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h : (Fin.rev t).val = 31 - t.val := by
    rw [Fin.val_rev]
    omega
  simp only [decode32_apply_bit, bit_and, h]

theorem fModel_single (v : V) (s : Fin 32) : fModel v (Pi.single s 1) = v (Fin.rev s) := by
  rw [fModel_apply, fVal, Finset.sum_eq_single (Fin.rev s)]
  · simp
  · intro b _ hb
    have : Fin.rev b ≠ s := fun h => hb (by rw [← h, Fin.rev_rev])
    simp [this]
  · simp

theorem fModel_nondegenerate {v : V} (h : ∀ w, fModel v w = 0) : v = 0 := by
  funext m
  have := h (Pi.single (Fin.rev m) 1)
  rw [fModel_single, Fin.rev_rev] at this
  exact this

end CFSG.GF2Type.SmithTypeE.DMod
