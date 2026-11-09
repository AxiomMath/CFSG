module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Wit
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2 Matrix

theorem fixCount_eq_of_imgCheckW {t : ℕ} {X : ℕ → ℕ} (hinv : invPair t t = true)
    (hi : imgCheckW t X = true) : fixCount t = 64 := by
  classical
  have hM : toMatK t * toMatK t = 1 := by
    simp only [invPair, Bool.and_eq_true, beq_iff_eq] at hinv
    rw [← toMatK_mulK, hinv.1, toMatK_idK]
  have h2 : ∀ w : Vec12, w + w = 0 := fun w => funext fun i => CharTwo.add_self_eq_zero (w i)
  have hneg : ∀ w : Vec12, -w = w := fun w => funext fun i => ZMod.neg_eq_self_mod_two (w i)
  let f : Vec12 →ₗ[ZMod 2] Vec12 := Matrix.toLin' (toMatK t + 1)
  have hf : ∀ v, f v = toMatK t *ᵥ v + v := fun v => by
    simp only [f, Matrix.toLin'_apply, Matrix.add_mulVec, Matrix.one_mulVec]
  have hker : ∀ v, v ∈ LinearMap.ker f ↔ v ∈ fixM (toMatK t) := by
    intro v
    rw [LinearMap.mem_ker, hf, fixM, Set.mem_ofPred_eq, add_eq_zero_iff_eq_neg, hneg]
  have hrange : LinearMap.range f = LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, hf, hf, Matrix.mulVec_add, Matrix.mulVec_mulVec, hM,
        Matrix.one_mulVec]
      calc x + toMatK t *ᵥ x + (toMatK t *ᵥ x + x)
          = (x + x) + (toMatK t *ᵥ x + toMatK t *ᵥ x) := by abel
        _ = 0 := by rw [h2, h2, add_zero]
    · intro v hv
      rw [hker] at hv
      obtain ⟨x, hx⟩ := exists_of_imgCheckW hi hv
      exact ⟨x, by rw [hf]; exact hx⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, Module.finrank_fin_fun] at hrn
  have h6 : Module.finrank (ZMod 2) (LinearMap.ker f) = 6 := by omega
  have hcard : Nat.card (LinearMap.ker f) = 2 ^ 6 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), h6, ZMod.card]
  rw [← card_fixM_eq]
  have hset : fixM (toMatK t) = (LinearMap.ker f : Set Vec12) := Set.ext fun v => (hker v).symm
  rw [hset]
  exact hcard

end CFSG.KC.O8
