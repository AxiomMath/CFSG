module

public import CFSG.GF2Type.SmithTypeE.LMod.T6

public section

namespace CFSG.GF2Type.SmithTypeE.L6

open Matrix CFSG.GF2Type.SmithTypeE.LMod
open scoped MatrixGroups

theorem zmod2_eq_one_of_mul {a b : ZMod 2} (h : a * b = 1) : b = 1 := by
  revert a b
  decide

theorem exists_conj_of_mat {π π' : Equiv.Perm (Fin 1953)}
    {G H : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hHG : Hᵀ * G = 1)
    (h : ∀ x y : Fin 1953, tvVec y = G *ᵥ tvVec x → tvForm y = H *ᵥ tvForm x →
      tvVec (π' y) = G *ᵥ tvVec (π x) ∧ tvForm (π' y) = H *ᵥ tvForm (π x)) :
    ∃ g ∈ T6, g * π * g⁻¹ = π' := by
  have hdet : G.det = 1 := by
    have e := congrArg det hHG
    rw [det_mul, det_one] at e
    exact zmod2_eq_one_of_mul e
  let A : SL(6, ZMod 2) := ⟨G, hdet⟩
  have hinv : ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = Hᵀ := by
    rw [← inv_eq_left_inv (coe_inv_mul A), ← inv_eq_left_inv hHG]
  have hact : ∀ x, tvVec (actPerm A x) = G *ᵥ tvVec x ∧ tvForm (actPerm A x) = H *ᵥ tvForm x :=
    fun x => ⟨tvVec_actPerm A x, by rw [tvForm_actPerm, hinv, vecMul_transpose]⟩
  have key : ∀ x, π' (actPerm A x) = actPerm A (π x) := fun x => by
    obtain ⟨e1, e2⟩ := h x (actPerm A x) (hact x).1 (hact x).2
    apply tvToSet_injective
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · change tvVec _ = tvVec _
      rw [e1, (hact (π x)).1]
    · change tvForm _ = tvForm _
      rw [e2, (hact (π x)).2]
  refine ⟨actPerm A, actPerm_mem A, Equiv.ext fun z => ?_⟩
  have e := key ((actPerm A)⁻¹ z)
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e]
  simp

end CFSG.GF2Type.SmithTypeE.L6
