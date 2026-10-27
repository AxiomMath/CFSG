module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCores
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadMinus)

variable (k : Type) [Field k]

@[expose] def minusDiagUnits : (Fin 3 → kˣ) →* (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → kˣ) where
  toFun t := Sum.elim t (Sum.elim (fun i => (t i)⁻¹) fun _ => 1)
  map_one' := by
    funext a
    rcases a with i | i | j <;> simp
  map_mul' t s := by
    funext a
    rcases a with i | i | j
    · rfl
    · simp only [Sum.elim_inr, Sum.elim_inl, Pi.mul_apply, _root_.mul_inv_rev]
      exact mul_comm _ _
    · simp

@[expose] noncomputable def diagOmegaMinus :
    (Fin 3 → kˣ) →* GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k :=
  TauCeti.diagGL.comp (minusDiagUnits k)

@[expose] def minusWeight (t : Fin 3 → kˣ) : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k :=
  Sum.elim (fun i => ((t i : kˣ) : k)) (Sum.elim (fun i => (((t i)⁻¹ : kˣ) : k)) fun _ => 1)

variable {k}

@[simp] theorem minusWeight_inl (t : Fin 3 → kˣ) (i : Fin 3) :
    minusWeight k t (Sum.inl i) = ((t i : kˣ) : k) := rfl

@[simp] theorem minusWeight_inr_inl (t : Fin 3 → kˣ) (i : Fin 3) :
    minusWeight k t (Sum.inr (Sum.inl i)) = (((t i)⁻¹ : kˣ) : k) := rfl

@[simp] theorem minusWeight_inr_inr (t : Fin 3 → kˣ) (j : Fin 2) :
    minusWeight k t (Sum.inr (Sum.inr j)) = 1 := rfl

theorem diagOmegaMinus_coe (t : Fin 3 → kˣ) :
    (diagOmegaMinus k t : Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) = diagonal (minusWeight k t) := by
  rw [diagOmegaMinus, MonoidHom.comp_apply, TauCeti.diagGL_coe]
  congr 1
  funext a
  rcases a with i | i | j <;> rfl

theorem isHypFrame_quadMinus_four (b c : k) :
    OmegaPilot.IsHypFrame (CFSG.LieType.Universal.Spin.quadMinus 4 k b c)
      (fun i : Fin 3 => (Sum.inl i : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2))
      (fun i : Fin 3 => Sum.inr (Sum.inl i)) where
  hyp i := OmegaPilot.isHypCoord_quadMinus (n := 4) b c i
  left_injective := fun _ _ h => Sum.inl_injective h
  right_injective := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)
  left_ne_right _ _ := Sum.inl_ne_inr

theorem toLinEquiv_diagOmegaMinus (b c : k) (t : Fin 3 → kˣ) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k
        (diagOmegaMinus k t) =
      OmegaPilot.frameLin (fun i : Fin 3 => (Sum.inl i : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2))
        (fun i : Fin 3 => Sum.inr (Sum.inl i)) t := by
  ext v a
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, OmegaPilot.frameLin_apply,
    diagOmegaMinus_coe, mulVec_diagonal]
  congr 1
  rcases a with i | i | j
  · rw [minusWeight_inl, (isHypFrame_quadMinus_four b c).frameEntry_left]
  · rw [minusWeight_inr_inl, (isHypFrame_quadMinus_four b c).frameEntry_right]
  · rw [minusWeight_inr_inr, OmegaPilot.frameEntry_of_forall_ne t (fun _ => Sum.inr_ne_inl)
      (fun _ h => Sum.inr_ne_inl (Sum.inr_injective h)), Units.val_one]

theorem diagOmegaMinus_mem [Finite k] [CharP k 2] (b c : k) (t : Fin 3 → kˣ) :
    diagOmegaMinus k t ∈ StatedOmega (StatedQuadMinus 4 k b c) := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadMinus 4 k b c), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, toLinEquiv_diagOmegaMinus b c]
  exact (isHypFrame_quadMinus_four b c).frameLin_mem_orthDerived t

end CFSG.SeitzReduction.F4Pilot
