module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelianLayers
public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelianClassTwo

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78.Finkelstein
open scoped commutatorElement

namespace Finkelstein.Hyp

variable {U : Type} [Group U] [Finite U] {n : ℕ} {t y : MulAut U} (h : Finkelstein.Hyp U n t y)
include h

theorem psi_mem_bSub_of_sq (hsq : ∀ u : U, u ^ 2 ∈ fixSubgroup t) (u : U) :
    psi t u ∈ h.bSub := by
  rw [mem_bSub, psi_psi h.t_t]
  exact inv_mem (hsq _)

theorem psi_psi_mul_of_sq (hsq : ∀ u : U, u ^ 2 ∈ fixSubgroup t) (u v : U) :
    psi t (psi t (u * v)) = psi t (psi t u) * psi t (psi t v) := by
  set c := ⁅(psi t u)⁻¹, v⁻¹⁆ with hc
  have hcA : c ∈ fixSubgroup t :=
    h.commutator_mem_fix_of_mem_bSub (inv_mem (h.psi_mem_bSub_of_sq hsq u)) _
  have e0 : psi t (u * v) = psi t u * c * psi t v := by
    simp only [psi, hc, commutatorElement_def, map_mul]
    group
  have e : psi t (u * v) = psi t u * psi t v * c := by
    rw [e0, mul_assoc, ← h.mem_center_of_mem_fix hcA (psi t v), ← mul_assoc]
  rw [e, h.psi_mul_fix hcA, h.psi_mul_of_mem (h.psi_mem_bSub_of_sq hsq u)]

@[expose] noncomputable def topHom (hsq : ∀ u : U, u ^ 2 ∈ fixSubgroup t) : U →* U where
  toFun u := psi t (psi t u)
  map_one' := by
    show psi t (psi t 1) = 1
    rw [psi_eq_one_iff.mpr (one_mem _), psi_eq_one_iff.mpr (one_mem _)]
  map_mul' := h.psi_psi_mul_of_sq hsq

theorem topHom_apply (hsq : ∀ u : U, u ^ 2 ∈ fixSubgroup t) (u : U) :
    h.topHom hsq u = psi t (psi t u) :=
  rfl

theorem topHom_mem (hsq : ∀ u : U, u ^ 2 ∈ fixSubgroup t) (u : U) :
    h.topHom hsq u ∈ fixSubgroup t :=
  h.psi_mem_bSub_of_sq hsq u

theorem topHom_y (hsq : ∀ u : U, u ^ 2 ∈ fixSubgroup t) (u : U) :
    h.topHom hsq (y u) = y (h.topHom hsq u) := by
  rw [topHom_apply, topHom_apply, psi_map_of_comm h.comm, psi_map_of_comm h.comm]

end Finkelstein.Hyp

end CFSG.SeitzReduction.RankOne
