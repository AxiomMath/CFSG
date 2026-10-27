module

public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.Generic6

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

theorem exists_autModel {L : Type} [Group L]
    (hL : LieModel L .PSL 3 3 1) :
    ∃ M : AutModel L (Equiv.Perm (Fin 26)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.L33.equiv_of_lieModel hL
  exact CFSG.GH74.KGroups.L33.autModel e

section Lift

variable {L : Type} [Group L] (M : AutModel L (Equiv.Perm (Fin 26)))

@[expose] noncomputable def liftA (g : Equiv.Perm (Fin 26)) (hg : g ∈ M.A) : MulAut L :=
  M.Φ.symm ⟨g, hg⟩

theorem ι_liftA (g : Equiv.Perm (Fin 26)) (hg : g ∈ M.A) : M.ι (liftA M g hg) = g := by
  show ((M.Φ (liftA M g hg) : M.A) : Equiv.Perm (Fin 26)) = g
  rw [liftA, MulEquiv.apply_symm_apply]

theorem liftA_ι (φ : MulAut L) : liftA M (M.ι φ) (M.ι_mem φ) = φ := by
  rw [liftA, MulEquiv.symm_apply_eq]
  exact Subtype.ext rfl

theorem e_liftA_apply {g : Equiv.Perm (Fin 26)} (hg : g ∈ M.A) (u : L) :
    ((M.e (liftA M g hg u) : M.P) : Equiv.Perm (Fin 26)) =
      g * (M.e u : Equiv.Perm (Fin 26)) * g⁻¹ := by
  rw [M.spec, liftA, MulEquiv.apply_symm_apply]

theorem liftA_inner_iff (hPA : M.P ≤ M.A) {g : Equiv.Perm (Fin 26)} (hg : g ∈ M.A) :
    (∃ a : L, ∀ u : L, liftA M g hg u = a * u * a⁻¹) ↔ g ∈ M.P := by
  constructor
  · rintro ⟨a, ha⟩
    have hmem : (M.e a : Equiv.Perm (Fin 26)) ∈ M.A := hPA (M.e a).2
    have hσ : (M.e a : Equiv.Perm (Fin 26))⁻¹ * g ∈ M.A :=
      M.A.mul_mem (M.A.inv_mem hmem) hg
    have hcomm : ∀ x ∈ M.P, ((M.e a : Equiv.Perm (Fin 26))⁻¹ * g) * x =
        x * ((M.e a : Equiv.Perm (Fin 26))⁻¹ * g) := by
      intro x hx
      obtain ⟨u, hu⟩ := M.e.surjective ⟨x, hx⟩
      have hx' : (M.e u : Equiv.Perm (Fin 26)) = x := congrArg Subtype.val hu
      rw [← hx']
      have key : g * (M.e u : Equiv.Perm (Fin 26)) * g⁻¹ =
          (M.e a : Equiv.Perm (Fin 26)) * (M.e u : Equiv.Perm (Fin 26)) *
            (M.e a : Equiv.Perm (Fin 26))⁻¹ := by
        rw [← e_liftA_apply M hg u, ha u]
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (M.e a : Equiv.Perm (Fin 26))⁻¹ * g * (M.e u : Equiv.Perm (Fin 26))
            = (M.e a : Equiv.Perm (Fin 26))⁻¹ *
                (g * (M.e u : Equiv.Perm (Fin 26)) * g⁻¹) * g := by group
        _ = (M.e a : Equiv.Perm (Fin 26))⁻¹ *
                ((M.e a : Equiv.Perm (Fin 26)) * (M.e u : Equiv.Perm (Fin 26)) *
                  (M.e a : Equiv.Perm (Fin 26))⁻¹) * g := by rw [key]
        _ = (M.e u : Equiv.Perm (Fin 26)) *
                ((M.e a : Equiv.Perm (Fin 26))⁻¹ * g) := by group
    have h1 : (M.e a : Equiv.Perm (Fin 26))⁻¹ * g = 1 :=
      M.centralizer_trivial hσ hcomm
    have h2 : g = (M.e a : Equiv.Perm (Fin 26)) := by
      calc g = (M.e a : Equiv.Perm (Fin 26)) *
                ((M.e a : Equiv.Perm (Fin 26))⁻¹ * g) := by group
        _ = (M.e a : Equiv.Perm (Fin 26)) := by rw [h1, mul_one]
    rw [h2]
    exact (M.e a).2
  · intro hgP
    refine ⟨M.e.symm ⟨g, hgP⟩, fun u => ?_⟩
    apply M.e.injective
    apply Subtype.ext
    rw [e_liftA_apply M hg u]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]

theorem liftA_e (hPA : M.P ≤ M.A) (a : L) :
    liftA M (M.e a : Equiv.Perm (Fin 26)) (hPA (M.e a).2) = MulAut.conj a := by
  ext u
  apply M.e.injective
  apply Subtype.ext
  rw [e_liftA_apply M (hPA (M.e a).2) u]
  simp only [MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

end Lift

end CFSG.OddStandard.SmallF3.L33
