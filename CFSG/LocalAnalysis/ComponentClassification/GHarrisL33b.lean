module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL33

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup HSFLit SCert

theorem SCert.SE.ghRel_genSwap : GHRel (SE.gen 0) (SE.gen 1) (SE.gen 2) (SE.gen 3) (SE.gen 4)
    (SE.gen 5) (SE.gen 6) (SE.gen 7) (SE.gen 8 * SE.gen 1) := by
  constructor <;> decide

theorem SCert.SE.invRep_seven : SE.invRep 7 = SE.gen 8 := by decide

theorem SCert.SE.invRep_eight : SE.invRep 8 = SE.gen 8 * SE.gen 1 := by decide

@[expose] def swapHom : SE →* SE := SE.ghRel_genSwap.hom.comp equivSE.symm.toMonoidHom

theorem swapHom_gen (i : Fin 9) : swapHom (SE.gen i) = ghFam (SE.gen 0) (SE.gen 1) (SE.gen 2)
    (SE.gen 3) (SE.gen 4) (SE.gen 5) (SE.gen 6) (SE.gen 7) (SE.gen 8 * SE.gen 1) i := by
  change SE.ghRel_genSwap.hom (equivSE.symm (SE.gen i)) = _
  rw [equivSE_symm_gen, GHRel.hom, PresentedGroup.toGroup.of]

theorem swapHom_surjective : Function.Surjective swapHom := by
  have hmem : ∀ i, SE.gen i ∈ swapHom.range := by
    intro i
    by_cases hi : i = 8
    · subst hi
      refine ⟨SE.gen 8 * (SE.gen 1)⁻¹, ?_⟩
      rw [map_mul, map_inv, swapHom_gen, swapHom_gen]
      exact mul_inv_cancel_right _ _
    · refine ⟨SE.gen i, ?_⟩
      rw [swapHom_gen]
      fin_cases i <;> first | rfl | exact absurd rfl hi
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← SE.closure_range_gen, closure_le]
  rintro _ ⟨i, rfl⟩
  exact hmem i

@[expose] def swapEquiv : SE ≃* SE :=
  MulEquiv.ofBijective swapHom
    ⟨Finite.injective_iff_surjective.mpr swapHom_surjective, swapHom_surjective⟩

theorem swapEquiv_apply (s : SE) : swapEquiv s = swapHom s := rfl

namespace GHSylow

variable {G : Type} [Group G] (D : GHSylow G)

@[expose] def swap : GHSylow G where
  S := D.S
  equiv := (equivSE.trans swapEquiv).trans (equivSE.symm.trans D.equiv)

theorem swap_toG (s : SE) : D.swap.toG s = D.toG (swapHom s) := by
  change ((D.equiv (equivSE.symm (swapEquiv (equivSE (equivSE.symm s))))) : G) =
    ((D.equiv (equivSE.symm (swapHom s))) : G)
  rw [MulEquiv.apply_symm_apply, swapEquiv_apply]

theorem swap_x : D.swap.x = D.x := by
  rw [x, x, swap_toG, swapHom_gen]
  rfl

theorem swap_a : D.swap.a = D.al := by
  rw [a, al, swap_toG, SE.invRep_seven, swapHom_gen, SE.invRep_eight]
  rfl

theorem exists_ghSylow_not_conj_x_a [Finite G] :
    ∃ D' : GHSylow G, D'.S = D.S ∧ ¬ ∃ g : G, g⁻¹ * D'.x * g = D'.a := by
  by_cases h : ∃ g : G, g⁻¹ * D.x * g = D.a
  · refine ⟨D.swap, rfl, ?_⟩
    rw [swap_x, swap_a]
    exact fun h' => D.not_conj_x_a_and_al ⟨h, h'⟩
  · exact ⟨D, rfl, h⟩

end GHSylow

end CFSG.ComponentClassification.GHarris
