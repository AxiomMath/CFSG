module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem borel_weyl_generation
    (τ : Tag) (K : Type*) [Field K] :
    adjointGroup τ K =
        borelGroup τ K ⊔ Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ K i 1) ∧
      adjointGroup τ K = borelGroup τ K ⊔ monomialSubgroup τ K := by
  have hB : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  have hN : Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ K i 1) ≤
      adjointGroup τ K := (Subgroup.closure_le _).2 (by
    rintro _ ⟨i, rfl⟩
    exact weylElt_mem_adjointGroup i 1)
  have hx : ∀ (i : Fin τ.rank) (c : K), xUnit τ K i c ∈ borelGroup τ K := fun i c => by
    refine Subgroup.mem_sup_right ?_
    rw [← pinnedX_single]
    exact Subgroup.mem_iSup_of_mem (Pi.single i 1) (Subgroup.mem_iSup_of_mem
      ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩ (Subgroup.subset_closure ⟨_, rfl⟩))
  have h1 : adjointGroup τ K =
      borelGroup τ K ⊔ Subgroup.closure (Set.range fun i : Fin τ.rank => weylElt τ K i 1) := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) (sup_le hB hN)
    rintro g ⟨i, c, hg | hg⟩
    · have : g = xUnit τ K i c := Units.ext hg
      rw [this]
      exact Subgroup.mem_sup_left (hx i c)
    · have hy : g = weylElt τ K i 1 * xUnit τ K i (-c) * (weylElt τ K i 1)⁻¹ := by
        refine Units.ext ?_
        rw [hg, Units.val_mul, Units.val_mul, coe_xUnit, weylElt_mul_xOp_mul_inv]
        congr 1
        simp
      rw [hy]
      refine mul_mem (mul_mem ?_ (Subgroup.mem_sup_left (hx i (-c)))) (inv_mem ?_) <;>
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, rfl⟩)
  refine ⟨h1, ?_⟩
  have hHB : torusGroup τ K ≤ borelGroup τ K := le_sup_left
  rw [h1, monomialSubgroup, ← sup_assoc, sup_eq_left.2 hHB]

end CFSG.LieType.Chevalley
