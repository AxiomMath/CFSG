module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.WeylRoots

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

@[expose] def parabolicWeylGroup
    (τ : Tag) (J : Set (Fin τ.rank)) : Subgroup (WeylGroup τ) :=
  Subgroup.closure (simple τ '' J)

@[expose] def parabolicSubgroup
    (τ : Tag) (K : Type*) [Field K] (J : Set (Fin τ.rank)) :
    Subgroup (Module.End K (RootModule τ K))ˣ :=
  borelGroup τ K ⊔ Subgroup.closure ((fun j => weylElt τ K j 1) '' J)

theorem parabolicSubgroup_le_adjointGroup
    (τ : Tag) (K : Type*) [Field K]
    (J : Set (Fin τ.rank)) : parabolicSubgroup τ K J ≤ adjointGroup τ K := by
  have hB : borelGroup τ K ≤ adjointGroup τ K :=
    ((triangular_borel_structure τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
  refine sup_le hB ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, -, rfl⟩
  exact weylElt_mem_adjointGroup j 1

end CFSG.LieType.Chevalley
