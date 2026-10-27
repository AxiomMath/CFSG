module

public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] def foldedParabolicWeylGroup
    (J : Set (Fin t.foldedTag.rank)) :
    Subgroup (WeylGroup t.tag) :=
  Subgroup.closure (t.orbitReflection '' J)

@[expose] def graphFixedParabolic
    (J : Set (Fin t.foldedTag.rank)) : Subgroup (ModGL t.tag K) :=
  graphFixedRootBorel t K σ ⊔ Subgroup.closure
    ((fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) '' J)

theorem foldedParabolicWeylGroup_le
    (J : Set (Fin t.foldedTag.rank)) :
    foldedParabolicWeylGroup t J ≤ relWeylTwist t :=
  (Subgroup.closure_le _).2 fun _ ⟨a, _, ha⟩ => ha ▸ t.orbitReflection_mem a

theorem graphFixedParabolic_le
    (J : Set (Fin t.foldedTag.rank)) :
    graphFixedParabolic t K σ J ≤ graphFixedRootGroup t K σ :=
  sup_le (graphFixedRootBorel_le t K σ) ((Subgroup.closure_le _).2 fun _ ⟨a, _, ha⟩ =>
    ha ▸ canonicalRep_orbitReflection_mem_graphFixedRootGroup a)

theorem graphFixedRootBorel_le_graphFixedParabolic
    (J : Set (Fin t.foldedTag.rank)) :
    graphFixedRootBorel t K σ ≤ graphFixedParabolic t K σ J :=
  le_sup_left

theorem foldedParabolicWeylGroup_empty
    : foldedParabolicWeylGroup t ∅ = ⊥ := by
  rw [foldedParabolicWeylGroup, Set.image_empty, Subgroup.closure_empty]

theorem graphFixedParabolic_empty
    : graphFixedParabolic t K σ ∅ = graphFixedRootBorel t K σ := by
  rw [graphFixedParabolic, Set.image_empty, Subgroup.closure_empty, sup_bot_eq]

end CFSG.LieType.Chevalley
