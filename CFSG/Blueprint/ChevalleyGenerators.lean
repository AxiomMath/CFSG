module

public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Blueprint.ChevalleyUnits
public import Certificates.Certificate113

public section

namespace CFSG.Blueprint.Chevalley

theorem simple_root_operator_units_of_tag (τ : Tag) (R : Type*) [CommRing R] (i : Fin τ.rank)
    (c : R) :
    (∀ a b : Label τ, b.Precedes a → xOp τ R i c (Finsupp.single b 1) a = 0) ∧
      (∀ b : Label τ, xOp τ R i c (Finsupp.single b 1) b = 1) ∧
      (∀ a b : Label τ, a.Precedes b → yOp τ R i c (Finsupp.single b 1) a = 0) ∧
      (∀ b : Label τ, yOp τ R i c (Finsupp.single b 1) b = 1) ∧
      LinearMap.det (xOp τ R i c) = 1 ∧ LinearMap.det (yOp τ R i c) = 1 ∧
      IsUnit (xOp τ R i c) ∧ IsUnit (yOp τ R i c) :=
  simple_root_operator_units i c

theorem xOp_yOp_mem_adjointGroup (τ : Tag) (K : Type*) [Field K] (i : Fin τ.rank) (c : K) :
    (∃ g ∈ adjointGroup τ K, (g : Module.End K (RootModule τ K)) = xOp τ K i c) ∧
      ∃ g ∈ adjointGroup τ K, (g : Module.End K (RootModule τ K)) = yOp τ K i c :=
  ⟨exists_mem_adjointGroup_xOp i c, exists_mem_adjointGroup_yOp i c⟩

end CFSG.Blueprint.Chevalley
