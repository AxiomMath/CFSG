module

public import CFSG.Blueprint.SourceExceptionalRootData
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank Module

@[expose] def autFixedSubgroup {M : Type} [Group M] (F : M ≃* M) : Subgroup M :=
  MonoidHom.eqLocus F.toMonoidHom (MonoidHom.id M)

theorem mem_autFixedSubgroup {M : Type} [Group M] (F : M ≃* M) (g : M) :
    g ∈ autFixedSubgroup F ↔ F g = g :=
  Iff.rfl

end CFSG.Blueprint.EvenSource
