module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.WholeGroup

variable {G : Type*} [Group G]

@[expose, reducible] def layerOf (C : Subgroup G → Prop) : Subgroup G :=
  sSup {K : Subgroup G | C K}

@[expose, reducible] def fstarOf (E : Subgroup G) : Subgroup G :=
  fittingSubgroup G ⊔ E

theorem layerOf_congr {C D : Subgroup G → Prop} (h : ∀ K, C K ↔ D K) : layerOf C = layerOf D := by
  simp only [layerOf, h]

theorem fstarOf_layerOf_congr {C D : Subgroup G → Prop} (h : ∀ K, C K ↔ D K) :
    fstarOf (layerOf C) = fstarOf (layerOf D) := by
  rw [layerOf_congr h]

end CFSG.WholeGroup
