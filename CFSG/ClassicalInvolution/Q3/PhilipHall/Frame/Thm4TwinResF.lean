module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinTight

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform

namespace Thm4Twin

@[expose] def F2Config {G : Type} [Group G] [Finite G] (J L L₀ : Subgroup G) : Prop :=
  TwinT4Min 3 G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L ∧
    omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ ∧
    HasTwin (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) ∧
    TL4.NoInvO2 (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) ∧
    CFSG.IsComponent L₀ ∧ L₀.Normal ∧ layer G = L₀ ∧
    generalizedFitting G = L₀ ⊔ pCore 2 G ∧ pCore 2 G = Subgroup.center G ∧
    Subgroup.centralizer (L₀ : Set G) = Subgroup.center G ∧
    (∀ K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L, ∀ z : G,
      IsUniqueInvolution K z → z ∈ L₀)

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
