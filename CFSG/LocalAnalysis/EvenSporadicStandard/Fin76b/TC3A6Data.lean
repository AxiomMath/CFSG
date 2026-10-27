module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.QuasithinUnique.A6Facts

@[expose] def A6OrdData : Prop :=
  ∀ c ∈ Core.autL, (Core.cpow c 16 = Core.cid → Core.cpow c 8 = Core.cid) ∧
    (Core.cpow c 8 = Core.cid → Core.cpow c 4 ≠ Core.cid →
      ∀ d ∈ Core.autL, Core.cmul d c = Core.cmul c d → ∃ k < 8, d = Core.cpow c k)

instance : Decidable A6OrdData := by unfold A6OrdData; infer_instance

end CFSG.EvenSporadicStandard.Fin76b
