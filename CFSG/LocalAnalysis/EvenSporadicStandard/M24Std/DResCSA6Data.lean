module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open CFSG.QuasithinUnique.A6Facts

@[expose] def A6InvData : Prop :=
  ∀ c ∈ Core.autL, Core.cmul c c = Core.cid →
    ((Core.cpslList c).length = 360 ∨ (Core.cpslList c).length = 8 ∨
      (Core.cpslList c).length = 24 ∨ (Core.cpslList c).length = 10)

instance : Decidable A6InvData := by unfold A6InvData; infer_instance

end CFSG.EvenSporadicStandard.M24Std.DRes
