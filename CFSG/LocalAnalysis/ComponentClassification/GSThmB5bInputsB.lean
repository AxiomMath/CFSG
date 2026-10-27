module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsLit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar

public section

namespace CFSG.ComponentClassification.GSThmB

theorem genFittingSimpleStatement : GenFittingSimpleStatement :=
  fun _ _ _ h => h.generalizedFitting_simple.2.1

theorem sylowKernelStatement : SylowKernelStatement := fun _ _ _ h => h.sylow_kernel

theorem prodConjStatement : ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H), ⁅h.B, conjugate h.B h.x⁆ = ⊥ :=
  fun _ _ _ h => h.prod_conj.2.2.1

theorem embedsTQuotStatement : EmbedsTQuotStatement := fun _ _ _ h => h.embeds_T_quot

end CFSG.ComponentClassification.GSThmB
