module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier (fixSub)

@[expose] def ONOuterLocalInput : Prop :=
  ∀ (G : Type) [Group G], Nonempty (G ≃* NativeSporadic.ON) → ∀ α : MulAut G, α * α = 1 →
    α ∉ inner G → ∀ z : fixSub α, orderOf z = 2 →
      ∃ F : Subgroup (fixSub α), F ≤ centralizer ({z} : Set (fixSub α)) ∧ z ∉ F ∧
        centralizer ({z} : Set (fixSub α)) = zpowers z ⊔ F ∧
        Nonempty (F ≃* alternatingGroup (Fin 5))

end CFSG.ComponentClassification.SolMax
