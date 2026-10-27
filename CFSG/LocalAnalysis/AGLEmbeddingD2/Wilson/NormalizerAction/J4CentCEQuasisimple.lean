module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0Struct

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
  CFSG.AGLEmbeddingD2.Wilson.Coordinator CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.GLQ Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Struct


theorem centralizer_cE_quasisimple (hF : J4Facts) :
    CFSG.IsQuasisimple ↥(centralizer ({cE} : Set J)) ∧
    Nat.card ↥(center ↥(centralizer ({cE} : Set J))) = 6 ∧
    Nonempty (↥(centralizer ({cE} : Set J)) ⧸ center ↥(centralizer ({cE} : Set J)) ≃*
      CFSG.Blueprint.NativeSporadic.M22) := by
  have h := L0_eq_centralizer hF
  rw [← h]
  exact ⟨isQuasisimple_LL hF, card_center_LL hF, ⟨quotEquivM22 hF⟩⟩

end Struct

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
