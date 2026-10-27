module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.U3L14Blk

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Stmt13_3_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V Lp : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → V ⊓ centralizer (L : Set G) = ⊥ →
    (A6.IsHatA6 L → Lp = A6.l1plus T L V) → (¬ A6.IsHatA6 L → Lp = L₁Of L (fsuV1 T V)) →
    ((Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6))) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      (CharNormal (baum (pCoreOf 2 (Lp ⊔ T))) (L ⊔ T) ∨ H13.IsA6Block L ∨ IsG2Block L) ∧
      (IsG2Block L →
        normalizer (baum (pCoreOf 2 (Lp ⊔ T)) : Set G) ≤ normalizer (L : Set G))) ∧
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      CharNormal (baum (pCoreOf 2 (Lp ⊔ T))) (L ⊔ T) ∨ IsLnBlock L 3)

variable [CFSG.GH74.QTGen4.Finite4 G]

end CFSG.Quasithin.H13.U3
