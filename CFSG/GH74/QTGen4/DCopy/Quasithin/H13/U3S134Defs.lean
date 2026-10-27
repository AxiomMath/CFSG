module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

@[expose] def Stmt13_4_8_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (_ : A6.Setting134 G T L V) (z : G),
    z ∈ fsuV1 T V → z ∉ centralizer (L : Set G) →
    ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G) →
    ∀ H VH : Subgroup G, InHz T L V z H → Group.IsSolvable ↥H → IsTwoReducedIn H VH →
      V ⊓ centralizer (L : Set G) ≤ VH →

      quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6)) ∧

      quasithinO2QuotientIso (conjClosure (thompsonJ (r1Of T L V)) H) (Perm (Fin 3)) ∧
      Nat.card ↥⁅VH, conjClosure (thompsonJ (r1Of T L V)) H⁆ = 4 ∧

      H = L₁Of L (fsuV1 T V) ⊔ conjClosure (thompsonJ (r1Of T L V)) H ⊔ T ∧
      quasithinO2QuotientIso H (Perm (Fin 3) × Perm (Fin 3)) ∧
      IsHStar T (normalizer (L : Set G)) (conjClosure (thompsonJ (r1Of T L V)) H ⊔ T) ∧
      ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H →
        X = conjClosure (thompsonJ (r1Of T L V)) H ⊔ T

end CFSG.Quasithin.H13.U3
