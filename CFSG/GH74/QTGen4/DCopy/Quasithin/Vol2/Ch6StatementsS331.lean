module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Vol2.Ch6Inputs
public import CFSG.Quasithin.Vol2.Ch6Statements

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Stmt6_1_2_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    (IsSumOfTwo L V (fun W => IsNatModCh5 L W n) ∨ IsNatQuotCh5 L ⁅V, L⁆ n ∨
      (2 < n ∧ IsOrthCh5 L V n)) ∧
    (IsNatQuotCh5 L ⁅V, L⁆ n ∨
      (thompsonJ T ≤ ch6Q T V ∧ ch6Q T V = pCoreOf 2 (L ⊔ T) ∧
        L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
        IsUniqueM (Subgroup.normalizer (thompsonJ T : Set G)) M))

end CFSG.Quasithin.H13
