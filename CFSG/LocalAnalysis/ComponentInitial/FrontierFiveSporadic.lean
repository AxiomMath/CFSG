module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentInitial.FrontierAssembly
public import CFSG.Sporadic.Schreier.J4SCatalog
public import CFSG.Sporadic.Schreier.Co1CatalogSchreier
public import CFSG.Sporadic.Co2Schreier.Model
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification.SporadicSchreierDispatch
open CFSG.ComponentClassification.CatalogSchreierCases
open CFSG.ComponentClassification.OuterAutomorphisms

theorem sporadicSchreierCase_J4 :
    SporadicSchreierCase .J4 :=
  fun _ _ _ _ _ he => CFSG.Sporadic.J4Schreier.R3E_J4_catalog_Schreier he

theorem sporadicSchreierCase_Co2 :
    SporadicSchreierCase .Co2 :=
  sporadicSchreierCase_of_outer CFSG.Sporadic.Co2Schreier.AT_Co2_Schreier

theorem sporadicSchreierCase_Co1
    : SporadicSchreierCase .Co1 := by
  obtain ⟨-, hfin, hp, -⟩ := CFSG.Sporadic.Co1Schreier.catalog_schreier_of_inputs.{0}
    fun K _ e => CFSG.Sporadic.Co2Schreier.AT_Co2_model_Schreier K e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hp.isNilpotent
  have hs : Group.IsSolvable (Outer CFSG.Blueprint.NativeSporadic.Co1) := inferInstance
  exact sporadicSchreierCase_of_outer hs

theorem sporadicRep_schreier_of_five
    (hHN : SporadicSchreierCase .HN)
    (hLy : SporadicSchreierCase .Ly) (hTh : SporadicSchreierCase .Th)
    (hB : SporadicSchreierCase .B) (hM : SporadicSchreierCase .M) (S : Type) [Group S]
    [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hS : CFSG.Blueprint.NativeSporadic.SporadicRep S) : Group.IsSolvable (Outer S) :=
  sporadicRep_schreier_of_remaining sporadicSchreierCase_J2 sporadicSchreierCase_J3
    sporadicSchreierCase_J4 sporadicSchreierCase_Co1 sporadicSchreierCase_Co2
    sporadicSchreierCase_Co3 sporadicSchreierCase_Fi22 sporadicSchreierCase_Fi23
    sporadicSchreierCase_Fi24 sporadicSchreierCase_HS sporadicSchreierCase_McL
    sporadicSchreierCase_He sporadicSchreierCase_Ru sporadicSchreierCase_Suz
    sporadicSchreierCase_ON hHN hLy hTh hB hM S hnonab hS

theorem initial_standard_component_frontier_of_five_sporadic
    (hHN : SporadicSchreierCase .HN) (hLy : SporadicSchreierCase .Ly)
    (hTh : SporadicSchreierCase .Th) (hBM : SporadicSchreierCase .B)
    (hM : SporadicSchreierCase .M) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hrank : 3 ≤ CFSG.Assembly.twoRank G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :=
  initial_standard_component_frontier_of_tits_sporadic tits_model_outer_solvable
    (fun S _ _ _ hnonab hS => sporadicRep_schreier_of_five hHN hLy hTh hBM hM S hnonab hS)
    G hnonab hK hrank hcomp hB

end CFSG.LocalAnalysis.ComponentInitial
