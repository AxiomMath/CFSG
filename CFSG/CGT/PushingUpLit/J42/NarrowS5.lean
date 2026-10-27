module

public import CFSG.CGT.PushingUpLit.J42.Narrow
public import CFSG.CGT.PushingUpLit.J42.Alt5Gen

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.GH74 Equiv Equiv.Perm
open CFSG.Assembly (InCatalog KProper)

@[expose] def JankoU42Gen4S5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (S : SolCfg G M X 2),
    KProper InCatalog G → TightData S → RSmall S → ¬ CentInM S →
      (∃ m : ↥M, sign (S.θ m) = -1) → SectionalTwoRankLE G 4

theorem jankoU42Gen4_of_S5 (h : JankoU42Gen4S5) : JankoU42Gen4 := by
  intro G _ _ M X S hKP hT hR hC
  by_cases hA : ∃ m : ↥M, sign (S.θ m) = -1
  · exact h G M X S hKP hT hR hC hA
  · push Not at hA
    refine S.gen4_degree_five_of_alt hT hR (fun m => ?_) hC
    exact Equiv.Perm.mem_alternatingGroup.2 ((Int.units_eq_one_or _).resolve_right (hA m))

end CFSG.CGT.PushingUpLit.SolK
