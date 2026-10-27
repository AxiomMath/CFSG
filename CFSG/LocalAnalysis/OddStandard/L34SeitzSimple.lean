module

public import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.LocalAnalysis.OddStandard.L34FaithfulExclusion

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint

@[expose] def Seitz77SimpleL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ A : Subgroup G, standardComponentIsStandard A → Odd (Nat.card (center A)) →
      (∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S) →
        LieModel (A ⧸ center A) .PSL 3 2 2 → Seitz77Outcome G A 3 2

theorem l34CyclicOddCenter_of_seitzSimple (h : Seitz77SimpleL34) : L34CyclicOddCenter := by
  intro G _ _ L hS h34 hodd S hcyc
  exact false_of_seitz77Outcome hS h34 (h G hS.simple hS.nonab L hS.standard hodd
    (fun S' => ((Sylow.equiv S S').isCyclic).1 hcyc) h34)

end CFSG.OddStandard
