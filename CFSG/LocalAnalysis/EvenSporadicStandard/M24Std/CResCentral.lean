module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResChief
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResHopf

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

variable {U E : Type} [Group U] [Group E]

theorem card_ker_eq_one_of_chiefData [Finite U] [Finite E] (hFT : OddSolv) (hH1 : ElemAbH1)
    (hH2 : ElemAbH2) (hU : commutator U = ⊤) (q : U →* E) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) {N0 : ℕ} (hN0 : Nat.card U ∣ N0) (hE : ChiefData E N0)
    (hM : Nat.card (griessHopfMultiplier E) ∣ 2) : Nat.card q.ker = 1 := by
  have hcen : q.ker ≤ center U :=
    le_center_of_chiefTrivial hU (chiefTrivial_of_data hFT hH1 hH2 hU q hq hodd hN0 hE)
  exact card_ker_eq_one_of_odd hU q hq hcen hodd hM

end CFSG.EvenSporadicStandard.M24Std
