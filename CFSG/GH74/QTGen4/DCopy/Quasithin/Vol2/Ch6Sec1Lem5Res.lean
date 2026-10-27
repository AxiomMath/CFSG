module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.Vol2.Ch6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def Res615Blocks_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H : Subgroup G) (n : ℕ), Hyp611 G T M L V n →
    IsHStar T M H → ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) H))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hU)))),
      (I.card = 1 ∨ I.card = 2) →
      autI hU (thompsonJ H) = ⨆ K ∈ I, K →
      (∀ K ∈ I, (∃ m : ℕ, E2.IsL2Natural K (fixV (autI hU (twoResidual H))) m) ∨
        E2.IsA5Module K) →
      ∀ K ∈ I, E2.IsL2Natural K (fixV (autI hU (twoResidual H))) 1

end CFSG.Quasithin.H13
