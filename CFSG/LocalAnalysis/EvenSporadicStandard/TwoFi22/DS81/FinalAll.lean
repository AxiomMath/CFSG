module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.FinalAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutFinal

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Blueprint.NativeSporadic

theorem lemma44_one_two_final
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G}
    (ht : (center L).map L.subtype = zpowers t) :
    centralizer (L : Set G) = zpowers t ∧
      (centralizer ({t} : Set G) ≠ L →
        ∃ θ : centralizer ({t} : Set G) →* MulAut (L ⧸ center L), Function.Surjective θ ∧
          θ.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G))) :=
  lemma44_one_two fi22CoverAut h h2 hQ ht

end CFSG.EvenSporadicStandard.TwoFi22.DS81
