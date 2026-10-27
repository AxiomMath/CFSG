module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAssembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Spine

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Blueprint.NativeSporadic

theorem lemma44_one_two
    (A : Fi22CoverAut)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    (h2 : Nat.card (center L) = 2) (hQ : IsSporadic (L ⧸ center L) .Fi22) {t : G}
    (ht : (center L).map L.subtype = zpowers t) :
    centralizer (L : Set G) = zpowers t ∧
      (centralizer ({t} : Set G) ≠ L →
        ∃ θ : centralizer ({t} : Set G) →* MulAut (L ⧸ center L), Function.Surjective θ ∧
          θ.ker = (zpowers t).subgroupOf (centralizer ({t} : Set G))) := by
  obtain ⟨E', M⟩ := exists_localModel (fi22CoverRest_of_aut A) h.standard.1 h2 hQ
  exact ⟨(spine h h2 hQ ht M).1, fun hne => exists_surjective_automizer h h2 hQ ht M hne⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81
