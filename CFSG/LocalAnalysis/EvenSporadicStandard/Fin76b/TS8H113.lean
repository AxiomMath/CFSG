module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H112
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H610N

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OuterS8Hyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (h : OuterS8Hyp G L z t T E Q x B β S)

include h

theorem outerMFacts {α : G} (hα : AlphaSpec S z t α) : OuterMFacts E S z t where
  gen_four := (h.outerE.eFacts611 h.wFacts h.sporadic).gen_four
  cent_z := fun m hm hmz => by
    have : m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) :=
      ⟨hm, mem_centralizer_singleton_iff.2 hmz⟩
    rw [h.cent_z_normU] at this
    exact this.1
  centZ := h.centZ
  cardM := h.card_M hα
  NH_le := h.normHE_le_normU

end OuterS8Hyp

end CFSG.EvenSporadicStandard.Fin76b
