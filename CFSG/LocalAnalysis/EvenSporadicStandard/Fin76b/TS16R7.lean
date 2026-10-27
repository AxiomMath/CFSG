module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RCtx
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16R7EB

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem EB_le_centS : L ⊓ centralizer ({t} : Set G) ≤ centralizer (S : Set G) := by
  rw [EB_eq_sup c.hyp.wFacts c.hyp.outerB (fun e he => c.hyp.outerE.t_comm_E he)]
  refine sup_le ?_ ?_
  · intro e he
    exact mem_centralizer_iff.2 fun s hs => (mem_centralizer_iff.1 (c.SC hs) e he).symm
  · intro b hb
    exact mem_centralizer_iff.2 fun s hs => (c.BS b hb s hs).symm

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
