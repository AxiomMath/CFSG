module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H69O
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EFacts

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

theorem toOHyp69 : OHyp69 L z t T E B β S :=
  { oe := h.outerE, wf := h.wFacts, ef := h.outerE.eFacts69 h.wFacts h.sporadic, ob := h.outerB,
    S2 := h.S2, SC := h.SC, Smax := h.Smax, zS := h.zS, D8 := h.D8, BS := h.BS, odd := h.odd,
    h67 := h.h67, h68 := h.h112, fus := h.exists_fus, cU := h.cU }

theorem card_M {α : G} (hα : AlphaSpec S z t α) :
    Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) = 245760 := by
  have hH := h.toOHyp69
  have h1 := card_conj_orbit_mul_card_cent (normalizer ((S ⊔ E : Subgroup G) : Set G)) z
  rw [hH.orbit_eq_X, hH.X_card hα, h.cent_z_normU, h.card_normHE] at h1
  omega

end OuterS8Hyp

end CFSG.EvenSporadicStandard.Fin76b
