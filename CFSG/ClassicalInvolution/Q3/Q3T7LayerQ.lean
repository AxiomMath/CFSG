module

public import CFSG.ClassicalInvolution.Q3.Q3T7Layer
public import CFSG.ClassicalInvolution.Asc77.AscR10G2Q

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Disc3

section Section


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {c : G}

theorem hypOmegaModU_layerFam3 (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hne : (tqMembers3 Ω c).Nonempty) : HypOmegaModU (.sl2 3 1) (layerFam3 Ω c) :=
  T3CII.hypOmegaModU_oddQuotientFamily (hypOmegaModU_exactPair3 hs hc2 hne)

theorem layerQuot3_oddCore_eq_bot :
    classicalInvolutionOddCore (layerQuot3 Ω c) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree ↥(exactLayer3 Ω c)

theorem card_layerQuot3_lt (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) :
    Nat.card (layerQuot3 Ω c) < Nat.card G :=
  lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective))
    (card_exactLayer3_lt Ω c hnc)

theorem layer_commutes_of_not_conj (hs : AscStand3 Ω K) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G) (hne : (tqMembers3 Ω c).Nonempty)
    (hA : ∀ L ∈ layerFam3 Ω c, AEmpty (layerFam3 Ω c) L) {A B : Subgroup (layerQuot3 Ω c)}
    (hAm : A ∈ layerFam3 Ω c) (hBm : B ∈ layerFam3 Ω c)
    (hAB : ¬ ∃ g : layerQuot3 Ω c, conjSub g A = B) : Commutes A B :=
  hs.ih.thm4 (by norm_num) (by norm_num) (layerQuot3 Ω c) (card_layerQuot3_lt hnc) (layerFam3 Ω c)
    (hypOmegaModU_layerFam3 hs hc2 hne) layerQuot3_oddCore_eq_bot hA A hAm B hBm hAB

end Section

end CFSG.ClassicalInvolution.Q3.Q3T7
