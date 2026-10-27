module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXCriterion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXOneComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXCaseOne

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem EscapingLift.fusionStronglyEmbedded_of_component (hu : EscapingLift B z u)
    (h : Setting J Q B) (hz : FourGen Q z) (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u))
    {L : Subgroup (QuasiQuotient u)} (hL : CFSG.IsComponent L) (heL : quasiCentral u ∉ L) :
    fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) := by
  have hc := hu.baseConfig h hz hrank
  exact hu.fusionStronglyEmbedded_of_quasiQuotient h hz
    (H := L ⊔ Subgroup.zpowers (quasiCentral u))
    (fun t ht => hc.involution_mem_component_sup hL heL (quasi_orderOf_mk u ht))
    (fun x hx => hc.mul_self_ne_of_mem_component_sup hL heL hx)

namespace BadLift

theorem quasiCentral_mem_component (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) {L : Subgroup (QuasiQuotient u)}
    (hL : CFSG.IsComponent L) : quasiCentral u ∈ L := by
  by_contra heL
  exact hu.not_embedded (hu.toEscapingLift.fusionStronglyEmbedded_of_component h hz hrank hL heL)

theorem exists_oneComponent (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    ∃ L : Subgroup (QuasiQuotient u),
      OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L :=
  (hu.baseConfig h hz hrank).exists_oneComponent (three_le_twoRank_quasiQuotient hrank)
    (quasiBar_mul_self u) (zpowers_quasiBar_normal u)
    fun _ hL => hu.quasiCentral_mem_component h hz hrank hL

end BadLift

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
