module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreZComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYSummary

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace EscapingLift

theorem baseConfig_of_ne_top (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hne : quasiImage B u ≠ ⊤) : BaseConfig (quasiImage B u) (quasiCentral u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, -, -⟩ := hu.exists_sylow h hz
  have hcore := h.gamma_le _ T hT
  obtain ⟨hcen, hord⟩ := hu.quasiCentral_mem_center h
  refine ⟨pPrimeCore_quotient_pPrimeCore_eq_bot 2, hcen, hord, hne,
    T.mapSurjective (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hT
  · rw [Sylow.coe_mapSurjective, ← gamma_image_odd_normal_quotient T _ (quasi_oddCore_odd u) 2]
    exact Subgroup.map_mono hcore

theorem quasiImage_ne_top (hu : EscapingLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) : quasiImage B u ≠ ⊤ :=
  (hu.baseConfig h hz hrank).ne_top

theorem two_le_pRank_quasiNormalizer (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) : 2 ≤ CFSG.Open.pRank 2 (quasiNormalizer u) :=
  (hu.two_le_pRank h hz).trans (CFSG.SectionRank.pRank_mono (by decide) inf_le_right)

theorem pRank_eq_two_of_quasiImage_eq_top (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (htop : quasiImage B u = ⊤) :
    CFSG.Open.pRank 2 (quasiNormalizer u) = 2 := by
  have h2 := hu.two_le_pRank_quasiNormalizer h hz
  by_contra hne
  exact hu.quasiImage_ne_top h hz (by omega) htop

theorem fusionStronglyEmbedded_of_component_of_baseConfig (hu : EscapingLift B z u)
    (h : Setting J Q B) (hz : FourGen Q z) (hc : BaseConfig (quasiImage B u) (quasiCentral u))
    {L : Subgroup (QuasiQuotient u)} (hL : CFSG.IsComponent L) (heL : quasiCentral u ∉ L) :
    fusionStronglyEmbedded ((B.map (QuotientGroup.mk' (Subgroup.center J))).subgroupOf
      (localInvolutionPointHull (z : J ⧸ Subgroup.center J) (u : J ⧸ Subgroup.center J))) :=
  hu.fusionStronglyEmbedded_of_quasiQuotient h hz
    (H := L ⊔ Subgroup.zpowers (quasiCentral u))
    (fun _ ht => hc.involution_mem_component_sup hL heL (quasi_orderOf_mk u ht))
    (fun _ hx => hc.mul_self_ne_of_mem_component_sup hL heL hx)

end EscapingLift

namespace BadLift

theorem quasiCentral_mem_component_of_ne_top (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (hne : quasiImage B u ≠ ⊤) {L : Subgroup (QuasiQuotient u)}
    (hL : CFSG.IsComponent L) : quasiCentral u ∈ L := by
  by_contra heL
  exact hu.not_embedded (hu.toEscapingLift.fusionStronglyEmbedded_of_component_of_baseConfig h
    hz (hu.baseConfig_of_ne_top h hz hne) hL heL)

theorem exists_oneComponent_of_ne_top (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (hne : quasiImage B u ≠ ⊤) :
    ∃ L : Subgroup (QuasiQuotient u),
      OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L :=
  (hu.baseConfig_of_ne_top h hz hne).exists_oneComponent_of_sq (quasiBar_mul_self u)
    (zpowers_quasiBar_normal u) fun _ hL => hu.quasiCentral_mem_component_of_ne_top h hz hne hL

theorem false_of_szModel_of_ne_top
    (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (hne : quasiImage B u ≠ ⊤) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hZ : Nat.card (Subgroup.center L) = 2)
    (eS : L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) : False :=
  hu.not_embedded (hu.toEscapingLift.fusionStronglyEmbedded_of_quasiQuotient h hz (H := L)
    (fun _ ht => hL.mem_of_szModel hZ eS (quasi_orderOf_mk u ht))
    (fun _ hx => hL.mul_self_ne_of_szModel (hu.baseConfig_of_ne_top h hz hne) hZ eS hx))

theorem exists_alternating_component_of_ne_top
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) (hne : quasiImage B u ≠ ⊤) :
    ∃ L : Subgroup (QuasiQuotient u),
      OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L ∧
      Nat.card (Subgroup.center L) = 2 ∧ quasiBar u ∉ L ∧
      Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) ∧
      ∀ x : QuasiQuotient u, orderOf x = 2 →
        x ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  have hc := hu.baseConfig_of_ne_top h hz hne
  obtain ⟨L, hL⟩ := hu.exists_oneComponent_of_ne_top h hz hne
  obtain ⟨hZ, hvL, hcov⟩ := hL.center_card_and_cover hc (quasiBar_mul_self u)
    (zpowers_quasiBar_normal u) (canonicalBelow_quasiQuotient IH u)
  rcases hcov with hL2 | hS
  · obtain ⟨e₅⟩ :=
      CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
    let eA := hL2.some.trans e₅
    exact ⟨L, hL, hZ, hvL, ⟨eA⟩, fun x hx => hL.mem_sup_centralizer_of_alternating hc
      (quasiBar_mul_self u) (zpowers_quasiBar_normal u) hZ eA hx⟩
  · exact (hu.false_of_szModel_of_ne_top h hz hne hL hZ hS.some).elim

end BadLift

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
