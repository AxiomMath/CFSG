module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2End175
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndModel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2EndData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundation

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2End

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2
open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.Endgame

theorem false_of_config
    (h32 : AS76b.Lemma32) {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : AS76b.Hyp31 A)
    (e : ↥A ⧸ center ↥A ≃* Blueprint.NativeSporadic.Carrier .J2) (hF : J2EndFacts)
    {ψ : normalizer (A : Set G) →* ↥R} (hψ : IsActionHom A (P.subgroupOf R) ψ)
    (hc : YCensus (P.subgroupOf R) (ExcClass R j2E0Sub)) {g : G}
    (hg : g ∉ normalizer (A : Set G)) {RK T : Subgroup G}
    (hR : IsSylowOf 2 RK (centralizer (A : Set G)))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTN : T ≤ normalizer (A : Set G)) (hRN : RK ≤ normalizer (rightConjugate A g : Set G)) :
    False :=
  false_of_endgame h32 hA P_le_R R_le_normalizer commutatorElement_mem_P
    (endFacts_of_j2EndFacts hF) hψ hc (fun _ ht2 htX hQ => odd_card_center h32 hA e hψ ht2 htX hQ)
    hg hR hT hTN hRN

theorem sporadicCaseOdd_J2_of_check
    {sG roots sG' roots' : Array ℕ} {nodes nodes' : Array CFSG.KC.Census.NodeP}
    {cS cS' : CFSG.KC.Census.ArrCertP} {wcs wcs' : Array (Array CFSG.KC.Census.ArrCertP)}
    {excs : List CFSG.KC.Census.ExcRefP} (hII : j2CheckWII sG roots nodes cS wcs = true)
    (hX : j2CheckWExc j2E0 sG' roots' nodes' cS' wcs' excs = true)
    (hE : j2EndCheck j2E0 j2EndA0 j2EndC0 j2EndLeaves j2EndN0 = true)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .J2 := by
  intro G _ _ A hH hodd ⟨e⟩
  have hyp : AS76b.Hyp31 A :=
    ⟨hH.standard, hypII_of_yCensus j2AutModel (j2_yCensusII hII) hH.standard.1.1 e, hodd,
      by have := hH.rank; omega, hH.not_normal⟩
  obtain ⟨ψ, hψ⟩ := exists_isActionHom j2AutModel hyp.standard.1.1 e
  obtain ⟨g, hg, RK, T, hR, hT, hTN, hRN, -, -, -⟩ :=
    AS76b.section3Config_of h32 h33 RankTwoFoundation.asc75Theorem4 AS76b.asc08Lemma34 G A hyp
  exact false_of_config h32 hyp e (j2EndFacts_of_check hE) hψ (j2_yCensusExc hX) hg hR hT hTN
    hRN

end CFSG.ComponentClassification.RankTwoSporadic.J2End
