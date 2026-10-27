module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinAlt
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinM12
public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3TwinSz8
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutL4b
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutU4b
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinVac
public import CFSG.GH74.E2.FactsK
public import CFSG.GH74.GLS.Stage1.Main.Gen4NoL34Proof
public import CFSG.GH74.Generic.GKFFinal
public import CFSG.GH74.Generic.S1.Exo.NbCenterClasses
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.TwinFr
open CFSG.GH74.L5U5 CFSG.LieType.Steinberg

theorem noCentralTwinR_of_gh74
    (hGH : GH74SectionalModels) {r : ℕ} (hr : 4 ≤ r) :
    NoCentralTwinR r := by
  intro Y _ _ R S t hd hc hE2 hQ hsmall c hcN hc1 y hy
  have hq8 := exists_q8Emb (by omega) hd hc.1
  have hH := twinHyp_fstar_R hd hc hE2 hsmall
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hq := isQuasisimple_fstar hQ
  have hZ2 := isPGroup_center_fstar_R hc
  have hne : Subgroup.center ↥(genFittingFStar Y) ≠ ⊥ := by
    obtain ⟨z, hz, rfl⟩ := hcN
    intro hbot
    rw [hbot, SetLike.mem_coe, Subgroup.mem_bot] at hz
    exact hc1 (by rw [hz]; rfl)
  have hgh : GH74.GHList (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) := by
    have := hQ.2
    exact ghList_of_small (TA3.smallList hGH _ hq.2.2 (twoSubgroupsFourGenerated_of_surjective
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hsmall))
  have hG := GH74.Generic.genericKnownFacts_of_griess
    ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hgood : GoodThreeElement R t := by
    rcases GH74.Generic.S1.Exo.nb_center_classes hG GH74.E2.e2ComponentFacts hq hZ2 hsmall hgh
      hne with hS | ⟨n, h7, h11, hn⟩ | ⟨hl, -⟩ | h2 | h2 | hL | ⟨F, _, _, hodd, ⟨e⟩⟩
    · exact (hH.false_of_sl2 hS).elim
    · rcases (by omega : n = 7 ∨ 8 ≤ n) with rfl | h8
      · exact (hH.false_of_twoA7 hn).elim
      · exact (false_of_alt_q8 hd hq8 hH h8 h11 hn).elim
    · exact (GH74.GLS.Stage1.Main.l34_cover_any _ hq hZ2 hl hne hsmall).elim
    · exact (false_of_m12_q8 hd hq8 hH h2).elim
    · exact (false_of_sz8_q8 hd hq8 hH h2).elim
    · rcases hL with ⟨F, _, _, hF4, ⟨e⟩⟩ | ⟨q, F, _, _, hFq, hq4, ⟨e⟩⟩
      · have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
        exact hH.good_of_model hodd (model_frame (ModelData.lin F)
          (GH74.L5U5.two_ne_zero_of_odd_card hodd) (lin_sl2_equiv_H2 F)) lin_frame3
          (fun u hu huc => lin_conj hF4 hu huc) (sl4FrameOuterQ8Free_holds F hF4) e
      · obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hFq
        obtain ⟨e2⟩ := nonempty_sl2_equiv_uni_H2 hFq
        have hodd' : Odd (Nat.card (fixedSubfield F p f)) := by
          rw [card_fixedSubfield hFq]
          exact Nat.odd_iff.2 (by omega)
        have hoddF : Odd (Nat.card F) := by
          rw [hFq]
          exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
        exact hH.good_of_model hodd' (model_frame (ModelData.uni hFq)
          (GH74.L5U5.two_ne_zero_of_odd_card hoddF) e2)
          (fun h3 => absurd h3 (by rw [card_fixedSubfield hFq]; omega))
          (fun u hu huc => uni_conj hFq hq4 hu huc) (su4FrameOuterQ8Free_holds F p f hFq hq4) e
    · exact hH.good_of_model hodd (sp4_frame (GH74.L5U5.two_ne_zero_of_odd_card hodd)) sp4_frame3
        (fun u hu huc => sp4_conj hodd hu huc) (sp4FrameOuterQ8Free_holds F hodd) e
  exact not_goodThreeElement_of_four_le hr hd hc.1 hgood

end CFSG.CGT.PushingUpLit.SolKNA.R4
