module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSpAut
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinVac
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinReduce
public import CFSG.GH74.Generic.S1.Exo.NbCenterClasses
public import CFSG.GH74.GLS.Stage1.Main.Gen4NoL34Proof
public import CFSG.ClassicalInvolution.Q3.TA3SmallBase
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSL4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.GH74.L5U5 CFSG.LieType.Steinberg TwinFr

theorem smallTwinLeaf_of_facts
    (hG : GH74.Generic.GenericKnownFacts) (hF : GH74.E2.E2ComponentFacts)
    (hL4 : SL4FrameOuterQ8Free) (hU4 : SU4FrameOuterQ8Free) (h2M12 : Twin2M12Leaf)
    (h2Sz8 : Twin2Sz8Leaf) (h2An : Twin2AnLeaf) : SmallTwinLeaf := by
  intro hGH Y _ _ hA hQ hsmall R S t hd hc hE2 c hcN hc1 hy
  have hH := twinHyp_fstar hd hc hE2 hsmall
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hq := isQuasisimple_fstar hQ
  have hZ2 := isPGroup_center_fstar hc
  have hne : Subgroup.center ↥(genFittingFStar Y) ≠ ⊥ := by
    obtain ⟨z, hz, rfl⟩ := hcN
    intro hbot
    rw [hbot, SetLike.mem_coe, Subgroup.mem_bot] at hz
    exact hc1 (by rw [hz]; rfl)
  have hgh : GH74.GHList (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y)) := by
    have := hQ.2
    exact ghList_of_small (smallList hGH _ hq.2.2 (twoSubgroupsFourGenerated_of_surjective
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hsmall))
  rcases GH74.Generic.S1.Exo.nb_center_classes hG hF hq hZ2 hsmall hgh hne with
    hS | ⟨n, h7, h11, hn⟩ | ⟨hl, -⟩ | h2 | h2 | hL | ⟨F, _, _, hodd, ⟨e⟩⟩
  · exact (hH.false_of_sl2 hS).elim
  · rcases (by omega : n = 7 ∨ 8 ≤ n) with rfl | h8
    · exact (hH.false_of_twoA7 hn).elim
    · exact h2An Y hA hQ hsmall ⟨n, h8, h11, hn⟩ R S t hd hc hE2 c hcN hc1 hy
  · exact (GH74.GLS.Stage1.Main.l34_cover_any _ hq hZ2 hl hne hsmall).elim
  · exact h2M12 Y hA hQ hsmall h2 R S t hd hc hE2 c hcN hc1 hy
  · exact h2Sz8 Y hA hQ hsmall h2 R S t hd hc hE2 c hcN hc1 hy
  · rcases hL with ⟨F, _, _, hF4, ⟨e⟩⟩ | ⟨q, F, _, _, hFq, hq4, ⟨e⟩⟩
    · have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
      exact hH.good_of_model hodd (model_frame (ModelData.lin F)
        (GH74.L5U5.two_ne_zero_of_odd_card hodd) (lin_sl2_equiv_H2 F)) lin_frame3
        (fun u hu huc => lin_conj hF4 hu huc) (hL4 F hF4) e
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
        (fun u hu huc => uni_conj hFq hq4 hu huc) (hU4 F p f hFq hq4) e
  · exact hH.good_of_model hodd (sp4_frame (GH74.L5U5.two_ne_zero_of_odd_card hodd)) sp4_frame3
      (fun u hu huc => sp4_conj hodd hu huc) (sp4FrameOuterQ8Free_holds F hodd) e

end CFSG.ClassicalInvolution.Q3.TA3
