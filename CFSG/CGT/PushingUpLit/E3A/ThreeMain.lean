module

public import CFSG.RankThree.PartOne.SolD3.Inputs3
public import CFSG.CGT.PushingUpLit.E3A.ThreeBorel
public import CFSG.CGT.PushingUpLit.E3A.ThreeAlt
public import CFSG.CGT.PushingUpLit.E3A.ThreeSporadic
public import CFSG.CGT.PushingUpLit.E3A.Lin

public section

namespace CFSG.CGT.PushingUpLit.E3A

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.CGT.PushingUpLit.SolK CFSG.RankThree.PartOne.SolD3
open CFSG.Assembly (pCoreOf)

theorem wcBlockCentralizerThree_of_list
    (hSCL : SimpleCaseListStmt) : WCBlockCentralizerThree := by
  intro G _ _ hsimple hchar R X hRab hR4 hTI hmax hWC hunique hXN hXnorm hshort hnat hXC
  have h3 : Hyp3 G (Subgroup.normalizer (R : Set G)) X :=
    ⟨hsimple, hchar, hmax, hXN, hXnorm, hunique, hshort, hnat⟩
  obtain ⟨a, hb⟩ := exists_blk3 hshort hnat
  have hna : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨w, hw, hw1⟩ := hb.exists_ne_one
    refine ⟨a, w, fun hcomm => hw1 (hb.fix w hw ?_)⟩
    rw [hcomm]
    group
  have := hsimple
  have hwc : IsWC R := isWC_of_corBHyp
    (corBHyp_of_ti_of_weaklyClosed hRab (fun g => hTI g⁻¹) (fun g => hWC.2 g⁻¹))
  have hlist : ListGroup G := hSCL G hna R hwc hR4
  have hstd : StdPair G R := listWCIdentification_of_cert G hlist R hwc hR4
  have hR2 : IsPGroup 2 R := isPGroup_two_of_isElemAbelian hRab
  have hR1 : R ≠ ⊥ := ne_bot_of_four_le_card hR4
  have hSR : ∀ S : Sylow 2 G, R ≤ (S : Subgroup G) →
      (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) :=
    fun S hRS => hwc.le_normalizer_of_le_pGroup S.isPGroup' hRS
  rcases hlist with ⟨m, s, hm, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hodd, hs3, hmod⟩ |
    ⟨k, hk6, hk9, he⟩ | hM22 | hM23 | hM24
  · by_cases hm3 : 3 ≤ m
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      have : CharP K 2 := charP_two_of_card hK
      obtain ⟨-, hR'⟩ := hstd.of_psl hm3 K hK e
      have hCR := (lin_centralizer_le hm3 e hR').2
      exact false_of_W_le_R hb hXC fun w hw => hCR (hXC (pCoreOf_le_self X hw))
    · have hm2 : m = 2 := by omega
      subst hm2
      obtain ⟨-, ⟨S, hS⟩, -⟩ := hstd.of_psl2 hmod
      exact false_of_sylow_eq h3 hb hXC S hS
  · obtain ⟨-, ⟨S, hS⟩, -, S', hS'⟩ := hstd.of_psu3 hs hmod
    exact false_of_center_sylow h3 hb hXC S S' hS hS'
  · obtain ⟨-, ⟨S, hS⟩, -, S', hS'⟩ := hstd.of_sz hodd hs3 hmod
    exact false_of_center_sylow h3 hb hXC S S' hS hS'
  · exact false_of_alt_three hk6 hk9 he.some (hstd.card_alternating hk6 hk9 he) hstd.transitive
      h3 hb hXC
  · obtain ⟨e⟩ := hM22
    exact false_of_sylowCenterTwo h3 hb hR2 hR1 hSR hXC (sylowCenterTwo_m22.map_mulEquiv e.symm)
  · obtain ⟨e⟩ := hM23
    exact false_of_sylowCenterTwo h3 hb hR2 hR1 hSR hXC (sylowCenterTwo_m23.map_mulEquiv e.symm)
  · obtain ⟨e⟩ := hM24
    exact false_of_sylowCenterTwo h3 hb hR2 hR1 hSR hXC (sylowCenterTwo_m24.map_mulEquiv e.symm)

end CFSG.CGT.PushingUpLit.E3A
