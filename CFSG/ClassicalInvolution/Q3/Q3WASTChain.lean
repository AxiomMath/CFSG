module

public import CFSG.ClassicalInvolution.Q3.Q3WASTInner
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3WASEnd4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ComponentClassification.CatalogueBHigherLinearAction CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

set_option linter.unusedSectionVars false

section Row

theorem chainRow3_two (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3) : ChainRow3 2 := by
  intro G _ _ _ hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hΩ := hR.inClass
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨c⟩ := exists_actx3_member hΩ hex hsingle hR.cls hP1 hO3 hshape hK hR.cls
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hj₀z := nd.mem 0 (by omega)
  have hj₁z := nd.mem 1 (by omega)
  have hw₀ := nd.isCl 0 (by omega)
  have hw₁ := nd.isCl 1 (by omega)
  have hKj₀ : Commutes K (nd.j 0) := nd.commK 0 (by omega)
  have hKj₁ : Commutes K (nd.j 1) := nd.commK 1 (by omega)
  have hnc : ¬ Commutes (nd.j 0) (nd.j 1) := nd.adj 0 (by omega)
  have hinj : nd.j 0 ≠ nd.j 1 := nd.inj 0 (by omega) 1 (by omega) (by omega)
  have hlayer : ∀ N ∈ conjClass3 K, Commutes K N → N ≤ nd.j 0 ⊔ nd.j 1 := by
    intro N hN hKN
    have hNz : N ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hN, le_centralizer_of_commutes3 hKN.symm hR.cls.mem⟩
    have hNK : N ≠ K := fun h => not_commutes_self3 hR.cls (h ▸ hKN)
    obtain ⟨zN, hzN⟩ := hΩ.classical N hN
    obtain ⟨R, i, hRi, hNR, -⟩ := c.exists_rootData hNz hNK hzN
    refine le_of_locImg_le3 hΩ hex hP1 hO3 hNz (N := nd.j 0 ⊔ nd.j 1) ?_
    rw [hNR, locImg_sup3 (le_centralizingLayer hj₀z) (le_centralizingLayer hj₁z),
      nd.img 0 (by omega), nd.img 1 (by omega), ← Subgroup.map_sup, Lc_node_sup_eq_top3 h2]
    exact Subgroup.map_mono le_top
  have hnorm : conjSub (nd.w 0) (nd.j 1) = nd.j 1 :=
    c.conjSub_eq_of_commute_roots hj₀z hj₁z
      (isLongRootSL2_Lc h2 c.hn (nodePair 2 0 (by omega)))
      (isLongRootSL2_Lc h2 c.hn (nodePair 2 1 (by omega))) (nd.img 0 (by omega))
      (nd.img 1 (by omega))
      (signGroup_comm (zElt_mem_signGroup _) (zElt_mem_signGroup _)) hw₀.mem hw₀.orderOf_eq_two
  obtain ⟨c'⟩ := exists_actx3_member hΩ hex hsingle hR.cls hP1 hO3 hshape hj₁z.1 hw₁
  have hKw₁ : K ∈ centralizingMembers (conjClass3 K) {nd.w 1} :=
    ⟨hK, le_centralizer_of_commutes3 hKj₁ hw₁.mem⟩
  have hKj₁' : K ≠ nd.j 1 := (nd.ne_K 1 (by omega)).symm
  obtain ⟨R, i, hRi, hKR, -⟩ := c'.exists_rootData hKw₁ hKj₁' hR.cls
  obtain ⟨R', i', hRi', hcomm', hne', hnc'⟩ := exists_partner_two3 h2 hRi
  obtain ⟨β, hβ, hβJ, hβR⟩ := exists_member_of_root3 c'.hm c'.hΩ c'.hex c'.hK c'.hz c'.hP1 c'.hO3
    c'.d (R := R') ⟨i', hRi'⟩
  obtain ⟨v, hv⟩ := hΩ.classical β hβ.1
  have hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β :=
    c'.stdpair_of_root hKw₁ hβ hRi hRi' hKR hβR hcomm' hne' hnc'
  have hnKβ : ¬ Commutes K β := fun h => hnc' ((c'.commutes_iff_root hKw₁ hβ hRi hKR hβR).mp h)
  have hKβne : K ≠ β := fun h =>
    hne' (c'.rootInv_eq_of_locImg_eq hRi hRi' hKR hβR (congrArg (locImg _ _) h))
  have hvK : conjSub v K = K :=
    c'.conjSub_eq_of_commute_roots hβ hKw₁ hRi' hRi hβR hKR hcomm'.symm hv.mem hv.orderOf_eq_two
  have hzw₀ : z ≠ nd.w 0 := by
    intro h
    have hcl' : IsClassicalMember3 (nd.j 0) z :=
      @Eq.subst G (fun y => IsClassicalMember3 (nd.j 0) y) (nd.w 0) z h.symm hw₀
    exact nd.ne_K 0 (by omega) (eq_of_locImg_le_Q₀3 c.hm hΩ hex hK hR.cls hP1 hO3 c.d hj₀z
      (locImg_self_le_Q₀3 c.hm hj₀z.1 hcl' c.d))
  obtain ⟨hP1x, hO3x⟩ := hP G K z hR (nd.j 0) hj₀z.1 (nd.w 0) hw₀ hKj₀ hzw₀
  exact exists_twin_chain3 hnab hΩ hconn hex hR.ih hsingle hK hR.cls
    (fun L hL hLK => commutes_K_of_ne3 c.hm hΩ hex hK hR.cls hP1 hO3 c.d hL hLK)
    hj₀z.1 hj₁z.1 hw₀ hw₁ (nd.ne_K 0 (by omega)) hinj hKj₀ hKj₁ hnc
    (nd.wcomm 0 (by omega) 1 (by omega)) hlayer hnorm
    (fun t ht1 ht2 htK htJ => c'.layer_dichotomy hKw₁ hKj₁' hR.cls ht1 ht2 htK htJ) hP1x hO3x
    hβ hβJ hv hnKβ hKβne hvK hKβ (nd.pair 0 (by omega))

end Row

end CFSG.ClassicalInvolution.Q3.Q3W
