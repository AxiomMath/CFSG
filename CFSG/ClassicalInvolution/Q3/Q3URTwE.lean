module

public import CFSG.ClassicalInvolution.Q3.Q3URTwD
public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3URTwB
public import CFSG.ClassicalInvolution.Q3.Q3URTwC

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups


section Chain

theorem UChain2.nonempty (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G}
    {z : G} (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .PSU (2 + 1)) (conjClass3 K) z) :
    Nonempty (UChain2 K z) := by
  classical
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hΩ := hR.inClass
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z := h3 G K z hR
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have h2 := two_ne_zero_gf9
  obtain ⟨c⟩ := exists_uctx3_member hΩ hex hsingle hR.cls hP1 hO3 hshape hK hR.cls
  obtain ⟨nd⟩ := c.nonempty_nodes
  have hj₀z := nd.mem 0 (by omega)
  have hj₁z := nd.mem 1 (by omega)
  have hw₀ := nd.isCl 0 (by omega)
  have hw₁ := nd.isCl 1 (by omega)
  have hKj₀ : Commutes K (nd.j 0) := nd.commK 0 (by omega)
  have hKj₁ : Commutes K (nd.j 1) := nd.commK 1 (by omega)
  have hnc : ¬ Commutes (nd.j 0) (nd.j 1) := nd.adj 0 (by omega)
  have hinj : nd.j 0 ≠ nd.j 1 := nd.inj 0 (by omega) 1 (by omega) (by omega)
  have hj₀K : nd.j 0 ≠ K := nd.ne_K 0 (by omega)
  have hj₁K : nd.j 1 ≠ K := nd.ne_K 1 (by omega)
  have hD1 : ∀ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ K → Commutes K L :=
    fun L hL hLK => commutes_K_of_neU3 c.hm hΩ hex hK hR.cls hP1 hO3 c.d hL hLK
  have hD1all : ∀ N ∈ conjClass3 K, ∀ u : G, IsClassicalMember3 N u →
      ∀ L ∈ centralizingMembers (conjClass3 K) {u}, L ≠ N → Commutes N L :=
    fun N hN u hu L hL hLN => commutes_of_centralizing3 hΩ hsingle hR.cls hD1 hN hu hL hLN
  have hlayer : ∀ N ∈ conjClass3 K, Commutes K N → N ≤ nd.j 0 ⊔ nd.j 1 := by
    intro N hN hKN
    have hNz : N ∈ centralizingMembers (conjClass3 K) {z} :=
      ⟨hN, le_centralizer_of_commutes3 hKN.symm hR.cls.mem⟩
    have hNK : N ≠ K := fun h => not_commutes_self3 hR.cls (h ▸ hKN)
    obtain ⟨zN, hzN⟩ := hΩ.classical N hN
    obtain ⟨R, i, hRi, hNR, -⟩ := c.exists_rootData hNz hNK hzN
    refine le_of_locImg_le3 hΩ hex hP1 hO3 hNz (N := nd.j 0 ⊔ nd.j 1) ?_
    rw [hNR, locImg_sup3 (le_centralizingLayer hj₀z) (le_centralizingLayer hj₁z),
      nd.img 0 (by omega), nd.img 1 (by omega), ← Subgroup.map_sup, LcU_node_sup_eq_top3]
    exact Subgroup.map_mono le_top
  have hnorm : conjSub (nd.w 0) (nd.j 1) = nd.j 1 :=
    c.conjSub_eq_of_commute_roots hj₀z hj₁z
      (isLongRootSU2_LcU h2 c.hn (nodePair 2 0 (by omega)))
      (isLongRootSU2_LcU h2 c.hn (nodePair 2 1 (by omega))) (nd.img 0 (by omega))
      (nd.img 1 (by omega))
      (signGroupU_comm (zEltU_mem_signGroupU _) (zEltU_mem_signGroupU _)) hw₀.mem
      hw₀.orderOf_eq_two
  obtain ⟨c'⟩ := exists_uctx3_member hΩ hex hsingle hR.cls hP1 hO3 hshape hj₁z.1 hw₁
  have hKw₁ : K ∈ centralizingMembers (conjClass3 K) {nd.w 1} :=
    ⟨hK, le_centralizer_of_commutes3 hKj₁ hw₁.mem⟩
  have hKj₁' : K ≠ nd.j 1 := hj₁K.symm
  obtain ⟨R, i, hRi, hKR, -⟩ := c'.exists_rootData hKw₁ hKj₁' hR.cls
  obtain ⟨R', i', hRi', hcomm', hne', hnc', hsup⟩ := exists_partner_two_su3 hRi
  obtain ⟨β, hβ, hβJ, hβR⟩ := exists_member_of_rootU3 c'.hm c'.hΩ c'.hex c'.hK c'.hz c'.hP1 c'.hO3
    c'.d (R := R') ⟨i', hRi'⟩
  obtain ⟨v, hv⟩ := hΩ.classical β hβ.1
  have hKβ : ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β :=
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
    exact hj₀K (eq_of_locImg_le_Q₀U3 c.hm hΩ hex hK hR.cls hP1 hO3 c.d hj₀z
      (locImg_self_le_Q₀U3 c.hm hj₀z.1 hcl' c.d))
  obtain ⟨hP1x, hO3x⟩ := hP G K z hR (nd.j 0) hj₀z.1 (nd.w 0) hw₀ hKj₀ hzw₀
  have hlay := centralizes_layer3 hnab hΩ hconn hsingle hK hR.cls hD1 hj₀z.1 hj₁z.1 hw₀ hw₁
    hKj₀ hKj₁ hnc (nd.wcomm 0 (by omega) 1 (by omega)) hlayer hnorm
    (fun t ht1 ht2 htK htJ => c'.layer_dichotomy hKw₁ hKj₁' hR.cls ht1 ht2 htK htJ)
  have hzw₀c : z * nd.w 0 = nd.w 0 * z := hKj₀ z hR.cls.mem (nd.w 0) hw₀.mem
  have hKx : K ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} := by
    refine ⟨hK, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k z :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hR.cls.subnormal hk)
    have c₂ : Commute k (nd.w 0) := hKj₀ k hk (nd.w 0) hw₀.mem
    exact c₁.mul_right c₂
  have hMx : nd.j 0 ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} := by
    refine ⟨hj₀z.1, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k z :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_commutes3 hKj₀.symm hR.cls.mem hk)
    have c₂ : Commute k (nd.w 0) :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hw₀.subnormal hk)
    exact c₁.mul_right c₂
  have hβx : β ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} := ⟨hβ.1, hlay β hβ hβJ⟩
  have hxc := not_subset_center_of_commuting_involutions3 hnab hR.cls.orderOf_eq_two
    hw₀.orderOf_eq_two hzw₀c hzw₀
  have hβw₁ : Commutes (nd.j 1) β := hD1all (nd.j 1) hj₁z.1 (nd.w 1) hw₁ β hβ hβJ
  have hβj₀ : β ≠ nd.j 0 := by
    intro h
    have : nd.j 0 ∈ centralizingMembers (conjClass3 K) {nd.w 1} := h ▸ hβ
    exact hnc (hD1all (nd.j 1) hj₁z.1 (nd.w 1) hw₁ (nd.j 0) this hinj).symm
  have hnβM : ¬ Commutes β (nd.j 0) := by
    intro hc
    have h₁ : β ≤ Subgroup.centralizer ({nd.w 0} : Set G) :=
      le_centralizer_of_commutes3 hc hw₀.mem
    have h₂ : β ≤ Subgroup.centralizer ({z * nd.w 0} : Set G) := hβx.2
    have h₃ := le_centralizer_of_mul_right3 h₁ h₂
    exact hnKβ (hD1 β ⟨hβ.1, h₃⟩ hKβne.symm)
  have htwin := twin_condition_x3 hD1all hK hj₀z.1 hR.cls hw₀ hKj₀ rfl
  have hs := chainSign_images3 hΩ hex hR.ih hxc hP1x hO3x hR.cls hv hw₀ hKx hβx hMx rfl hzw₀
    hKj₀ hj₀K.symm hKβne hβj₀ hnKβ hnβM hvK htwin
  have hpair₁₂ := unitary_of_chainSign_images3 hΩ hex hP1x hO3x hKx hβx hMx hs hKβ
  have hcl1 : conjClass3 (nd.j 1) = conjClass3 K := Q3TC.conjClass3_eq_of_mem hj₁z.1
  have hsingle' : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g (nd.j 1) := by
    intro L hL
    rw [← hcl1] at hL
    obtain ⟨g, rfl⟩ := hL
    exact ⟨g, rfl⟩
  have hzv : z * v = v * z := by
    obtain ⟨W, hW⟩ := hKβ
    exact unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW hR.cls.mem hv.mem
      hR.cls.orderOf_eq_two hv.orderOf_eq_two
  have hlayer' : ∀ N ∈ conjClass3 K, Commutes (nd.j 1) N → N ≤ β ⊔ K := by
    intro N hN hcN
    have hNw : N ∈ centralizingMembers (conjClass3 K) {nd.w 1} :=
      ⟨hN, le_centralizer_of_commutes3 hcN.symm hw₁.mem⟩
    have hNJ : N ≠ nd.j 1 := fun h => not_commutes_self3 hw₁ (h ▸ hcN)
    obtain ⟨zN, hzN⟩ := hΩ.classical N hN
    obtain ⟨R'', i'', hRi'', hNR, -⟩ := c'.exists_rootData hNw hNJ hzN
    refine le_of_locImg_le3 hΩ hex c'.hP1 c'.hO3 hNw (N := β ⊔ K) ?_
    rw [hNR, locImg_sup3 (le_centralizingLayer hβ) (le_centralizingLayer hKw₁), hβR, hKR,
      ← Subgroup.map_sup, sup_comm, hsup]
    exact Subgroup.map_mono le_top
  have hlay' := centralizes_layer3 hnab hΩ hconn hsingle' hj₁z.1 hw₁
    (fun L hL hLj => hD1all (nd.j 1) hj₁z.1 (nd.w 1) hw₁ L hL hLj) hβ.1 hK hv hR.cls
    hβw₁ hKj₁.symm (fun h => hnKβ h.symm) hzv.symm hlayer' hvK
    (fun s hs1 hs2 hsK hsJ => c.layer_dichotomy hj₁z hj₁K hw₁ hs1 hs2 hsK hsJ)
  have hw₁v : nd.w 1 * v = v * nd.w 1 := hβw₁ (nd.w 1) hw₁.mem v hv.mem
  have hw₁ne : nd.w 1 ≠ v := by
    intro h
    have hcl' : IsClassicalMember3 β (nd.w 1) :=
      @Eq.subst G (fun y => IsClassicalMember3 β y) v (nd.w 1) h.symm hv
    exact hβJ (eq_of_locImg_le_Q₀U3 c'.hm c'.hΩ c'.hex c'.hK c'.hz c'.hP1 c'.hO3 c'.d hβ
      (locImg_self_le_Q₀U3 c'.hm hβ.1 hcl' c'.d))
  have hj₁x' : nd.j 1 ∈ centralizingMembers (conjClass3 K) {nd.w 1 * v} := by
    refine ⟨hj₁z.1, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k (nd.w 1) :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hw₁.subnormal hk)
    have c₂ : Commute k v :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_commutes3 hβw₁ hv.mem hk)
    exact c₁.mul_right c₂
  have hβx' : β ∈ centralizingMembers (conjClass3 K) {nd.w 1 * v} := by
    refine ⟨hβ.1, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k (nd.w 1) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_commutes3 hβw₁.symm hw₁.mem hk)
    have c₂ : Commute k v :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hv.subnormal hk)
    exact c₁.mul_right c₂
  have hj₀x' : nd.j 0 ∈ centralizingMembers (conjClass3 K) {nd.w 1 * v} :=
    ⟨hj₀z.1, hlay' (nd.j 0) hj₀z hj₀K⟩
  have hxc' := not_subset_center_of_commuting_involutions3 hnab hw₁.orderOf_eq_two
    hv.orderOf_eq_two hw₁v hw₁ne
  have htwin' := twin_condition_x3 hD1all hj₁z.1 hβ.1 hw₁ hv hβw₁ rfl
  have hPR := hP G (nd.j 1) (nd.w 1) (Q3TC.RouteD3Setup.of_mem_conjClass3 hR hj₁z.1 hw₁) β
    (by rw [hcl1]; exact hβ.1) v hv hβw₁ hw₁ne
  rw [hcl1] at hPR
  obtain ⟨hP1x', hO3x'⟩ := hPR
  have hneβ1 : β ≠ nd.j 1 := hβJ
  refine ⟨{ j0 := nd.j 0, j1 := nd.j 1, β := β, w0 := nd.w 0, w1 := nd.w 1, t := v,
            hj0 := hj₀z.1, hj1 := hj₁z.1, hβ := hβ.1, cl0 := hw₀, cl1 := hw₁, clβ := hv,
            c0 := hKj₀, c1 := hKj₁, cβ1 := hβw₁.symm, nKβ := hnKβ, nβ0 := hnβM, n01 := hnc,
            pKβ := hKβ, pβ0 := hpair₁₂, p01 := nd.pair 0 (by omega), neKβ := hKβne,
            neK0 := hj₀K.symm, neK1 := hj₁K.symm, neβ0 := hβj₀, ne01 := hinj, neβ1 := hneβ1,
            ztEq := hzv, t0Eq := ?_, w01Eq := nd.wcomm 0 (by omega) 1 (by omega), z0Eq := hzw₀c,
            z1Eq := hKj₁ z hR.cls.mem (nd.w 1) hw₁.mem, t1Eq := hw₁v.symm, Kx := hKx,
            j0x := hMx, βx := hβx, zne0 := hzw₀, xc := hxc, twin := htwin, vK := hvK,
            P1x := hP1x, O3x := hO3x, j1x' := hj₁x', j0x' := hj₀x', βx' := hβx',
            w1net := hw₁ne, xc' := hxc', twin' := htwin', vj1 := hnorm, P1x' := hP1x',
            O3x' := hO3x' }⟩
  obtain ⟨W, hW⟩ := hpair₁₂
  exact unitaryStandardPair_involutions_commute card_gf9 (by norm_num) hW hv.mem hw₀.mem
    hv.orderOf_eq_two hw₀.orderOf_eq_two

end Chain

end CFSG.ClassicalInvolution.Q3.Q3W
