module

public import CFSG.ClassicalInvolution.Q3.Q3WASEnd4
public import CFSG.ClassicalInvolution.Q3.Q3WASChart3

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)
open scoped MatrixGroups

section Ker

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem ShapeADict.kerInvolutionFree_three3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G}
    (hz : IsClassicalMember3 K z) (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z)
    (d : ShapeADict 3 1 3 Ω z) : Transfer.KerInvolutionFree d.ψ := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hn : 2 ≤ 3 + 1 := by omega
  intro u hu hu2
  rcases Transfer.eq_one_or_coe_eq_neg_one (by omega : 1 ≤ 3 + 1) (d.ker_le hu) hu2 with h1 | h1
  · exact h1
  exfalso
  set T0 : Pair (3 + 1) := nodePair 3 0 (by omega) with hT0
  set T2 : Pair (3 + 1) := nodePair 3 2 (by omega) with hT2
  have hzu : zElt (GaloisField 3 1) T2 = u * zElt (GaloisField 3 1) T0 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, h1, neg_one_mul]
    exact zMat_nodePair_two_eq_neg
  have hψ : d.ψ (zElt (GaloisField 3 1) T0) = d.ψ (zElt (GaloisField 3 1) T2) := by
    rw [hzu, map_mul, MonoidHom.mem_ker.mp hu, one_mul]
  have hR0 : Lc (GaloisField 3 1) T0 ∈ longRootSet (K := GaloisField 3 1) hn :=
    ⟨_, isLongRootSL2_Lc h2 hn T0⟩
  have hR2 : Lc (GaloisField 3 1) T2 ∈ longRootSet (K := GaloisField 3 1) hn :=
    ⟨_, isLongRootSL2_Lc h2 hn T2⟩
  obtain ⟨L, hL, -, hLR⟩ := exists_member_of_root3 (m := 3) (by omega) hΩ hex hK hz hP1 hO3 d hR0
  obtain ⟨L', hL', -, hLR'⟩ := exists_member_of_root3 (m := 3) (by omega) hΩ hex hK hz hP1 hO3 d hR2
  obtain ⟨w, hw⟩ := hΩ.classical L hL.1
  obtain ⟨w', hw'⟩ := hΩ.classical L' hL'.1
  have hy : w ∈ locLayer Ω z := le_centralizingLayer hL hw.mem
  have hy' : w' ∈ locLayer Ω z := le_centralizingLayer hL' hw'.mem
  have hinv : d.ψ (zElt (GaloisField 3 1) T0) = locElt Ω z w hy :=
    psi_root_inv (by omega) odd_gf3 d (isLongRootSL2_Lc h2 hn T0) (by simpa using hLR)
      (le_centralizingLayer hL) hw.mem hw.orderOf_eq_two
  have hinv' : d.ψ (zElt (GaloisField 3 1) T2) = locElt Ω z w' hy' :=
    psi_root_inv (by omega) odd_gf3 d (isLongRootSL2_Lc h2 hn T2) (by simpa using hLR')
      (le_centralizingLayer hL') hw'.mem hw'.orderOf_eq_two
  have hwe : locElt Ω z w hy = locElt Ω z w' hy' := hinv.symm.trans (hψ.trans hinv')
  have hww : w = w' := congrArg Subtype.val
    (eq_of_involutions_of_mk (Y := ↥(locLayer Ω z)) hP1 (a := ⟨w, hy⟩) (b := ⟨w', hy'⟩)
      (Subtype.ext (mul_self_of_isClassicalMember3 hw))
      (Subtype.ext (mul_self_of_isClassicalMember3 hw')) hwe)
  obtain ⟨g, hg⟩ := hsingle L hL.1
  have hwg : w = g * z * g⁻¹ := involution_unique3 hw (hg ▸ hz.conj g)
  have hNΩ : conjSub g⁻¹ L' ∈ Ω := hΩ.conjInvariant g⁻¹ L' hL'.1
  have hNcl : IsClassicalMember3 (conjSub g⁻¹ L') z := by
    have e : g⁻¹ * w' * g⁻¹⁻¹ = z := by rw [inv_inv, ← hww, hwg]; group
    exact e ▸ hw'.conj g⁻¹
  have hNz : conjSub g⁻¹ L' ∈ centralizingMembers Ω {z} :=
    ⟨hNΩ, isSubnormal_le hNcl.subnormal⟩
  have hNK : conjSub g⁻¹ L' = K :=
    eq_of_locImg_le_Q₀3 (by omega) hΩ hex hK hz hP1 hO3 d hNz
      (locImg_self_le_Q₀3 (by omega) hNΩ hNcl d)
  have hL'L : L' = L := by
    rw [hg, ← hNK, conjSub_conjSub_inv]
  have hc : Commutes L L' := by
    refine commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hL hL' ?_
    rw [hLR, hLR']
    exact commutes_map_of_commutes d.ψ
      (commutes_Lc_of_disjoint h2 (nodePair_disjoint (by omega) (by omega) (by omega)))
  rw [hL'L] at hc
  exact not_commutes_self3 hw hc

end Ker

section Partner

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx3.exists_partner_three (c : ACtx3 3 Ω K z) (nd : Nodes3 c)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) :
    ∃ β : Subgroup G, β ∈ Ω ∧ (∃ wβ : G, IsClassicalMember3 β wβ) ∧ ¬ Commutes K β ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β) ∧
      ¬ Commutes β (nd.j 0) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (nd.j 0)) ∧
      Commutes β (nd.j 2) := by
  have h2 := two_ne_zero_gf3
  have hMΩ : nd.j 2 ∈ Ω := (nd.mem 2 (by omega)).1
  obtain ⟨g, hg⟩ := hsingle _ hMΩ
  obtain ⟨hK'm, hK'ne, R₀, i₀, hR₀, hKR₀, hy₀, hi₀⟩ := c.exists_rootData_conj hg c.hK
    (nd.commK 2 (by omega)) (nd.ne_K 2 (by omega)).symm c.hz
  obtain ⟨hN0m, hN0ne, R₁, i₁, hR₁, hN0R, hy₁, hi₁⟩ := c.exists_rootData_conj hg
    (nd.mem 0 (by omega)).1 (nd.far 0 (by omega) 2 (by omega) (by omega))
    (nd.inj 0 (by omega) 2 (by omega) (by omega)) (nd.isCl 0 (by omega))
  have hKne : conjSub g⁻¹ K ≠ conjSub g⁻¹ (nd.j 0) := fun h =>
    nd.ne_K 0 (by omega) ((conjSub_injective g⁻¹ h).symm)
  have hne : i₀ ≠ i₁ := c.ne_of_rootInv hK'm hN0m hKne hR₀ hR₁ hKR₀ hN0R
  have hR01 : Commutes R₀ R₁ :=
    (c.commutes_iff_root hK'm hN0m hR₀ hKR₀ hN0R).mp
      ((commutes_conjSub_iff g⁻¹).mpr (nd.commK 0 (by omega)))
  obtain ⟨B, iB, hB, hc0, hne0, hnc0, hc1, hne1, hnc1⟩ := exists_partner_one h2 hR₀ hR₁ hne hR01
  obtain ⟨β', hβ'm, hβ'K, hβ'img⟩ := exists_member_of_root3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3
    c.d (R := B) ⟨iB, hB⟩
  obtain ⟨wb, hwb⟩ := c.hΩ.classical β' hβ'm.1
  have hnK' : ¬ Commutes (conjSub g⁻¹ K) β' := fun h =>
    hnc0 ((c.commutes_iff_root hK'm hβ'm hR₀ hKR₀ hβ'img).mp h).symm
  have hn0' : ¬ Commutes β' (conjSub g⁻¹ (nd.j 0)) := fun h =>
    hnc1 ((c.commutes_iff_root hβ'm hN0m hB hβ'img hN0R).mp h)
  obtain ⟨W1, hW1⟩ := c.stdpair_of_root hK'm hβ'm hR₀ hB hKR₀ hβ'img hc0.symm hne0.symm
    (fun h => hnc0 h.symm)
  obtain ⟨W2, hW2⟩ := c.stdpair_of_root hβ'm hN0m hB hR₁ hβ'img hN0R hc1 hne1 hnc1
  have hKβ'M : Commutes K β' :=
    commutes_K_of_ne3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hβ'm hβ'K
  refine ⟨conjSub g β', c.hΩ.conjInvariant g β' hβ'm.1, ⟨_, IsClassicalMember3.conj hwb g⟩, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro h
    rw [← conjSub_conjSub_inv g K] at h
    exact hnK' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W1, ?_⟩
    have := linearBlockStandardPair_conjSub hW1 g
    rwa [conjSub_conjSub_inv] at this
  · intro h
    rw [← conjSub_conjSub_inv g (nd.j 0)] at h
    exact hn0' ((commutes_conjSub_iff g).mp h)
  · refine ⟨conjSub g W2, ?_⟩
    have := linearBlockStandardPair_conjSub hW2 g
    rwa [conjSub_conjSub_inv] at this
  · rw [hg]
    exact (commutes_conjSub_iff g).mpr hKβ'M.symm

end Partner

section Middle

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem ACtx3.exists_middle_three {ι : Type} (c : ACtx3 3 Ω K z) (nd : Nodes3 c)
    (hMFZ : RouteD.Gaps.FundNoncentral 3)
    (hcl : LinearAutClassification (GaloisField 3 1) (3 + 1))
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z))
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} (hβ : β ∈ Ω) {t : G} (hwβ : IsClassicalMember3 β t)
    (hnK : ¬ Commutes K β)
    (hpair : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfirst : ¬ Commutes β (nd.j 0)) (hlast : Commutes β (nd.j 2)) :
    ∃ N : Subgroup G, N ∈ centralizingMembers Ω {z} ∧ N ≠ K ∧ Commutes β N ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W (nd.j 0) N) ∧
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N (nd.j 2)) := by
  classical
  have h2 := two_ne_zero_gf3
  have hΩ := c.hΩ
  have hex := c.hex
  have hconj := hΩ.conjInvariant
  have htz : t * z * t⁻¹ = z := fix_of_stdpair3 c.hz hwβ hpair
  have htt : t * t = 1 := mul_self_of_isClassicalMember3 hwβ
  have attach := fun (N : Subgroup G) (hN : N ∈ Ω) (hNK : Commutes N K) =>
    c.commutes_partner_iff hMFZ D hsingle hβ hwβ hnK hN hNK
  have hmemΩz : ∀ L ∈ centralizingMembers Ω {z}, conjSub t L ∈ centralizingMembers Ω {z} :=
    fun L hL => conjSub_mem_centralizingMembers3 hconj htz hL
  set σ := locAut hconj htz with hσdef
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hconj htz htt
  set ψ := c.d.ψ with hψ
  have hcK : IsClassicalMember3 (conjSub t K) z := by
    have := c.hz.conj t
    rwa [htz] at this
  have hmem : conjSub t K ∈ centralizingMembers Ω {z} :=
    ⟨hconj t K c.hK, isSubnormal_le hcK.subnormal⟩
  have hKt : conjSub t K = K :=
    eq_of_locImg_le_Q₀3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hmem
      (locImg_self_le_Q₀3 c.hm (hconj t K c.hK) hcK c.d)
  have hKt' : conjSub t⁻¹ K = K := by
    have := congrArg (conjSub t⁻¹) hKt
    rw [conjSub_inv_conjSub] at this
    exact this.symm
  have hconjne : ∀ L, conjSub t L ≠ K ↔ L ≠ K := by
    intro L
    constructor
    · intro hne heq
      apply hne
      rw [heq, hKt]
    · intro hne heq
      apply hne
      have := congrArg (conjSub t⁻¹) heq
      rwa [conjSub_inv_conjSub, hKt'] at this
  have hstab : ∀ x, σ (ψ x) ∈ ψ.range := by
    have hS : (⨆ R ∈ longRootSet (K := GaloisField 3 1) c.hn, R) ≤
        (ψ.range).comap (σ.toMonoidHom.comp ψ) := by
      refine iSup₂_le fun R hR y hy => ?_
      obtain ⟨L, hL, hLK, hLR⟩ := exists_member_of_root3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hR
      have hyL : ψ y ∈ locImg Ω z L := by rw [hLR]; exact ⟨y, hy, rfl⟩
      have h1 : σ (ψ y) ∈ locImg Ω z (conjSub t L) := by
        rw [← locAut_locImg hconj htz L]; exact ⟨_, hyL, rfl⟩
      obtain ⟨R', -, hR'⟩ := exists_root_of_ne3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d
        (hmemΩz L hL) ((hconjne L).mpr hLK)
      rw [hR'] at h1
      obtain ⟨y', -, hy'⟩ := h1
      exact ⟨y', hy'⟩
    intro x
    have hx : x ∈ ⨆ R ∈ longRootSet (K := GaloisField 3 1) c.hn, R := by
      rw [iSup_longRootSet_eq_top h2 c.hn]; exact Subgroup.mem_top x
    exact hS hx
  have hfix : ∀ A : SL(2, GaloisField 3 1),
      σ (ψ (blockSL2 (GaloisField 3 1) 3 ⟨2, by omega⟩ A)) =
        ψ (blockSL2 (GaloisField 3 1) 3 ⟨2, by omega⟩ A) := by
    intro A
    have hle : nd.j 2 ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hlast t hwβ.mem n hn).symm
    exact (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem 2 (by omega))).mp hle _
      (by rw [nd.locImg_eq (by omega)]; exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hmove : ∃ A : SL(2, GaloisField 3 1),
      σ (ψ (blockSL2 (GaloisField 3 1) 3 ⟨0, by omega⟩ A)) ≠
        ψ (blockSL2 (GaloisField 3 1) 3 ⟨0, by omega⟩ A) := by
    by_contra hcon
    push Not at hcon
    have hfx : ∀ a ∈ locImg Ω z (nd.j 0), σ a = a := by
      intro a ha
      rw [nd.locImg_eq (by omega)] at ha
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
      exact hcon A
    have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz (nd.mem 0 (by omega))).mpr hfx
    exact hfirst (Gaps.commutes_symm
      ((attach (nd.j 0) (nd.mem 0 (by omega)).1
        (Gaps.commutes_symm (nd.commK 0 (by omega)))).mpr hle))
  obtain ⟨g, hg0, hg2, hgσ⟩ := partner_chart_three_amb3 card_gf3 hcl ψ c.d.ker_le σ hσ2 hstab hfix
    hmove
  set α : SL(3 + 1, GaloisField 3 1) ≃* SL(3 + 1, GaloisField 3 1) :=
    slConjugation (3 + 1) (GaloisField 3 1) g with hα
  have hroot : ∀ T : Pair (3 + 1), IsLongRootSL2 c.hn
      ((Lc (GaloisField 3 1) T).map α.toMonoidHom) (α (zElt (GaloisField 3 1) T)) := fun T =>
    isLongRootSL2_map_aut3 c.hn α (isLongRootSL2_Lc h2 c.hn T)
  have hα0 : (Lc (GaloisField 3 1) (nodePair 3 0 (by omega))).map α.toMonoidHom =
      Lc (GaloisField 3 1) (nodePair 3 0 (by omega)) := by
    have := hg0
    rwa [blockSL2_range_eq_Lc h2 (by omega : 0 < 3)] at this
  have hα2 : (Lc (GaloisField 3 1) (nodePair 3 2 (by omega))).map α.toMonoidHom =
      Lc (GaloisField 3 1) (nodePair 3 2 (by omega)) := by
    rw [← blockSL2_range_eq_Lc h2 (by omega : 2 < 3), ← MonoidHom.range_comp]
    congr 1
    exact MonoidHom.ext fun A => hg2 A
  have hR1 : (Lc (GaloisField 3 1) (nodePair 3 1 (by omega))).map α.toMonoidHom ∈
      longRootSet (K := GaloisField 3 1) c.hn := ⟨_, hroot _⟩
  obtain ⟨N, hN, hNK, hNR⟩ := exists_member_of_root3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hR1
  have hfixN : ∀ a ∈ locImg Ω z N, σ a = a := by
    intro a ha
    rw [hNR] at ha
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := ha
    have hx' : x ∈ (blockSL2 (GaloisField 3 1) 3 ⟨1, by omega⟩).range := by
      rw [blockSL2_range_eq_Lc h2 (by omega : 1 < 3)]; exact hx
    obtain ⟨A, rfl⟩ := hx'
    have hd : partnerEnt 3 (1 : (GaloisField 3 1)ˣ) (⟨1, by omega⟩ : Fin 3).castSucc =
        partnerEnt 3 (1 : (GaloisField 3 1)ˣ) (⟨1, by omega⟩ : Fin 3).succ := by
      simp [partnerEnt]
    have hfixed1 := slConjugation_diagGL_blockSL2 (partnerEnt 3 (1 : (GaloisField 3 1)ˣ))
      ⟨1, by omega⟩ hd A
    have := hgσ (blockSL2 (GaloisField 3 1) 3 ⟨1, by omega⟩ A)
    unfold partnerDiag at this
    rw [hfixed1] at this
    exact this
  have hNK' : Commutes N K :=
    (commutes_K_of_ne3 c.hm hΩ hex c.hK c.hz c.hP1 c.hO3 c.d hN hNK).symm
  have hle := (locAut_fixed_iff3 hΩ hex c.hP1 c.hO3 htz hN).mpr hfixN
  have hcβ : Commutes β N := Gaps.commutes_symm ((attach N hN.1 hNK').mpr hle)
  have hcomm : ∀ T T' : Pair (3 + 1), Commute (α (zElt (GaloisField 3 1) T))
      (α (zElt (GaloisField 3 1) T')) := fun T T' => by
    show α _ * α _ = α _ * α _
    rw [← map_mul, ← map_mul, signGroup_comm (zElt_mem_signGroup T) (zElt_mem_signGroup T')]
  have hne : ∀ a b : ℕ, (ha : a < 3) → (hb : b < 3) → a ≠ b →
      α (zElt (GaloisField 3 1) (nodePair 3 a ha)) ≠
        α (zElt (GaloisField 3 1) (nodePair 3 b hb)) := by
    intro a b ha hb hab h
    have := (nodePair_eq_iff ha hb).mp (zElt_injective h2 (α.injective h))
    exact hab this
  have hnc : ∀ a : ℕ, (ha : a + 2 < 3 + 1) →
      ¬ Commutes ((Lc (GaloisField 3 1) (nodePair 3 a (by omega))).map α.toMonoidHom)
        ((Lc (GaloisField 3 1) (nodePair 3 (a + 1) (by omega))).map α.toMonoidHom) := by
    intro a ha hc'
    exact not_commutes_Lc_overlap h2 c.hn3 (i := ⟨a, by omega⟩) (j := ⟨a + 1, by omega⟩)
      (k := ⟨a + 2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]) ((commutes_map_iff α.toMonoidHom α.injective).mp hc')
  obtain ⟨W₁, hW₁⟩ := c.stdpair_of_root (nd.mem 0 (by omega)) hN (hroot (nodePair 3 0 (by omega)))
    (hroot (nodePair 3 1 (by omega))) (by rw [hα0, nd.img 0 (by omega)]) hNR (hcomm _ _)
    (hne 0 1 (by omega) (by omega) (by omega)) (hnc 0 (by omega))
  obtain ⟨W₂, hW₂⟩ := c.stdpair_of_root hN (nd.mem 2 (by omega)) (hroot (nodePair 3 1 (by omega)))
    (hroot (nodePair 3 2 (by omega))) hNR (by rw [hα2, nd.img 2 (by omega)]) (hcomm _ _)
    (hne 1 2 (by omega) (by omega) (by omega)) (hnc 1 (by omega))
  exact ⟨N, hN, hNK, hcβ, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩⟩

end Middle

section Row

theorem chainRow3_three (h3 : OddThreeFreeInput) : ChainRow3 3 := by
  intro G _ _ _ hnab K z hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hshape' := hshape
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dict (m := 3) (by norm_num) hR.inClass hK hR.cls hshape
  let c : ACtx3 3 (conjClass3 K) K z :=
    { hm := by norm_num, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d,
      hlift := Or.inr (ShapeADict.kerInvolutionFree_three3 hR.inClass hex hK hsingle hR.cls hP1
        (h3 G K z hR) d) }
  obtain ⟨nd⟩ := c.nonempty_nodes
  obtain ⟨ι, -, D, -⟩ := hshape'
  obtain ⟨β, hβΩ, ⟨t, hβcl⟩, hnK, hW1, hnβ0, ⟨W2, hW2⟩, hlast⟩ :=
    c.exists_partner_three nd hsingle
  obtain ⟨N, hN, hNK, hβN, ⟨W3, hW3⟩, ⟨W4, hW4⟩⟩ :=
    c.exists_middle_three nd (RouteD.Gaps.fundNoncentral 3)
      (linearAutClassification3 (by norm_num)) D hsingle hβΩ hβcl hnK hW1 hnβ0 hlast
  obtain ⟨W1, hW1⟩ := hW1
  refine ⟨![K, β, nd.j 0, N, nd.j 2], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hK
    · exact hβΩ
    · exact (nd.mem 0 (by norm_num)).1
    · exact hN.1
    · exact (nd.mem 2 (by norm_num)).1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact nd.commK 0 (by norm_num)
    · exact commutes_K_of_ne3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hN hNK
    · exact nd.commK 2 (by norm_num)
    · exact hβN
    · exact hlast
    · exact nd.far 0 (by norm_num) 2 (by norm_num) (by norm_num)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact ⟨W1, hW1⟩
    · exact ⟨W2, hW2⟩
    · exact ⟨W3, hW3⟩
    · exact ⟨W4, hW4⟩

end Row

end CFSG.ClassicalInvolution.Q3.Q3W
