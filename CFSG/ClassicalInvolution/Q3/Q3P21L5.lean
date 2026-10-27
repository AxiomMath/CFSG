module

public import CFSG.ClassicalInvolution.Q3.Q3P21L2
public import CFSG.ClassicalInvolution.Q3.Q3P21L3
public import CFSG.ClassicalInvolution.Q3.Q3P21L4
public import CFSG.ClassicalInvolution.Q3.Q3TCBridge
public import CFSG.ClassicalInvolution.Q3.Q3TCD4Clique
public import CFSG.ClassicalInvolution.Q3.Q3TSRowSL4
public import CFSG.ClassicalInvolution.Q3.Q3EXModel
public import CFSG.ClassicalInvolution.RouteD.TwinTenChain
public import CFSG.ClassicalInvolution.Q3.Q3TIVFinal
public import CFSG.ClassicalInvolution.Q3.Q3EXD4FLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.Timmesfeld
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinRow)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD.NonClassical (le_centralizer_of_commutes)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)

section Twin

theorem exists_node_twin3 (h3 : OddThreeFreeInput) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z)
    (cK : TCtx3 .PSL 4 (conjClass3 K) K z)
    (hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K) {β : Subgroup G}
    (hβ : β ∈ conjClass3 K) (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {M : Subgroup G} (hMΩ : M ∈ conjClass3 K) (hKM : Commutes K M) (hβM : Commutes β M)
    (hMnc : ¬ ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ M → Commutes M N)
    {x₀ : G} (hx₀ : IsClassicalMember3 M x₀) :
    ∃ T₀ : Subgroup G, T₀ ∈ conjClass3 K ∧ T₀ ≠ M ∧ Commutes M T₀ ∧ Commutes K T₀ ∧
      Commutes β T₀ ∧ IsClassicalMember3 T₀ x₀ := by
  classical
  have hΩ := cK.hΩ
  have hKΩ : K ∈ conjClass3 K := cK.hK
  have hβK : β ≠ K := fun e => by
    obtain ⟨W, hW⟩ := hKβ
    exact ne_of_linearBlockStandardPair hW e.symm
  have hncKβ : ¬ Commutes K β := by
    obtain ⟨W, hW⟩ := hKβ
    exact not_commutes_of_linearBlockStandardPair hW
  have hMK : M ≠ K := fun e => by
    subst e
    exact not_commutes_self3 cK.hz hKM
  obtain ⟨N', hN'z, hN'M, hnc⟩ :
      ∃ N' ∈ centralizingMembers (conjClass3 K) {z}, N' ≠ M ∧ ¬ Commutes M N' := by
    by_contra hcon
    push Not at hcon
    exact hMnc fun N hN hNM => hcon N hN hNM
  obtain ⟨g, hg⟩ := hsingle M hMΩ
  have hx₀g : x₀ = g * z * g⁻¹ := involution_unique3 hx₀ (hg ▸ cK.hz.conj g)
  have hcM : conjClass3 M = conjClass3 K := conjClass3_eq_of_mem hMΩ
  obtain ⟨cx⟩ := cK.exists_ctx_member hsingle hMΩ hx₀
  have hKx : K ∈ centralizingMembers (conjClass3 K) {x₀} :=
    mem_centralizingMembers_of_commutes hKΩ hx₀.mem hKM
  have hβx : β ∈ centralizingMembers (conjClass3 K) {x₀} :=
    mem_centralizingMembers_of_commutes hβ hx₀.mem hβM
  have hMx : M ∈ centralizingMembers (conjClass3 K) {x₀} :=
    ⟨hMΩ, isSubnormal_le hx₀.subnormal⟩
  have hKQ : ¬ locImg (conjClass3 K) x₀ K ≤ cx.d.Q₁ := by
    intro hKQ
    have hcomm : ∀ N ∈ centralizingMembers (conjClass3 K) {x₀}, N ≠ K → Commutes K N :=
      fun N hN hNK => cx.commutes_T_of_ne hKx hKQ hN hNK
    have hconj : ∃ g' : G, K = conjSub g' M :=
      ⟨g⁻¹, by rw [hg, ← conjSub_mul, inv_mul_cancel, conjSub_one]⟩
    have heq := centralizingMembers_eq_of_twin3 hΩ hx₀ cK.hz hconj hKx hcomm
    have hN'x : N' ∈ centralizingMembers (conjClass3 K) {x₀} := heq ▸ hN'z
    exact hnc (cx.commutes_K_of_ne hN'x hN'M)
  obtain ⟨T₀, hT₀x, hT₀Q⟩ := cx.exists_twin
  have hKT₀ : K ≠ T₀ := fun e => hKQ (e ▸ hT₀Q.le)
  have hT₀K : Commutes T₀ K := cx.commutes_T_of_ne hT₀x hT₀Q.le hKx hKT₀
  have hβT₀ : β ≠ T₀ := fun e => hncKβ (e ▸ hT₀K.symm)
  have hT₀β : Commutes T₀ β := cx.commutes_T_of_ne hT₀x hT₀Q.le hβx hβT₀
  have hMT₀ : M ≠ T₀ := (cx.twin_ne hT₀x hT₀Q.le).symm
  have hT₀M : Commutes T₀ M := cx.commutes_T_of_ne hT₀x hT₀Q.le hMx hMT₀
  have hrow : TwinRow .PSL 4 := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  have hRM : RouteD3Setup M x₀ := RouteD3Setup.of_mem_conjClass3 hR hMΩ hx₀
  have hshapeM : LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 M) x₀ := by
    rw [hcM, hx₀g]
    exact localShapeC3_conj hΩ.conjInvariant hshape g
  have hTwin : IsTwinAt (conjClass3 M) M T₀ x₀ := by
    rw [hcM]
    exact ⟨hT₀x, cx.twin_ne hT₀x hT₀Q.le, fun _ hN hNT => cx.commutes_T_of_ne hT₀x hT₀Q.le hN hNT,
      fun _ hN hNK => cx.commutes_K_of_ne hN hNK⟩
  have hT₀cls : IsClassicalMember3 T₀ x₀ :=
    Q3TIV.twinInvolution3_of_odd3 h3 G hnab M x₀ hRM .PSL 4 hrow hshapeM T₀ hTwin
  exact ⟨T₀, hT₀x.1, hMT₀.symm, hT₀M.symm, hT₀K.symm, hT₀β.symm, hT₀cls⟩

end Twin

section Main

theorem chainPiece3TwinSL4_of_linking (h3 : OddThreeFreeInput) (hP : CommutingProductP1Input3)
    (hY2 : TwinYType3On (fun t n => t = .PSL ∧ n = 4)) : Q3TS.ChainPiece3TwinSL4 := by
  intro G _ _ _ hnab K z hR hshape
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hΩ := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := fun L hL => by
    obtain ⟨g, hg⟩ := hL
    exact ⟨g, hg.symm⟩
  obtain ⟨cK⟩ := nonempty_tctx3 (yData3_sl4 statedLieAdmissible_sl4_three) h3 hR hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := cK.exists_partner hsingle
    ⟨_, rankOne_mem_fund_sl4_three statedLieAdmissible_sl4_three 0⟩
  obtain ⟨M, hMΩ, hKM, hβM, hMnc⟩ := id hfix
  obtain ⟨W₀, hW₀⟩ := hKβ
  have hRβ : RouteD3Setup β t := RouteD3Setup.of_mem_conjClass3 hR hβ ht
  have hcl : conjClass3 β = conjClass3 K := conjClass3_eq_of_mem hβ
  have hexβ : ExactMembers3 (conjClass3 β) := hRβ.setup.1
  have hΩβ : InClass3 (conjClass3 β) := hRβ.inClass
  obtain ⟨x₀, hx₀⟩ := hΩ.classical M hMΩ
  have hKx₀ : K ≤ Subgroup.centralizer ({x₀} : Set G) :=
    le_centralizer_of_commutes hKM hx₀.mem
  have hnotK : ¬ K ≤ Subgroup.centralizer ({t} : Set G) := by
    intro hle
    rcases cp_at_member3 h3 hnab hR hβ ht (L := K) ⟨hKΩ, hle⟩ with hc | he
    · exact not_commutes_of_linearBlockStandardPair hW₀ hc.symm
    · exact ne_of_linearBlockStandardPair hW₀ he
  have htx : t ≠ x₀ := fun h => hnotK (h ▸ hKx₀)
  have hMt : M ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hMΩ, le_centralizer_of_commutes (Commutes.symm hβM) ht.mem⟩
  have hMne : M ≠ β := fun h => not_commutes_of_linearBlockStandardPair hW₀ (h ▸ hKM)
  obtain ⟨cβ⟩ := cK.exists_ctx_member hsingle hβ ht
  obtain ⟨T, hT, hTQ⟩ := cβ.exists_twin
  have hTβ : T ≠ β := cβ.twin_ne hT hTQ.le
  have hTcomm : ∀ N ∈ centralizingMembers (conjClass3 K) {t}, N ≠ T → Commutes T N :=
    fun N hN hNT => cβ.commutes_T_of_ne hT hTQ.le hN hNT
  have hsingleβ : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g β := fun L hL => by
    rw [← hcl] at hL
    obtain ⟨g, hg⟩ := hL
    exact ⟨g, hg.symm⟩
  have hMnT : ∀ T' : Subgroup G, T' ∈ centralizingMembers (conjClass3 K) {t} →
      (∀ N ∈ centralizingMembers (conjClass3 K) {t}, N ≠ T' → Commutes T' N) → M ≠ T' := by
    intro T' hT' hT'comm hMT'
    have hTx : IsClassicalMember3 T' x₀ := hMT' ▸ hx₀
    have heq := centralizingMembers_eq_of_twin3 hΩ ht hTx (hsingleβ T' hT'.1) hT' hT'comm
    have hKmem : K ∈ centralizingMembers (conjClass3 K) {x₀} := ⟨hKΩ, hKx₀⟩
    rw [heq] at hKmem
    exact hnotK hKmem.2
  have hMT : M ≠ T := hMnT T hT hTcomm
  have hPP : Q3TC.ProductP1Input3 := productP1Input3_of_commuting hP
  obtain ⟨hP1x, hO3x⟩ := hPP G β t hRβ M (hcl ▸ hMΩ) x₀ hx₀ hβM htx
  obtain ⟨g₀, hg₀⟩ := hsingle β hβ
  have htg : t = g₀ * z * g₀⁻¹ := involution_unique3 ht (hg₀ ▸ hR.cls.conj g₀)
  have hshapeβ : LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 β) t := by
    rw [hcl, htg]
    exact localShapeC3_conj hΩ.conjInvariant hshape g₀
  have hlink : LinkedAtProduct (conjClass3 β) β t x₀ := by
    refine twinLinked3_sl4 h3 hP hY2 G hnab β t hRβ hshapeβ M (hcl ▸ hMt) hMne ?_ x₀ hx₀
    intro T' hT'
    exact hMnT T' (hcl ▸ hT'.mem) (hcl ▸ hT'.comm_T)
  obtain ⟨ι, hι, D, c, hk, -, hβc, hMc, hTc, hallc⟩ :=
    exists_d4_component_of_twin_product3 Q3W.EX.mfTwin3 h3 hnab hRβ (T₁ := T) (hcl ▸ hT) hTβ
      (fun N hN hNT => hTcomm N (hcl ▸ hN) hNT) (K₂ := M) (hcl ▸ hMt) hMne hMT hx₀ htx
      hP1x hO3x hlink
  obtain ⟨T₀, hT₀Ω, hT₀M, hMT₀, hKT₀, hβT₀, hT₀cls⟩ :=
    exists_node_twin3 h3 hnab hR hshape cK hsingle hβ ⟨W₀, hW₀⟩ hMΩ hKM hβM hMnc hx₀
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_commutes (Commutes.symm hβT₀) ht.mem
  have hT₀x₀ : T₀ ≤ Subgroup.centralizer ({x₀} : Set G) :=
    le_centralizer_of_commutes (Commutes.symm hMT₀) hx₀.mem
  have hT₀x : T₀ ∈ centralizingMembers (conjClass3 β) {t * x₀} :=
    ⟨hcl ▸ hT₀Ω, fun n hn => mem_centralizer_mul (hT₀t hn) (hT₀x₀ hn)⟩
  obtain ⟨N₀, hN₀x, hN₀β, hN₀nc⟩ := id hlink
  have hN₀c : N₀ ∈ compMembers3 (conjClass3 β) (t * x₀) D c := hallc N₀ hN₀x hN₀β hN₀nc
  obtain ⟨i₂, hi₂⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨T₀, hT₀x, rfl⟩)
  have hi₂c : i₂ = c := by
    by_contra hne
    have hcm := commutes_of_ne_comp3 hΩβ hexβ hP1x hO3x D (Ne.symm hne) hN₀c ⟨hT₀x, hi₂⟩
    have hN₀x₀ : N₀ ≤ Subgroup.centralizer ({x₀} : Set G) :=
      le_centralizer_of_commutes hcm hT₀cls.mem
    have hN₀t : N₀ ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
      mem_centralizer_left_of_mul (hN₀x.2 hn) (hN₀x₀ hn)
    rcases cp_at_member3 h3 hnab hR hβ ht (L := N₀) ⟨hcl ▸ hN₀x.1, hN₀t⟩ with hc | he
    · exact hN₀nc hc
    · exact hN₀β he
  have hT₀c : T₀ ∈ compMembers3 (conjClass3 β) (t * x₀) D c := ⟨hT₀x, hi₂c ▸ hi₂⟩
  have hz2 : z * z = 1 := Q3TLK.mul_self_eq_one_of_orderOf_eq_two3 hR.cls.orderOf_eq_two
  have hzt : z * t = t * z := standardPair_involutions_commute h2 hW₀ hR.cls.mem ht.mem
    hR.cls.orderOf_eq_two ht.orderOf_eq_two
  have hzx₀ : z * x₀ = x₀ * z := hKM z hR.cls.mem x₀ hx₀.mem
  have hzu : z * (t * x₀) * z⁻¹ = t * x₀ := by
    calc z * (t * x₀) * z⁻¹ = (z * t) * x₀ * z⁻¹ := by group
      _ = (t * z) * x₀ * z⁻¹ := by rw [hzt]
      _ = t * (z * x₀) * z⁻¹ := by group
      _ = t * (x₀ * z) * z⁻¹ := by rw [hzx₀]
      _ = t * x₀ := by group
  set τ := Gaps.locAut hΩβ.conjInvariant hzu with hτdef
  have hτ2 : ∀ y, τ (τ y) = y := Gaps.locAut_locAut hΩβ.conjInvariant hzu hz2
  obtain ⟨hsc', hpc, -, hcentral⟩ := component_facts (D.kind c) hk
  obtain ⟨A, hA⟩ := exists_corr_left3 hΩβ hexβ hP1x hO3x D hMc
  obtain ⟨B, hB⟩ := exists_corr_left3 hΩβ hexβ hP1x hO3x D hT₀c
  obtain ⟨C, hC⟩ := exists_corr_left3 hΩβ hexβ hP1x hO3x D hβc
  have hMz : M ≤ Subgroup.centralizer ({z} : Set G) :=
    le_centralizer_of_commutes (Commutes.symm hKM) hR.cls.mem
  have hT₀z : T₀ ≤ Subgroup.centralizer ({z} : Set G) :=
    le_centralizer_of_commutes (Commutes.symm hKT₀) hR.cls.mem
  have hfixN : ∀ {N : Subgroup G} {R : Subgroup (D.kind c).G},
      Corr3 (conjClass3 β) (t * x₀) D c N R → N ≤ Subgroup.centralizer ({z} : Set G) →
        ∀ r ∈ R, τ (D.hom c r) = D.hom c r := fun hNR hNz r hr =>
    (locAut_fixed_iff3 hΩβ hexβ hP1x hO3x hzu hNR.1).mp hNz (D.hom c r)
      (hNR.2.2 ▸ Subgroup.mem_map_of_mem _ hr)
  have hτr : ∀ k, τ (D.hom c k) ∈ (D.hom c).range :=
    aut_preserves_range_of_fixed D c hk hA.2.1 τ (hfixN hA hMz)
  have hAB : A ≠ B := fun h =>
    hT₀M (corr_unique_right3 hΩβ hexβ hP1x hO3x (h ▸ hB) hA)
  have hcAB : Commutes A B := (corr_commutes3 hΩβ hexβ hP1x hO3x hpc hA hB).mp hMT₀
  have hcAC : Commutes A C :=
    (corr_commutes3 hΩβ hexβ hP1x hO3x hpc hA hC).mp (Commutes.symm hβM)
  have hcBC : Commutes B C :=
    (corr_commutes3 hΩβ hexβ hP1x hO3x hpc hB hC).mp (Commutes.symm hβT₀)
  obtain ⟨xβ, hxβ, hxβ1, hxβ3, hxβinv⟩ := RouteD.TWS7.exists_inverted_unipotent (p := 3) h2
    (linearBlockStandardPair_symm hW₀) hR.cls.mem hR.cls.orderOf_eq_two
  have hxL : xβ ∈ locLayer (conjClass3 β) (t * x₀) := le_centralizingLayer hβc.1 hxβ
  obtain ⟨r₀, hr₀, hr₀x⟩ : locMk (conjClass3 β) (t * x₀) ⟨xβ, hxL⟩ ∈ C.map (D.hom c) := by
    rw [← hC.2.2]
    exact ⟨⟨xβ, hxL⟩, Subgroup.mem_subgroupOf.mpr hxβ, rfl⟩
  have hr₀1 : D.hom c r₀ ≠ 1 := by
    rw [hr₀x]
    intro h
    have h1 : locMk (conjClass3 β) (t * x₀) ⟨xβ, hxL⟩ = locMk (conjClass3 β) (t * x₀) 1 := by
      rw [h, map_one]
    have := Q3W.EX.locMk_inj_of_member3 hexβ hβc.1 (b := 1) hxβ (one_mem _) h1
    exact hxβ1 (by simpa using congrArg Subtype.val this)
  have hr₀3 : r₀ ^ 3 = 1 := by
    have h1 : D.hom c (r₀ ^ 3) = 1 := by
      rw [map_pow, hr₀x, ← map_pow]
      have : (⟨xβ, hxL⟩ : ↥(locLayer (conjClass3 β) (t * x₀))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hxβ3)
      rw [this, map_one]
    exact hcentral C hC.2.1 (r₀ ^ 3) (pow_mem hr₀ 3) (D.ker_le_center c (MonoidHom.mem_ker.mpr h1))
  have hτr₀ : τ (D.hom c r₀) = (D.hom c r₀)⁻¹ := by
    rw [hr₀x, ← map_inv]
    show locMk (conjClass3 β) (t * x₀) (Gaps.layerAut hΩβ.conjInvariant hzu ⟨xβ, hxL⟩) = _
    congr 1
    apply Subtype.ext
    simpa [Gaps.coe_layerAut] using hxβinv
  obtain ⟨R, hRf, hRc, hRs, hRfix, hRn, hRm⟩ := star_of_component (D.kind c) hk (D.hom c)
    (D.ker_le_center c) τ hτ2 hτr hA.2.1 hB.2.1 hC.2.1 hAB hcAB hcAC hcBC (hfixN hA hMz)
    (hfixN hB hT₀z) hr₀ hr₀1 hr₀3 hτr₀
  choose N hN using fun a => exists_corr_right3 hΩβ D hsc' (hRf a)
  have hNΩ : ∀ a, N a ∈ conjClass3 K := fun a => hcl ▸ (hN a).1.1
  have hKnotu : ¬ K ≤ Subgroup.centralizer ({t * x₀} : Set G) := fun h =>
    hnotK fun n hn => mem_centralizer_left_of_mul (h hn) (hKx₀ hn)
  have hNcomm : ∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (N a) (N b) :=
    fun a b hab h1 h2 => (corr_commutes3 hΩβ hexβ hP1x hO3x hpc (hN a) (hN b)).mpr
      (hRc a b hab h1 h2)
  have hNstd : ∀ a b, edgeD 4 a b →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (N a) (N b) := fun a b hab => by
    obtain ⟨W, hW⟩ := hRs a b hab
    have := Gaps.linearBlockStandardPair_map (D.hom c) (D.ker_le_center c) hW
    rw [← (hN a).2.2, ← (hN b).2.2] at this
    exact linearBlockStandardPair_of_locImg3' hΩβ hexβ hP1x hO3x (hN a).1 (hN b).1 this
  have hNz : ∀ a : Fin 4, 1 ≤ a.val → N a ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    (locAut_fixed_iff3 hΩβ hexβ hP1x hO3x hzu (hN a).1).mpr (fun y hy => by
      rw [(hN a).2.2] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      exact hRfix a ha g hg)
  have hKN : ∀ a : Fin 4, 1 ≤ a.val → Commutes K (N a) := fun a ha => by
    rcases cp_at_member3 h3 hnab hR hKΩ hR.cls (L := N a) ⟨hNΩ a, hNz a ha⟩ with h | h
    · exact h
    · exact absurd (h ▸ (hN a).1.2) hKnotu
  let a0 : Fin 4 := ⟨0, by omega⟩
  let a2 : Fin 4 := ⟨2, by omega⟩
  have hN0mov : ¬ N a0 ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hle
    obtain ⟨g, hg, hne⟩ := hRm
    apply hne
    exact (locAut_fixed_iff3 hΩβ hexβ hP1x hO3x hzu (hN a0).1).mp hle (D.hom c g)
      (by rw [(hN a0).2.2]; exact Subgroup.mem_map_of_mem _ hg)
  have hN0norm : conjSub z (N a0) = N a0 := by
    have hle : (locImg (conjClass3 β) (t * x₀) (N a0)).map τ.toMonoidHom ≤
        locImg (conjClass3 β) (t * x₀) (N a0) := by
      rw [(hN a0).2.2]
      rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact hRn g hg
    have heq : (locImg (conjClass3 β) (t * x₀) (N a0)).map τ.toMonoidHom =
        locImg (conjClass3 β) (t * x₀) (N a0) := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ τ.toMonoidHom τ.injective).toEquiv).le
    rw [hτdef, Gaps.locAut_locImg hΩβ.conjInvariant hzu] at heq
    exact locImg_injOn3 hΩβ hexβ hP1x hO3x
      (conjSub_mem_centralizingMembers3 hΩβ.conjInvariant hzu (hN a0).1) (hN a0).1 heq
  obtain ⟨y₂, hy₂⟩ := hΩ.classical (N a2) (hNΩ a2)
  obtain ⟨cN₂⟩ := cK.exists_ctx_member hsingle (hNΩ a2) hy₂
  obtain ⟨w₀, hw₀⟩ := hΩ.classical (N a0) (hNΩ a0)
  have hKN₂ : Commutes K (N a2) := hKN a2 (by show 1 ≤ 2; omega)
  have hN₀N₂ : Commutes (N a0) (N a2) :=
    hNcomm a0 a2 (by simp [a0, a2, Fin.ext_iff]) (by simp [edgeD, a0, a2])
      (by simp [edgeD, a0, a2])
  have hKy : K ∈ centralizingMembers (conjClass3 K) {y₂} :=
    mem_centralizingMembers_of_commutes hKΩ hy₂.mem hKN₂
  have hN₀y : N a0 ∈ centralizingMembers (conjClass3 K) {y₂} :=
    mem_centralizingMembers_of_commutes (hNΩ a0) hy₂.mem hN₀N₂
  have hKN₂ne : K ≠ N a2 := fun h => not_commutes_self3 hR.cls (h ▸ hKN₂)
  have hN₀N₂ne : N a0 ≠ N a2 := fun h => not_commutes_self3 hw₀ (h ▸ hN₀N₂)
  have hKN₀ : K ≠ N a0 := fun h => hKnotu (h ▸ (hN a0).1.2)
  have hKN₀nc : ¬ Commutes K (N a0) := fun h =>
    hN0mov (le_centralizer_of_commutes (Commutes.symm h) hR.cls.mem)
  obtain ⟨W₁, hW₁⟩ := stdPair_of_normalizing_involution3 cN₂ hR.cls hw₀ hKy hN₀y hKN₂ne hN₀N₂ne
    hKN₀ hN0norm hKN₀nc
  refine ⟨fun k => if h : k.val = 0 then K else N ⟨k.val - 1, by omega⟩, ?_, ?_, ?_⟩
  · intro k
    by_cases h : k.val = 0
    · simp only [h, dite_true]
      exact hKΩ
    · simp only [h, dite_false]
      exact hNΩ _
  · intro i j hij h1 h2
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · exact absurd (Fin.ext (hi.trans hj.symm)) hij
    · simp only [hi, hj, dite_true, dite_false]
      refine hKN _ ?_
      unfold edgeD at h1
      simp only at h1 ⊢
      omega
    · simp only [hi, hj, dite_true, dite_false]
      refine Commutes.symm (hKN _ ?_)
      unfold edgeD at h2
      simp only at h2 ⊢
      omega
    · simp only [hi, hj, dite_false]
      refine hNcomm _ _ ?_ ?_ ?_
      · intro hab
        exact hij (Fin.ext (by have := congrArg Fin.val hab; simp at this; omega))
      · intro h
        apply h1
        unfold edgeD at h ⊢
        simp only at h ⊢
        omega
      · intro h
        apply h2
        unfold edgeD at h ⊢
        simp only at h ⊢
        omega
  · intro i j hij
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · exfalso
      unfold edgeD at hij
      omega
    · simp only [hi, hj, dite_true, dite_false]
      have hj1 : j.val = 1 := by
        unfold edgeD at hij
        omega
      have : (⟨j.val - 1, by omega⟩ : Fin 4) = a0 := Fin.ext (by simp [a0]; omega)
      rw [this]
      exact ⟨W₁, hW₁⟩
    · exfalso
      unfold edgeD at hij
      omega
    · simp only [hi, hj, dite_false]
      exact hNstd _ _ (by
        unfold edgeD at hij ⊢
        simp only at hij ⊢
        omega)

theorem piece3TwinSL4_of_linking (h3 : OddThreeFreeInput) (hP : CommutingProductP1Input3)
    (hY2 : TwinYType3On (fun t n => t = .PSL ∧ n = 4)) : Piece3TwinSL4 :=
  Q3TS.piece3TwinSL4_of_chain h3 (chainPiece3TwinSL4_of_linking h3 hP hY2)

end Main

end CFSG.ClassicalInvolution.Q3.Q3P21
