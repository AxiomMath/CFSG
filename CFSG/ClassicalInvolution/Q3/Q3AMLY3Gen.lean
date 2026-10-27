module

public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Q3.Q3T7
open scoped MatrixGroups commutatorElement

section Gen


variable {G : Type} [Group G] [Finite G]

theorem mem_tqMembers3_of_nbr [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) {N : Subgroup G} (hN : N ∈ omegaNbr Ω M) :
    N ∈ tqMembers3 Ω a := by
  have hstd := h.std
  have hBelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hstd.stand.below
  obtain ⟨b, hb⟩ := (hstd.stand.hyp : HypOmegaGen Ω).exists_uniqueInvolution hN.1
  exact ⟨hN.1, trivialOnQuot_of_edge (h.toEdgeSetup hint hM hN ha hb) h.nonabelian hBelow⟩

theorem hypOmegaModU_nbrPair3 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) :
    HypOmegaModU (.sl2 3 1)
      (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a)) := by
  classical
  have hstd := h.std
  have hs3 : Q3.Disc3.AscStand3 Ω K := hstd.stand.toStand3
  have hΩ := hs3.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    isPGroup_zpowers_of_mul_self_eq_one ha.sq ha.ne_one
  have htq : ∀ N ∈ omegaNbr Ω M, N ∈ tqMembers3 Ω a := fun N hN =>
    mem_tqMembers3_of_nbr h hint hM ha hN
  have hcl := (secData3_nbrCoreFam h hint hM ha).inClass3
  refine ⟨hcl.conjInvariant, fun L hL => ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hcl.classical L hL
    exact ⟨z, IsClassicalMemberU.ofQ3 hz⟩
  · rintro _ ⟨Kc, hKc, hKcY, rfl⟩ _ ⟨Jc, hJc, hJcY, rfl⟩ hne'
    obtain ⟨⟨K₀, hK₀, rfl⟩, -⟩ := hKc
    obtain ⟨⟨J₀, hJ₀, rfl⟩, -⟩ := hJc
    have hKJ : K₀ ≠ J₀ := fun e => hne' (by rw [e])
    obtain ⟨h1, h2⟩ := omega4_exactCore3 hs3 hc2 (htq K₀ hK₀) (htq J₀ hJ₀) hKJ
    have hcard : Nat.card ↥((exactCore3 a K₀).subgroupOf (nbrLayer Ω M a) ⊓
        (exactCore3 a J₀).subgroupOf (nbrLayer Ω M a)) =
        Nat.card ↥(exactCore3 a K₀ ⊓ exactCore3 a J₀) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKcY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h' => ?_⟩
    have hle := h2 h'
    rw [oddCoreOf_subgroupOf hKcY, oddCoreOf_subgroupOf hJcY]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hxy : (⁅(x : G), (y : G)⁆) ∈ ⁅exactCore3 a K₀, exactCore3 a J₀⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
        (Subgroup.mem_subgroupOf.mp hy)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hxy).1, Subgroup.mem_subgroupOf.mpr (hle hxy).2⟩
  · rintro _ ⟨Kc, hKc, hKcY, rfl⟩ _ ⟨Jc, hJc, hJcY, rfl⟩ hne' z hz v hv hnc hv2 hvz
    obtain ⟨⟨K₀, hK₀, rfl⟩, -⟩ := hKc
    obtain ⟨⟨J₀, hJ₀, rfl⟩, -⟩ := hJc
    have hKJ : K₀ ≠ J₀ := fun e => hne' (by rw [e])
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K₀ hK₀.1
    have hz₀3 : IsClassicalMember3 K₀ z₀ := hz₀.toQ3 (by norm_num)
    have hz₀U : IsUniqueInvolution K₀ z₀ := hz₀.isUniqueInvolution (MemberType.cert_sl2 3 1)
    have hz₀A : z₀ ∈ exactCore3 a K₀ := mem_exactCore3 hz₀3 hc2 (htq K₀ hK₀).2
    have hzA : IsUniqueInvolution (exactCore3 a K₀) (z : G) :=
      isUniqueInvolution_of_subgroupOf hz hKcY
    have hzz : z₀ = (z : G) :=
      (hzA.unique z₀ hz₀A hz₀U.sq).resolve_left hz₀U.ne_one
    have hzK : IsUniqueInvolution K₀ (z : G) := hzz ▸ hz₀U
    have hvJ : (v : G) ∈ J₀ := exactCore3_le_left a J₀ (Subgroup.mem_subgroupOf.mp hv)
    have hnc' : ¬ ∀ w ∈ J₀, (v : G) * w = w * (v : G) := fun h' => hnc (by
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h' w (exactCore3_le_left a J₀ (Subgroup.mem_subgroupOf.mp hw'))))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K₀ hK₀.1 J₀ hJ₀.1 hKJ (z : G) hzK (v : G) hvJ hnc' hv2'
      (congrArg Subtype.val hvz)
    have hvc : (v : G) ∈ Subgroup.centralizer ({a} : Set G) :=
      nbrLayer_le_centralizer Ω M a v.2
    exact (mem_normalizer_subgroupOf_iff hKcY).mp
      (mem_normalizer_inf hn (Subgroup.le_normalizer hvc))

theorem mem_USet_of_nbr3 {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (htq : ∀ N ∈ omegaNbr Ω M, N ∈ tqMembers3 Ω a) {U : Subgroup G}
    (hU : U ∈ USet (centralizingMembers (nbrCoreFam Ω M a) {a})) : U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨⟨N, hN, rfl⟩, -⟩ := hL
  have hRK : IsSylow2In R N := ((isSylow2In_exactCore3_iff hc2 (htq N hN).2).mp hRL).1
  exact ⟨R, mem_RSet_of_isSylow2In hN.1 hRK, hUR, hcyc, hidx⟩

theorem cfg64_of_nbr3 {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G} (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (htq : ∀ N ∈ omegaNbr Ω M, N ∈ tqMembers3 Ω a) {K J : Subgroup G}
    (hK : K ∈ omegaNbr Ω M) (hJ : J ∈ omegaNbr Ω M)
    {zK zJ u v : ↥(nbrLayer Ω M a)} {R T : Subgroup ↥(nbrLayer Ω M a)}
    (h : Cfg64
      (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a))
      ((exactCore3 a K).subgroupOf (nbrLayer Ω M a))
      ((exactCore3 a J).subgroupOf (nbrLayer Ω M a)) zK zJ u v R T) :
    Cfg64 Ω K J (zK : G) (zJ : G) (u : G) (v : G)
      (R.map (nbrLayer Ω M a).subtype) (T.map (nbrLayer Ω M a).subtype) := by
  have hKt := htq K hK
  have hJt := htq J hJ
  have hKc : exactCore3 a K ∈ centralizingMembers (nbrCoreFam Ω M a) {a} :=
    ⟨⟨K, hK, rfl⟩, exactCore3_le_centralizer a K⟩
  have hJc : exactCore3 a J ∈ centralizingMembers (nbrCoreFam Ω M a) {a} :=
    ⟨⟨J, hJ, rfl⟩, exactCore3_le_centralizer a J⟩
  have hKY : exactCore3 a K ≤ nbrLayer Ω M a := exactCore3_le_nbrLayer hK
  have hJY : exactCore3 a J ≤ nbrLayer Ω M a := exactCore3_le_nbrLayer hJ
  have hKJ : K ≠ J := fun e => h.hKJ (by rw [e])
  have hzKc : IsUniqueInvolution (exactCore3 a K) (zK : G) :=
    isUniqueInvolution_of_subgroupOf h.hz hKY
  have hzJc : IsUniqueInvolution (exactCore3 a J) (zJ : G) :=
    isUniqueInvolution_of_subgroupOf h.hj hJY
  have hzK : IsUniqueInvolution K (zK : G) :=
    isUniqueInvolution_of_le_member3 hΩ hK.1 (exactCore3_le_left a K) hzKc
  have hzJ : IsUniqueInvolution J (zJ : G) :=
    isUniqueInvolution_of_le_member3 hΩ hJ.1 (exactCore3_le_left a J) hzJc
  have hnbrJ : ¬ ∃ T' : Subgroup G, IsSylow2In T' (exactCore3 a J) ∧
      T' ≤ Subgroup.normalizer ((exactCore3 a K : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notJ ⟨subgroupOf_mem_restrictFamily hJc hJY, h.hKJ.symm,
      T'.subgroupOf (nbrLayer Ω M a), mem_RSet_restrict hJc hJY hT',
      Subgroup.subgroupOf_mono (nbrLayer Ω M a) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hKY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hnbrK : ¬ ∃ T' : Subgroup G, IsSylow2In T' (exactCore3 a K) ∧
      T' ≤ Subgroup.normalizer ((exactCore3 a J : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notK ⟨subgroupOf_mem_restrictFamily hKc hKY, h.hKJ, T'.subgroupOf (nbrLayer Ω M a),
      mem_RSet_restrict hKc hKY hT', Subgroup.subgroupOf_mono (nbrLayer Ω M a) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hJY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hUmap : (Subgroup.zpowers u).map (nbrLayer Ω M a).subtype = Subgroup.zpowers (u : G) :=
    MonoidHom.map_zpowers _ _
  have hVmap : (Subgroup.zpowers v).map (nbrLayer Ω M a).subtype = Subgroup.zpowers (v : G) :=
    MonoidHom.map_zpowers _ _
  have hUG : Subgroup.zpowers (u : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hU
    rw [hUmap] at h1
    exact mem_USet_of_nbr3 hc2 htq h1
  have hVG : Subgroup.zpowers (v : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hV
    rw [hVmap] at h1
    exact mem_USet_of_nbr3 hc2 htq h1
  have hUK : Subgroup.zpowers (u : G) ≤ K := by
    rw [← hUmap]
    refine (Subgroup.map_mono h.hUK).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hKY]
    exact exactCore3_le_left a K
  have hVJ : Subgroup.zpowers (v : G) ≤ J := by
    rw [← hVmap]
    refine (Subgroup.map_mono h.hVJ).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
    exact exactCore3_le_left a J
  have hUV : Commutes (Subgroup.zpowers (u : G)) (Subgroup.zpowers (v : G)) := by
    rw [← hUmap, ← hVmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (h.hUV x hx y hy)
  have hRKc : IsSylow2In (R.map (nbrLayer Ω M a).subtype) (exactCore3 a K) := by
    have := (isSylow2In_map_subtype_iff (Y := nbrLayer Ω M a)).mpr h.hR
    rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
  have hTJc : IsSylow2In (T.map (nbrLayer Ω M a).subtype) (exactCore3 a J) := by
    have := (isSylow2In_map_subtype_iff (Y := nbrLayer Ω M a)).mpr h.hT
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  have hUVmap : (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map (nbrLayer Ω M a).subtype =
      Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers (v : G) := by
    rw [Subgroup.map_sup, hUmap, hVmap]
  exact
    { hΩ := hΩ
      hK := hK.1
      hJ := hJ.1
      hKJ := hKJ
      hz := hzK
      hj := hzJ
      notJ := not_mem_omegaNbr_of_exact3 hΩ hc2 hKt hJt hKJ hzK hzKc.mem hnbrJ
      notK := not_mem_omegaNbr_of_exact3 hΩ hc2 hJt hKt hKJ.symm hzJ hzJc.mem hnbrK
      hU := hUG
      hUK := hUK
      hV := hVG
      hVJ := hVJ
      hUV := hUV
      hR := ((isSylow2In_exactCore3_iff hc2 hKt.2).mp hRKc).1
      hT := ((isSylow2In_exactCore3_iff hc2 hJt.2).mp hTJc).1
      huR := by
        rw [← hUmap]
        exact Subgroup.map_mono h.huR
      hvT := by
        rw [← hVmap]
        exact Subgroup.map_mono h.hvT
      hRN := by
        rw [← hUVmap]
        exact map_le_normalizer_map h.hRN
      hTN := by
        rw [← hUVmap]
        exact map_le_normalizer_map h.hTN }

theorem aEmpty_nbrPair3 {Ω : Set (Subgroup G)} {M : Subgroup G} {a : G} (hΩ : HypOmegaGen Ω)
    (hΛ : HypOmegaGen
      (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a)))
    (hA : ∀ M' ∈ Ω, CFSG.ClassicalInvolution.Asc77.AEmpty Ω M')
    (hc2 : IsPGroup 2 (Subgroup.zpowers a))
    (htq : ∀ N ∈ omegaNbr Ω M, N ∈ tqMembers3 Ω a) :
    ∀ L ∈ restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a),
      CFSG.ClassicalInvolution.Asc77.AEmpty
        (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a)) L := by
  rintro K₁ hK₁ J₁ hJs hJn zK zJ hzK hzJ
  have hK₁' := hK₁
  have hJ₁' := hJs.1
  obtain ⟨Kc, hKc, hKcY, rfl⟩ := hK₁
  obtain ⟨Jc, hJc, hJcY, rfl⟩ := hJs.1
  obtain ⟨⟨K, hK, rfl⟩, -⟩ := hKc
  obtain ⟨⟨J, hJ, rfl⟩, -⟩ := hJc
  obtain ⟨u, v, R, T, hcfg⟩ := exists_cfg64 hΛ hK₁' hJ₁' hzK hzJ hJs hJn
  have hcfgG := cfg64_of_nbr3 hΩ hc2 htq hK hJ hcfg
  have hstar : J ∈ omegaStarNbr Ω K :=
    ⟨hJ.1, hcfgG.hKJ.symm, Subgroup.zpowers (v : G), hcfgG.hV, hcfgG.hVJ,
      hcfgG.symm.U_le_normalizer⟩
  obtain ⟨g, hg, hgK⟩ := hA K hK.1 J hstar hcfgG.notJ (zK : G) (zJ : G) hcfgG.hz hcfgG.hj
  obtain ⟨ρ, hρ, hρK⟩ := exists_mem_sup_conj_of_cfg64 hcfgG hg hgK
  rw [← Subgroup.map_sup] at hρ
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hρ
  refine ⟨ρ₁, sup_le hcfg.R_le_Y hcfg.T_le_Y hρ₁, ?_⟩
  have hρc : (ρ₁ : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    nbrLayer_le_centralizer Ω M a ρ₁.2
  have e : (ρ₁ : G) * a * (ρ₁ : G)⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hρc]
    group
  have h1 := exactCore3_conjSub (ρ₁ : G) a K
  rw [e] at h1
  have hρK' : conjSub (ρ₁ : G) K = J := hρK
  rw [hρK'] at h1
  rw [conjSub_subgroupOf (nbrLayer Ω M a) ρ₁ (exactCore3 a K), ← h1]

theorem genSection_layerFam [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) : Q3T8.Sect.GenSection (layerFam Ω M a) := by
  classical
  have hstd := h.std
  have hΩG : HypOmegaGen Ω := hstd.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    isPGroup_zpowers_of_mul_self_eq_one ha.sq ha.ne_one
  have htq : ∀ N ∈ omegaNbr Ω M, N ∈ tqMembers3 Ω a := fun N hN =>
    mem_tqMembers3_of_nbr h hint hM ha hN
  set Y : Subgroup G := nbrLayer Ω M a with hYdef
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛU := hypOmegaModU_nbrPair3 h hint hM ha
  have hΛ : HypOmegaGen
      (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛU
  have hΛ'U : HypOmegaModU (.sl2 3 1) (layerFam Ω M a) :=
    Asc77.T3CII.hypOmegaModU_oddQuotientFamily hΛU
  have hΛ' : HypOmegaGen (quotFamily
      (restrictFamily (centralizingMembers (nbrCoreFam Ω M a) {a}) (nbrLayer Ω M a)) N₀) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ'U
  have hΛA := aEmpty_nbrPair3 hΩG hΛ hstd.stand.aEmpty hc2 htq
  have hcl := (secData3_nbrCoreFam h hint hM ha).inClass3
  exact
    { modU := hΛ'U
      hyp := hΛ'
      cls := Q3CL.classicalClause_of_modU hΛ'U
      oddCore := CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y
      gen := omegaGen_quotFamily_of_gen _ N₀ hcl.generated
      aEmpty := C25J.aEmpty_quotFamily_gen hΛ hΛ' hN₀odd hΛA }

end Gen

end CFSG.ClassicalInvolution.Q3.Q3AM
