module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15STrans
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SOrbit
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64Ex
public import CFSG.ClassicalInvolution.Q3.Q3NLExact
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem isSylow2In_exactCore3_iff {K : Subgroup G} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hcK : c ∈ trivialOnQuot K) {V : Subgroup G} :
    IsSylow2In V (exactCore3 c K) ↔ IsSylow2In V K ∧ V ≤ Subgroup.centralizer ({c} : Set G) := by
  have hcomm : ⁅Subgroup.zpowers c, K⁆ ≤ oddCoreOf K :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hcK ha)).2 x hx
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  have hPc' : P ≤ Subgroup.centralizer ({c} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hPc
  have hPK : P ≤ exactCore3 c K := le_inf hP.1 hPc'
  constructor
  · intro hV
    have hVK : V ≤ K := hV.1.trans (exactCore3_le_left c K)
    have hVc : V ≤ Subgroup.centralizer ({c} : Set G) :=
      hV.1.trans (exactCore3_le_centralizer c K)
    have hle : Nat.card P ≤ Nat.card V := hV.natCard_le hP.2.1 hPK
    exact ⟨hP.of_natCard_le hV.2.1 hVK hle, hVc⟩
  · rintro ⟨hVK, hVc⟩
    exact ⟨le_inf hVK.1 hVc, hVK.2.1, fun V' hV'K hV'2 hVV' =>
      hVK.2.2 V' (hV'K.trans (exactCore3_le_left c K)) hV'2 hVV'⟩

theorem mem_USet_of_exact3 (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {U : Subgroup G} (hU : U ∈ USet (centralizingMembers (exactFamily3 Ω c) {c})) :
    U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨⟨K, hK, rfl⟩, -⟩ := hL
  have hRK : IsSylow2In R K := ((isSylow2In_exactCore3_iff hc2 hK.2).mp hRL).1
  exact ⟨R, mem_RSet_of_isSylow2In hK.1 hRK, hUR, hcyc, hidx⟩

theorem isUniqueInvolution_of_le_member3 (hΩ : HypOmegaGen Ω) {K A : Subgroup G} (hK : K ∈ Ω)
    (hAK : A ≤ K) {z : G} (hz : IsUniqueInvolution A z) : IsUniqueInvolution K z := by
  obtain ⟨⟨b, hb⟩, -⟩ := hΩ.omega1 K hK
  have hzb : z = b := (hb.unique z (hAK hz.mem) hz.sq).resolve_left hz.ne_one
  rw [hzb]
  exact hb

end Sylow

section Nbr

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem not_mem_omegaNbr_of_exact3 (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) (hzK : z ∈ exactCore3 c K)
    (h : ¬ ∃ T : Subgroup G, IsSylow2In T (exactCore3 c J) ∧
        T ≤ Subgroup.normalizer ((exactCore3 c K : Subgroup G) : Set G)) :
    J ∉ omegaNbr Ω K := by
  rintro ⟨-, -, R', hR', hR'J, hR'N⟩
  have hR'syl : IsSylow2In R' J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ.1 hR' hR'J
  have hR'z : R' ≤ Subgroup.centralizer ({z} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' hz hR'N
  have hzc : c * z = z * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (exactCore3_le_centralizer c K hzK)).symm
  obtain ⟨P, hPD, hPc⟩ := exists_isSylow2In_inf_centralizer_of_trivialOnQuot hc2 hJ.2 hzc
  have hR'D : R' ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := le_inf hR'J hR'z
  have hle : Nat.card R' ≤ Nat.card P := hPD.natCard_le hR'syl.2.1 hR'D
  have hPJ : IsSylow2In P J := hR'syl.of_natCard_le hPD.2.1 (hPD.1.trans inf_le_left) hle
  have hPJc : IsSylow2In P (exactCore3 c J) :=
    (isSylow2In_exactCore3_iff hc2 hJ.2).mpr ⟨hPJ, hPc⟩
  have h3 : 3 ≤ Nat.card P := by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hR'
    omega
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 hKJ hz hPJ.1 hPJ.2.1 h3
      (hPD.1.trans inf_le_right)
  have hPKc : P ≤ Subgroup.normalizer ((exactCore3 c K : Subgroup G) : Set G) := by
    intro b hb
    exact mem_normalizer_inf (hPK hb) (Subgroup.le_normalizer (hPc hb))
  exact h ⟨P, hPJc, hPKc⟩

end Nbr

section Cfg

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem cfg64_of_exact3 (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c)
    {zK zJ u v : ↥(exactLayer3 Ω c)} {R T : Subgroup ↥(exactLayer3 Ω c)}
    (h : Cfg64 (exactPair3 Ω c) ((exactCore3 c K).subgroupOf (exactLayer3 Ω c))
      ((exactCore3 c J).subgroupOf (exactLayer3 Ω c)) zK zJ u v R T) :
    Cfg64 Ω K J (zK : G) (zJ : G) (u : G) (v : G)
      (R.map (exactLayer3 Ω c).subtype) (T.map (exactLayer3 Ω c).subtype) := by
  have hKc : exactCore3 c K ∈ centralizingMembers (exactFamily3 Ω c) {c} :=
    ⟨exactCore3_mem_exactFamily3 hK, exactCore3_le_centralizer c K⟩
  have hJc : exactCore3 c J ∈ centralizingMembers (exactFamily3 Ω c) {c} :=
    ⟨exactCore3_mem_exactFamily3 hJ, exactCore3_le_centralizer c J⟩
  have hKY : exactCore3 c K ≤ exactLayer3 Ω c := le_centralizingLayer hKc
  have hJY : exactCore3 c J ≤ exactLayer3 Ω c := le_centralizingLayer hJc
  have hKJ : K ≠ J := fun e => h.hKJ (by rw [e])
  have hzKc : IsUniqueInvolution (exactCore3 c K) (zK : G) :=
    isUniqueInvolution_of_subgroupOf h.hz hKY
  have hzJc : IsUniqueInvolution (exactCore3 c J) (zJ : G) :=
    isUniqueInvolution_of_subgroupOf h.hj hJY
  have hzK : IsUniqueInvolution K (zK : G) :=
    isUniqueInvolution_of_le_member3 hΩ hK.1 (exactCore3_le_left c K) hzKc
  have hzJ : IsUniqueInvolution J (zJ : G) :=
    isUniqueInvolution_of_le_member3 hΩ hJ.1 (exactCore3_le_left c J) hzJc
  have hnbrJ : ¬ ∃ T' : Subgroup G, IsSylow2In T' (exactCore3 c J) ∧
      T' ≤ Subgroup.normalizer ((exactCore3 c K : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notJ ⟨subgroupOf_mem_restrictFamily hJc hJY, h.hKJ.symm,
      T'.subgroupOf (exactLayer3 Ω c), mem_RSet_restrict hJc hJY hT',
      Subgroup.subgroupOf_mono (exactLayer3 Ω c) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hKY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hnbrK : ¬ ∃ T' : Subgroup G, IsSylow2In T' (exactCore3 c K) ∧
      T' ≤ Subgroup.normalizer ((exactCore3 c J : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notK ⟨subgroupOf_mem_restrictFamily hKc hKY, h.hKJ, T'.subgroupOf (exactLayer3 Ω c),
      mem_RSet_restrict hKc hKY hT', Subgroup.subgroupOf_mono (exactLayer3 Ω c) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hJY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hUmap : (Subgroup.zpowers u).map (exactLayer3 Ω c).subtype = Subgroup.zpowers (u : G) :=
    MonoidHom.map_zpowers _ _
  have hVmap : (Subgroup.zpowers v).map (exactLayer3 Ω c).subtype = Subgroup.zpowers (v : G) :=
    MonoidHom.map_zpowers _ _
  have hUG : Subgroup.zpowers (u : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hU
    rw [hUmap] at h1
    exact mem_USet_of_exact3 hc2 h1
  have hVG : Subgroup.zpowers (v : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hV
    rw [hVmap] at h1
    exact mem_USet_of_exact3 hc2 h1
  have hUK : Subgroup.zpowers (u : G) ≤ K := by
    rw [← hUmap]
    refine (Subgroup.map_mono h.hUK).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hKY]
    exact exactCore3_le_left c K
  have hVJ : Subgroup.zpowers (v : G) ≤ J := by
    rw [← hVmap]
    refine (Subgroup.map_mono h.hVJ).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
    exact exactCore3_le_left c J
  have hUV : Commutes (Subgroup.zpowers (u : G)) (Subgroup.zpowers (v : G)) := by
    rw [← hUmap, ← hVmap]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (h.hUV a ha b hb)
  have hRKc : IsSylow2In (R.map (exactLayer3 Ω c).subtype) (exactCore3 c K) := by
    have := (isSylow2In_map_subtype_iff (Y := exactLayer3 Ω c)).mpr h.hR
    rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
  have hTJc : IsSylow2In (T.map (exactLayer3 Ω c).subtype) (exactCore3 c J) := by
    have := (isSylow2In_map_subtype_iff (Y := exactLayer3 Ω c)).mpr h.hT
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  have hUVmap : (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map (exactLayer3 Ω c).subtype =
      Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers (v : G) := by
    rw [Subgroup.map_sup, hUmap, hVmap]
  exact
    { hΩ := hΩ
      hK := hK.1
      hJ := hJ.1
      hKJ := hKJ
      hz := hzK
      hj := hzJ
      notJ := not_mem_omegaNbr_of_exact3 hΩ hc2 hK hJ hKJ hzK hzKc.mem hnbrJ
      notK := not_mem_omegaNbr_of_exact3 hΩ hc2 hJ hK hKJ.symm hzJ hzJc.mem hnbrK
      hU := hUG
      hUK := hUK
      hV := hVG
      hVJ := hVJ
      hUV := hUV
      hR := ((isSylow2In_exactCore3_iff hc2 hK.2).mp hRKc).1
      hT := ((isSylow2In_exactCore3_iff hc2 hJ.2).mp hTJc).1
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

theorem aEmpty_exactPair3 (hΩ : HypOmegaGen Ω) (hΛ : HypOmegaGen (exactPair3 Ω c))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    ∀ L ∈ exactPair3 Ω c, AEmpty (exactPair3 Ω c) L := by
  rintro K₁ hK₁ J₁ hJs hJn zK zJ hzK hzJ
  have hK₁' := hK₁
  have hJ₁' := hJs.1
  obtain ⟨Kc, hKc, hKcY, rfl⟩ := hK₁
  obtain ⟨Jc, hJc, hJcY, rfl⟩ := hJs.1
  obtain ⟨⟨K, hK, rfl⟩, -⟩ := hKc
  obtain ⟨⟨J, hJ, rfl⟩, -⟩ := hJc
  obtain ⟨u, v, R, T, hcfg⟩ := exists_cfg64 hΛ hK₁' hJ₁' hzK hzJ hJs hJn
  have hcfgG := cfg64_of_exact3 hΩ hc2 hK hJ hcfg
  have hstar : J ∈ omegaStarNbr Ω K :=
    ⟨hJ.1, hcfgG.hKJ.symm, Subgroup.zpowers (v : G), hcfgG.hV, hcfgG.hVJ,
      hcfgG.symm.U_le_normalizer⟩
  obtain ⟨g, hg, hgK⟩ := hA K hK.1 J hstar hcfgG.notJ (zK : G) (zJ : G) hcfgG.hz hcfgG.hj
  obtain ⟨ρ, hρ, hρK⟩ := exists_mem_sup_conj_of_cfg64 hcfgG hg hgK
  rw [← Subgroup.map_sup] at hρ
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hρ
  refine ⟨ρ₁, sup_le hcfg.R_le_Y hcfg.T_le_Y hρ₁, ?_⟩
  have hρc : (ρ₁ : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    centralizingLayer_le_centralizer _ _ ρ₁.2
  have e : (ρ₁ : G) * c * (ρ₁ : G)⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hρc]
    group
  have h1 := exactCore3_conjSub (ρ₁ : G) c K
  rw [e] at h1
  have hρK' : conjSub (ρ₁ : G) K = J := hρK
  rw [hρK'] at h1
  rw [conjSub_subgroupOf (exactLayer3 Ω c) ρ₁ (exactCore3 c K), ← h1]

end Cfg

end CFSG.ClassicalInvolution.Q3.Q3T7
