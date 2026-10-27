module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAE
public import CFSG.ClassicalInvolution.Q3.TL3GlueJ

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

section Core

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

@[expose] noncomputable def coreAt (c : G) (J : Subgroup G) : Subgroup G :=
  tightCore (J ⊓ Subgroup.centralizer ({c} : Set G))

theorem coreAt_le_left (c : G) (J : Subgroup G) : coreAt c J ≤ J :=
  (tightCore_le _).trans inf_le_left

theorem coreAt_le_centralizer (c : G) (J : Subgroup G) :
    coreAt c J ≤ Subgroup.centralizer ({c} : Set G) :=
  (tightCore_le _).trans inf_le_right

@[expose] def coreFamily (Ω : Set (Subgroup G)) (c : G) : Set (Subgroup G) :=
  {M | ∃ J ∈ tqMembers3 Ω c, M = coreAt c J}

theorem coreAt_mem_coreFamily {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    coreAt c J ∈ coreFamily Ω c := ⟨J, hJ, rfl⟩

theorem isSylow2In_coreAt_iff (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G}
    (hcJ : c ∈ trivialOnQuot J) {V : Subgroup G} :
    IsSylow2In V (coreAt c J) ↔ IsSylow2In V J ∧ V ≤ Subgroup.centralizer ({c} : Set G) := by
  have hcomm : ⁅Subgroup.zpowers c, J⁆ ≤ oddCoreOf J :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hcJ ha)).2 x hx
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  have hPc' : P ≤ Subgroup.centralizer ({c} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hPc
  have hPK : P ≤ coreAt c J :=
    le_tightCore_of_isPGroup (le_inf hP.1 hPc') hP.2.1
  constructor
  · intro hV
    have hVK : V ≤ J := hV.1.trans (coreAt_le_left c J)
    have hVc : V ≤ Subgroup.centralizer ({c} : Set G) :=
      hV.1.trans (coreAt_le_centralizer c J)
    have hle : Nat.card P ≤ Nat.card V := hV.natCard_le hP.2.1 hPK
    exact ⟨hP.of_natCard_le hV.2.1 hVK hle, hVc⟩
  · rintro ⟨hVK, hVc⟩
    exact ⟨le_tightCore_of_isPGroup (le_inf hVK.1 hVc) hVK.2.1, hVK.2.1,
      fun V' hV'K hV'2 hVV' => hVK.2.2 V' (hV'K.trans (coreAt_le_left c J)) hV'2 hVV'⟩

theorem mem_USet_of_core (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {U : Subgroup G}
    (hU : U ∈ USet (coreFamily Ω c)) : U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  obtain ⟨L, hL, hRL⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨K, hK, rfl⟩ := hL
  have hRK : IsSylow2In R K := ((isSylow2In_coreAt_iff hc2 hK.2).mp hRL).1
  exact ⟨R, mem_RSet_of_isSylow2In hK.1 hRK, hUR, hcyc, hidx⟩

theorem not_mem_omegaNbr_of_core (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) (hzK : z ∈ coreAt c K)
    (h : ¬ ∃ T : Subgroup G, IsSylow2In T (coreAt c J) ∧
        T ≤ Subgroup.normalizer ((coreAt c K : Subgroup G) : Set G)) :
    J ∉ omegaNbr Ω K := by
  rintro ⟨-, -, R', hR', hR'J, hR'N⟩
  have hR'syl : IsSylow2In R' J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJ.1 hR' hR'J
  have hR'z : R' ≤ Subgroup.centralizer ({z} : Set G) :=
    Sec6Gen.le_centralizer_of_le_normalizer' hz hR'N
  have hzc : c * z = z * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (coreAt_le_centralizer c K hzK)).symm
  obtain ⟨P, hPD, hPc⟩ := exists_isSylow2In_inf_centralizer_of_trivialOnQuot hc2 hJ.2 hzc
  have hR'D : R' ≤ J ⊓ Subgroup.centralizer ({z} : Set G) := le_inf hR'J hR'z
  have hle : Nat.card R' ≤ Nat.card P := hPD.natCard_le hR'syl.2.1 hR'D
  have hPJ : IsSylow2In P J := hR'syl.of_natCard_le hPD.2.1 (hPD.1.trans inf_le_left) hle
  have hPJc : IsSylow2In P (coreAt c J) := (isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hPJ, hPc⟩
  have h3 : 3 ≤ Nat.card P := by
    have := Sec6Gen.eight_le_of_mem_RSet hΩ hR'
    omega
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK.1 hJ.1 hKJ hz hPJ.1 hPJ.2.1 h3
      (hPD.1.trans inf_le_right)
  have hPKc : P ≤ Subgroup.normalizer ((coreAt c K : Subgroup G) : Set G) := by
    intro b hb
    have hb' : b ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :
        Set G) := mem_normalizer_inf' (hPK hb) (Subgroup.le_normalizer (hPc hb))
    exact mem_normalizer_of_conjSub_eq (conjSub_tightCore_of_mem_normalizer hb')
  exact h ⟨P, hPJc, hPKc⟩

end Core

section Cfg

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem cfg64_of_core (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c)
    {zK zJ u v : ↥(Subgroup.centralizer ({c} : Set G))}
    {R T : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    (h : Cfg64 (restrictFamily (coreFamily Ω c) (Subgroup.centralizer ({c} : Set G)))
      ((coreAt c K).subgroupOf (Subgroup.centralizer ({c} : Set G)))
      ((coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))) zK zJ u v R T) :
    Cfg64 Ω K J (zK : G) (zJ : G) (u : G) (v : G)
      (R.map (Subgroup.centralizer ({c} : Set G)).subtype)
      (T.map (Subgroup.centralizer ({c} : Set G)).subtype) := by
  have hKc : coreAt c K ∈ coreFamily Ω c := coreAt_mem_coreFamily hK
  have hJc : coreAt c J ∈ coreFamily Ω c := coreAt_mem_coreFamily hJ
  have hKY : coreAt c K ≤ (Subgroup.centralizer ({c} : Set G)) := coreAt_le_centralizer c K
  have hJY : coreAt c J ≤ (Subgroup.centralizer ({c} : Set G)) := coreAt_le_centralizer c J
  have hKJ : K ≠ J := fun e => h.hKJ (by rw [e])
  have hzKc : IsUniqueInvolution (coreAt c K) (zK : G) :=
    isUniqueInvolution_of_subgroupOf h.hz hKY
  have hzJc : IsUniqueInvolution (coreAt c J) (zJ : G) :=
    isUniqueInvolution_of_subgroupOf h.hj hJY
  have hzK : IsUniqueInvolution K (zK : G) :=
    Q3T7.isUniqueInvolution_of_le_member3 hΩ hK.1 (coreAt_le_left c K) hzKc
  have hzJ : IsUniqueInvolution J (zJ : G) :=
    Q3T7.isUniqueInvolution_of_le_member3 hΩ hJ.1 (coreAt_le_left c J) hzJc
  have hnbrJ : ¬ ∃ T' : Subgroup G, IsSylow2In T' (coreAt c J) ∧
      T' ≤ Subgroup.normalizer ((coreAt c K : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notJ ⟨subgroupOf_mem_restrictFamily hJc hJY, h.hKJ.symm,
      T'.subgroupOf (Subgroup.centralizer ({c} : Set G)), mem_RSet_restrict hJc hJY hT',
      Subgroup.subgroupOf_mono (Subgroup.centralizer ({c} : Set G)) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hKY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hnbrK : ¬ ∃ T' : Subgroup G, IsSylow2In T' (coreAt c K) ∧
      T' ≤ Subgroup.normalizer ((coreAt c J : Subgroup G) : Set G) := by
    rintro ⟨T', hT', hT'N⟩
    exact h.notK ⟨subgroupOf_mem_restrictFamily hKc hKY, h.hKJ, T'.subgroupOf (Subgroup.centralizer ({c} : Set G)),
      mem_RSet_restrict hKc hKY hT', Subgroup.subgroupOf_mono (Subgroup.centralizer ({c} : Set G)) hT'.1, fun x hx =>
        (mem_normalizer_subgroupOf_iff hJY).mp (hT'N (Subgroup.mem_subgroupOf.mp hx))⟩
  have hUmap : (Subgroup.zpowers u).map (Subgroup.centralizer ({c} : Set G)).subtype = Subgroup.zpowers (u : G) :=
    MonoidHom.map_zpowers _ _
  have hVmap : (Subgroup.zpowers v).map (Subgroup.centralizer ({c} : Set G)).subtype = Subgroup.zpowers (v : G) :=
    MonoidHom.map_zpowers _ _
  have hUG : Subgroup.zpowers (u : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hU
    rw [hUmap] at h1
    exact mem_USet_of_core hc2 h1
  have hVG : Subgroup.zpowers (v : G) ∈ USet Ω := by
    have h1 := map_mem_USet_restrict h.hV
    rw [hVmap] at h1
    exact mem_USet_of_core hc2 h1
  have hUK : Subgroup.zpowers (u : G) ≤ K := by
    rw [← hUmap]
    refine (Subgroup.map_mono h.hUK).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hKY]
    exact coreAt_le_left c K
  have hVJ : Subgroup.zpowers (v : G) ≤ J := by
    rw [← hVmap]
    refine (Subgroup.map_mono h.hVJ).trans ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hJY]
    exact coreAt_le_left c J
  have hUV : Commutes (Subgroup.zpowers (u : G)) (Subgroup.zpowers (v : G)) := by
    rw [← hUmap, ← hVmap]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (h.hUV a ha b hb)
  have hRKc : IsSylow2In (R.map (Subgroup.centralizer ({c} : Set G)).subtype) (coreAt c K) := by
    have := (isSylow2In_map_subtype_iff (Y := (Subgroup.centralizer ({c} : Set G)))).mpr h.hR
    rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at this
  have hTJc : IsSylow2In (T.map (Subgroup.centralizer ({c} : Set G)).subtype) (coreAt c J) := by
    have := (isSylow2In_map_subtype_iff (Y := (Subgroup.centralizer ({c} : Set G)))).mpr h.hT
    rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at this
  have hUVmap : (Subgroup.zpowers u ⊔ Subgroup.zpowers v).map (Subgroup.centralizer ({c} : Set G)).subtype =
      Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers (v : G) := by
    rw [Subgroup.map_sup, hUmap, hVmap]
  exact
    { hΩ := hΩ
      hK := hK.1
      hJ := hJ.1
      hKJ := hKJ
      hz := hzK
      hj := hzJ
      notJ := not_mem_omegaNbr_of_core hΩ hc2 hK hJ hKJ hzK hzKc.mem hnbrJ
      notK := not_mem_omegaNbr_of_core hΩ hc2 hJ hK hKJ.symm hzJ hzJc.mem hnbrK
      hU := hUG
      hUK := hUK
      hV := hVG
      hVJ := hVJ
      hUV := hUV
      hR := ((isSylow2In_coreAt_iff hc2 hK.2).mp hRKc).1
      hT := ((isSylow2In_coreAt_iff hc2 hJ.2).mp hTJc).1
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

theorem aEmpty_coreFamily (hΩ : HypOmegaGen Ω)
    (hΛ : HypOmegaGen (restrictFamily (coreFamily Ω c) (Subgroup.centralizer ({c} : Set G))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    ∀ L ∈ restrictFamily (coreFamily Ω c) (Subgroup.centralizer ({c} : Set G)),
      AEmpty (restrictFamily (coreFamily Ω c) (Subgroup.centralizer ({c} : Set G))) L := by
  rintro K₁ hK₁ J₁ hJs hJn zK zJ hzK hzJ
  have hK₁' := hK₁
  have hJ₁' := hJs.1
  obtain ⟨Kc, hKc, hKcY, rfl⟩ := hK₁
  obtain ⟨Jc, hJc, hJcY, rfl⟩ := hJs.1
  obtain ⟨K, hK, rfl⟩ := hKc
  obtain ⟨J, hJ, rfl⟩ := hJc
  obtain ⟨u, v, R, T, hcfg⟩ := exists_cfg64 hΛ hK₁' hJ₁' hzK hzJ hJs hJn
  have hcfgG := cfg64_of_core hΩ hc2 hK hJ hcfg
  have hstar : J ∈ omegaStarNbr Ω K :=
    ⟨hJ.1, hcfgG.hKJ.symm, Subgroup.zpowers (v : G), hcfgG.hV, hcfgG.hVJ,
      hcfgG.symm.U_le_normalizer⟩
  obtain ⟨g, hg, hgK⟩ := hA K hK.1 J hstar hcfgG.notJ (zK : G) (zJ : G) hcfgG.hz hcfgG.hj
  obtain ⟨ρ, hρ, hρK⟩ := exists_mem_sup_conj_of_cfg64 hcfgG hg hgK
  rw [← Subgroup.map_sup] at hρ
  obtain ⟨ρ₁, hρ₁, rfl⟩ := hρ
  refine ⟨ρ₁, sup_le hcfg.R_le_Y hcfg.T_le_Y hρ₁, ?_⟩
  have hρK' : conjSub (ρ₁ : G) K = J := hρK
  have hρC : (ρ₁ : G) ∈ (Subgroup.centralizer ({c} : Set G)) := ρ₁.2
  rw [conjSub_subgroupOf (Subgroup.centralizer ({c} : Set G)) ρ₁ (coreAt c K)]
  show (conjSub (ρ₁ : G) (coreAt c K)).subgroupOf (Subgroup.centralizer ({c} : Set G)) = (coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))
  congr 1
  unfold coreAt
  rw [conjSub_tightCore, conjSub_inf, hρK', conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hρC)]

end Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent
