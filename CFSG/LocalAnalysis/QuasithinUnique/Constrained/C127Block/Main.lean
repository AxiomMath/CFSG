module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Lin2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C127Block.Degree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127FFK
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127MPar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A3Type
public import CFSG.Quasithin.Background.GoldschmidtE23Setup

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace L246C127

namespace C127Block

open MPar MAut

variable {G : Type} [Group G] [Finite G]

theorem kBlockType_of_comp (hP4 : AsB15Part4) (hComp : B69.AsB69ComponentK)
    (hDeg : B69.AsB69AltDegree) {P T M K : Subgroup G} (hmp : MinParabolic P T M)
    (hP : CharTwo P) (hPG : CFSG.SectionRank.IsKGroupCat ↥P) (hK : IsBlock2 P K)
    (hKJ : ⁅K, thompsonJ T⁆ = K) (hPK : P = T ⊔ conjClosure K T) (hUT : blockU K ≤ T) :
    KBlockTypeOf K := by
  classical
  have hTP : T ≤ P := hmp.isSylow.1
  have hT2 : IsPGroup 2 T := hmp.isSylow.2.1
  have hshort : IsShort2 K := hK.1
  have hKP : K ≤ P := hK.2.1
  rcases hshort.2.2.2.1 with hq | h3
  swap
  · exact Or.inr ⟨1, le_rfl, by simpa using L246.isAltType_three hshort h3⟩
  have hV : IsElemAbelian 2 (W0 T K) := isElemAbelian_W0 hP hTP hK
  set V := W0 T K with hVdef
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := P_le_normalizer_W0 hP hTP hK hPK
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hKP.trans hPN
  have hUV : blockU K ≤ V := blockU_le_W0 T K
  have hVP : V ≤ P := (W0_le_T hUT).trans hTP
  have hsubK : IsSubnormal K P := C1GN.isSubnormal_of_isBlock2 hK
  have hVK : ⁅V, K⁆ ≤ blockU K := commutator_le_blockU hshort hsubK hVP
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVP).2 hPN) (hT2.to_le (W0_le_T hUT))
  have hQ : blockQ K ≤ Subgroup.centralizer (V : Set G) :=
    (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hKP hK.2.2).trans
      (pCoreOf_le_centralizer_W0 hK hTP)
  have hker := ker_toAutI_eq_pCore hV hshort hKN hUV hQ
  have hqb : CFSG.IsQuasisimple ↥(autI hV K) := isQuasisimple_autI_of_ker hV hKN hker hq
  have hKbOpen : CFSG.Open.IsQuasisimple ↥(autI hV K) :=
    ⟨Group.isPerfect_def.1 hqb.1, hqb.2.1⟩
  have hred : IsTwoReducedIn P V := isTwoReducedIn_W0 hmp hP hK hPK hUT
  have hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) :=
    not_thompsonJ_le_centralizer_W0 hP hTP hK hKJ
  have hHV : ¬ P ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (hTP.trans hle))
  have hJH : ¬ thompsonJ P ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hmp.isSylow).trans hle)
  obtain ⟨hFF, -⟩ := B2_7_of_not_le hV hVP hPN hJH
  have hmpS := GE23.minParabolic_star hV hmp hred hHV
  have hO2 := GE23.pCoreOf_star hV hred
  have hns : ¬ Group.IsSolvable ↥P := by
    intro hs
    have hKs : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKP)
        (Subgroup.inclusion_injective hKP)
    have hKbs : Group.IsSolvable ↥(autI hV K) :=
      Group.isSolvable_of_surjective (toAutI_surjective hV K hKN)
    haveI : Nontrivial ↥(autI hV K) := CFSG.LocalCores.isQuasisimple_nontrivial hqb
    haveI : Group.IsPerfect ↥(autI hV K) := hqb.1
    exact Group.IsPerfect.not_isSolvable (autI hV K) hKbs
  have hnsS := GE23.not_isSolvable_star hV hmp hred hHV hns
  have hKGS : CFSG.SectionRank.IsKGroupCat ↥(autI hV P) :=
    C24Pf.isKGroupCat_autI hV hPN hPG
  have hsubKb : IsSubnormal (autI hV K) (autI hV P) := by
    have h2' : IsSubnormal (K.subgroupOf P) ⊤ := by
      have := A3.subnormal_comap P.subtype hsubK
      have e : P.comap P.subtype = ⊤ := by ext x; simp
      rwa [e] at this
    have h3'' := A3.subnormal_map (convHom hV P hPN) h2'
    rw [← autI_eq_map_convHom hV hPN hKP, Subgroup.map_top, range_convHom hV P hPN] at h3''
    exact h3''
  have hL : CFSG.Open.IsComponentOf (autI hV K) (autI hV P) :=
    ⟨autI_mono hV hKP, hsubKb, hKbOpen⟩
  obtain ⟨A, hA, hLA, hW, hshape⟩ :=
    exists_shape hP4 hComp (fun v : IntMod V hV => IntMod.sq_eq_one v) hKGS hmpS hO2 hFF hnsS hL
  have hcs := hshape
  rcases hshape with ⟨⟨e, he, hnat⟩, -, -⟩ | ⟨k, hk, hAlt⟩
  · obtain ⟨n, hn, hlin⟩ := isLin2Type_of_natural_shape hV hKN hshort hUV hVK hker hqb he hnat
    exact Or.inl ⟨n, hn, hlin⟩
  · have hAltK : B69.AltShapeK k (autI hV M) A (autI hV K) (commV (autI hV K)) := hAlt
    have hk2 : 2 ≤ k := two_le_of_altShapeK hk hKbOpen hAltK
    have hcomm := commV_sup_eq (fun v : IntMod V hV => IntMod.sq_eq_one v) hA hKbOpen hLA hW hcs
    have hty := isAltType_of_altShapeK hV hKN hshort hUV hVK hker hk2 hcomm hAltK
    obtain ⟨j, hj⟩ := hDeg (IntMod V hV) (fun v : IntMod V hV => IntMod.sq_eq_one v) (autI hV P)
      (autI hV T) (autI hV M) A (autI hV K) ⟨hKGS, hmpS, hO2, hFF, hnsS, hA, hL, hLA⟩
      (commV (autI hV K)) hW k hk hAltK
    refine Or.inr ⟨j, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0
        omega
      · exact h0
    · have h2j : 2 ^ j + 1 = 2 * k + 1 := by omega
      rw [h2j]
      exact hty

end C127Block

end L246C127

end CFSG.QuasithinUnique

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127
open scoped commutatorElement

theorem c127KBlockType_of_deg (hP4 : AsB15Part4) (hComp : B69.AsB69ComponentK)
    (hDeg : B69.AsB69AltDegree) : C127KBlockType := by
  intro G _ _ X T P K hX hT hKG hP hK hKJ hPK
  obtain ⟨M, hmp⟩ := MPar.exists_minParabolic_of_uFamHat hT hP
  have hTP : T ≤ P := hmp.isSylow.1
  have hPX : P ≤ X := hP.1.1
  have hPc : CharTwo P := C1GN.charTwo_of_le hX hT hTP hPX
  have S : Setting X T P K := ⟨hX, hT, hPX, hTP, hK⟩
  have hPG : CFSG.SectionRank.IsKGroupCat ↥P :=
    CFSG.SectionRank.IsKGroupCat.of_mulEquiv (hKG.subgroup (P.subgroupOf X))
      (Subgroup.subgroupOfEquivOfLe hPX).symm
  exact C127Block.kBlockType_of_comp hP4 hComp hDeg hmp hPc hPG hK hKJ hPK S.blockU_le_T

theorem c127KBlockType_of (hP4 : AsB15Part4) (hComp : B69.AsB69ComponentK) : C127KBlockType :=
  c127KBlockType_of_deg hP4 hComp (asB69AltDegree_of hP4 hComp)

end CFSG.Quasithin
