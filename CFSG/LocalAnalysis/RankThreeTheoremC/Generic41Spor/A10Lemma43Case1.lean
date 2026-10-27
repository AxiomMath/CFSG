module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PlaneStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCase1McL
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Main
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_case1 (hS : Setting G) (hD1 : TheoremD1 G) (hX : A10Facts)
    (hc : PointConfig IsA10Type G 5 P M x J) {U : Subgroup G} (hU : IIPlane 5 P x J U)
    {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hUY : U ≤ Subgroup.normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ rankThreePrimeCore 5 M) (rankThreePrimeCore 5 M))
    (hYn : Y ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore 5 M : Subgroup G) : Set G)) :
    Subgroup.normalizer (Y : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 5) := ⟨hc.prime⟩
  obtain ⟨hTcard, hTel, hxJ⟩ := plane_T_structure hX.sylow hc
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  obtain ⟨hRM, hRn, hRcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 5 M
  have hM2loc : IsTwoLocal M := hc.core.1.1
  have hCharM : CFSG.QuasithinUnique.CharTwo M := hS.charTwo M hM2loc
  have hM2 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P₂, hP₂1, hP₂2, hP₂M⟩ := hM2loc
    have hP₂le : P₂ ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP₂M ▸ Subgroup.le_normalizer)
        hP₂M.le hP₂2
    intro h
    exact hP₂1 (le_bot_iff.1 (hP₂le.trans h.le))
  have hO2R : pCoreOf 2 M ≤ rankThreePrimeCore 5 M :=
    Generic49U3.pCoreOf_two_le_relPPrimeCore (by have := hc.five; omega) M
  have hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 5 (H ⊓ M) → H ≤ M :=
    fun H hH hr => le_of_three_le_pRank_inf hD1 hc.sigma hc.core hH hr
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hTP : u3T P x J ≤ (P : Subgroup G) := hTS.trans hSP
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hxM : x ∈ M := hc.generic.2.1.1
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hxT : x ∉ u3T P x J := fun h => hxJ (hTJ h)
  have hxcT : ∀ t ∈ u3T P x J, x * t = t * x := by
    intro t ht
    have htS : t ∈ Subgroup.centralizer ({x} : Set G) := (hTS ht).2
    exact Subgroup.mem_centralizer_iff.1 htS x rfl
  have hVp : IsPGroup 5 (u3T P x J ⊔ Subgroup.zpowers x : Subgroup G) :=
    P.isPGroup'.to_le (sup_le hTP (Subgroup.zpowers_le.2 hxP))
  have hUV : U ≤ u3T P x J ⊔ Subgroup.zpowers x :=
    mcl_le_sup_of_card hc.prime hU.elem.1 hU.card hU.card_inf hU.mem hxp hx1 hxT
  have hVc : u3T P x J ⊔ Subgroup.zpowers x ≤
      Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G) := by
    refine sup_le (fun t ht => Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => (hxcT h hh).symm))
    exact congrArg Subtype.val (hTel.1.is_comm.comm (⟨h, hh⟩ : u3T P x J) ⟨t, ht⟩)
  have hUcT : ∀ u ∈ U, ∀ t ∈ u3T P x J, u * t = t * u := fun u hu t ht =>
    (Subgroup.mem_centralizer_iff.1 (hVc (hUV hu)) t ht).symm
  have hUcx : ∀ u ∈ U, u * x = x * u := fun u hu =>
    (Subgroup.mem_centralizer_iff.1 (hU.le hu).2 x rfl).symm
  exact Generic49U3.case1_core_of_Y hc.five hD1' hM2 hCharM hRM hRn hRcop hO2R hYn hTM (le_refl 2)
    hTcard hTel.2 hxM hxp hx1 hxT hxcT hVp hUV hU.mem hU.card hUcT hUcx hY2 hYM hUY hYB

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
