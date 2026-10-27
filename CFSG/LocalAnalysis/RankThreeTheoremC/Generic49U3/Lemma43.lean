module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Assembly
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

theorem u3_normal_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (h123 : KFactWeakClosureHeis)
    (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) :
    M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) :=
  u3_normal_core_proof hS hD1 hU0 hInn hWC h123 hc hfus

theorem u3_lemma43 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J)
    (hnorm : M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore p M : Subgroup G) : Set G)) :
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → u3U0 P x J ≤ Subgroup.normalizer (Y : Set G) →
      CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ rankThreePrimeCore p M) (rankThreePrimeCore p M) →
      Subgroup.normalizer (Y : Set G) ≤ M := by
  intro Y hY2 hYM hUY hYB
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨hTcard, hTexp, -, hxJ⟩ := u3_T_structure hc
  obtain ⟨-, hUcard, hUS, hxU, hUc, -, -⟩ := u3U0_facts hc
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  obtain ⟨hRM, hRn, hRcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  have hM2loc : IsTwoLocal M := hc.core.1.1
  have hCharM : CFSG.QuasithinUnique.CharTwo M := hS.charTwo M hM2loc
  have hM2 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P₂, hP₂1, hP₂2, hP₂M⟩ := hM2loc
    have hP₂le : P₂ ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP₂M ▸ Subgroup.le_normalizer)
        hP₂M.le hP₂2
    intro h
    exact hP₂1 (le_bot_iff.1 (hP₂le.trans h.le))
  have hO2R : pCoreOf 2 M ≤ rankThreePrimeCore p M :=
    pCoreOf_two_le_relPPrimeCore (by have := hc.five; omega) M
  have hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M :=
    fun H hH hr => le_of_three_le_pRank_inf hD1 hc.sigma hc.core hH hr
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hTP : u3T P x J ≤ (P : Subgroup G) := hTS.trans hSP
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hxM : x ∈ M := hc.generic.2.1.1
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hxT : x ∉ u3T P x J := fun h => hxJ (hTJ h)
  have hxcT : ∀ t ∈ u3T P x J, x * t = t * x := by
    intro t ht
    have htS : t ∈ Subgroup.centralizer ({x} : Set G) := (hTS ht).2
    exact Subgroup.mem_centralizer_iff.1 htS x rfl
  have hVp : IsPGroup p (u3T P x J ⊔ Subgroup.zpowers x : Subgroup G) :=
    P.isPGroup'.to_le (sup_le hTP (Subgroup.zpowers_le.2 hxP))
  have hUV : u3U0 P x J ≤ u3T P x J ⊔ Subgroup.zpowers x :=
    sup_le_sup_right (inf_le_left : u3ZT P x J ≤ u3T P x J) _
  have hUcT : ∀ u ∈ u3U0 P x J, ∀ t ∈ u3T P x J, u * t = t * u :=
    fun u hu t ht => (hUc t (hTS ht) u hu).symm
  have hUcx : ∀ u ∈ u3U0 P x J, u * x = x * u :=
    fun u hu => (hUc x (hUS hxU) u hu).symm
  exact case1_core hc.five hD1' hM2 hCharM hRM hRn hRcop hO2R hnorm hTM hTcard hTexp hxM hxp hx1 hxT
    hxcT hVp hUV hxU hUcard hUcT hUcx hY2 hYM hUY hYB

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
