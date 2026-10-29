module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCase1McL
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Main
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICase2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_normal_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hK : TypeIIKFacts) (hX : ExtraFacts Typ p Shape) (hc : PointConfig Typ G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) :
    M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) := by
  exact typeII_normal_core_proof hS hD1 hU0 hK hX hc hfus

theorem j4_lemma43 {P : Sylow 11 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : ExtraFacts IsJ4Type 11 J4Shape) (hc : PointConfig IsJ4Type G 11 P M x J)
    (hnorm : M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore 11 M : Subgroup G) : Set G)) :
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → u3U0 P x J ≤ Subgroup.normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ rankThreePrimeCore 11 M) (rankThreePrimeCore 11 M) →
      Subgroup.normalizer (Y : Set G) ≤ M := by
  intro Y hY2 hYM hUY hYB
  haveI : Fact (Nat.Prime 11) := ⟨hc.prime⟩
  obtain ⟨hTcard, hTexp, -, hxJ⟩ := typeII_T_structure hX hc
  obtain ⟨-, hUcard, hUS, hxU, hUc, -, -⟩ := typeII_U0_facts hX hc
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  obtain ⟨hRM, hRn, hRcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 11 M
  have hM2loc : IsTwoLocal M := hc.core.1.1
  have hCharM : CFSG.QuasithinUnique.CharTwo M := hS.charTwo M hM2loc
  have hM2 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P₂, hP₂1, hP₂2, hP₂M⟩ := hM2loc
    have hP₂le : P₂ ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP₂M ▸ Subgroup.le_normalizer)
        hP₂M.le hP₂2
    intro h
    exact hP₂1 (le_bot_iff.1 (hP₂le.trans h.le))
  have hO2R : pCoreOf 2 M ≤ rankThreePrimeCore 11 M :=
    Generic49U3.pCoreOf_two_le_relPPrimeCore (by have := hc.five; omega) M
  have hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 11 (H ⊓ M) → H ≤ M :=
    fun H hH hr => le_of_three_le_pRank_inf hD1 hc.sigma hc.core hH hr
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hSP : u3S P x ≤ (P : Subgroup G) := inf_le_left
  have hTP : u3T P x J ≤ (P : Subgroup G) := hTS.trans hSP
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hxM : x ∈ M := hc.generic.2.1.1
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 11 = 1 := hc.generic.2.1.2.2.1
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hxT : x ∉ u3T P x J := fun h => hxJ (hTJ h)
  have hxcT : ∀ t ∈ u3T P x J, x * t = t * x := by
    intro t ht
    have htS : t ∈ Subgroup.centralizer ({x} : Set G) := (hTS ht).2
    exact Subgroup.mem_centralizer_iff.1 htS x rfl
  have hVp : IsPGroup 11 (u3T P x J ⊔ Subgroup.zpowers x : Subgroup G) :=
    P.isPGroup'.to_le (sup_le hTP (Subgroup.zpowers_le.2 hxP))
  have hUV : u3U0 P x J ≤ u3T P x J ⊔ Subgroup.zpowers x :=
    sup_le_sup_right (inf_le_left : u3ZT P x J ≤ u3T P x J) _
  have hUcT : ∀ u ∈ u3U0 P x J, ∀ t ∈ u3T P x J, u * t = t * u :=
    fun u hu t ht => (hUc t (hTS ht) u hu).symm
  have hUcx : ∀ u ∈ u3U0 P x J, u * x = x * u :=
    fun u hu => (hUc x (hUS hxU) u hu).symm
  exact Generic49U3.case1_core hc.five hD1' hM2 hCharM hRM hRn hRcop hO2R hnorm hTM hTcard hTexp hxM hxp
    hx1 hxT hxcT hVp hUV hxU hUcard hUcT hUcx hY2 hYM hUY hYB

theorem mcl_lemma43 {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G} (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : ExtraFacts IsMcLType 5 McLShape) (hc : PointConfig IsMcLType G 5 P M x J)
    (hnorm : M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore 5 M : Subgroup G) : Set G))
    {U : Subgroup G} (hU : IIPlane 5 P x J U) :
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ Subgroup.normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ rankThreePrimeCore 5 M) (rankThreePrimeCore 5 M) →
      Subgroup.normalizer (Y : Set G) ≤ M := by
  intro Y hY2 hYM hUY hYB
  haveI : Fact (Nat.Prime 5) := ⟨hc.prime⟩
  obtain ⟨hTcard, hTexp, -, hxJ⟩ := typeII_T_structure hX hc
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
  have haU : ∃ a ∈ U ⊓ u3T P x J, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : U ⊓ u3T P x J = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact hcon g hg
    have h5 := hU.card_inf
    rw [hbot, Subgroup.card_bot] at h5
    omega
  exact mcl_case1_core hc.five hD1' hM2 hCharM hRM hRn hRcop hO2R hnorm hTM hTcard hTexp hxM hxp hx1 hxT
    hxcT hVp hUV hU.mem haU hY2 hYM hUY hYB


end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
