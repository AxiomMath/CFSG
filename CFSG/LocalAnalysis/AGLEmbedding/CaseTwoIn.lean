module

public import CFSG.LocalAnalysis.AGLEmbedding.KGenTwoModAbFix
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPIdent
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactCaseTwoAlphaThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) →
    Subgroup.center K ≠ ⊥ → IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup 3 L →
      ∀ f : A →* L, Function.Surjective f → Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
      ∀ T : Sylow 3 K,
        (KGenTwoModAbFix 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧
          (3 ≤ Open.pRank 3 (⊤ : Subgroup K) ∨ KOutNormalSylow 3 K)) ∨
        (GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K))

namespace ReducedNongeneration

section Three

variable {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {X₀ : Subgroup X}

theorem false_of_caseTwoThree_of_mem (h : ReducedNongeneration 3 X R X₀)
    (hR3 : Open.pRank 3 (R : Subgroup X) ≤ 3) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hAT : KFactCaseTwoAlphaThree)
    {A : Subgroup K} {Λ : Type} [Group Λ] (hiso : IsCaseTwoGroup 3 Λ) (f : A →* Λ)
    (hf : Function.Surjective f) : False := by
  have hp := h.prime
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hrank : Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rw [← (SectionRank.pRank_sylow T).1,
      ← pRank_map_of_injective 3 hp K.subtype K.subtype_injective, hT]
    exact (pRank_mono 3 hp inf_le_left).trans hR3
  rcases hAT K hK.2.2 (hX.isCatalogGroup_center_quotient hK) (center_ne_bot_of_mem hp hz hzp hzK)
      (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK) (h.isCyclic_center hK hKn) A Λ hiso
      f hf hrank T with ⟨hgen, hZ3, h3 | hout⟩ | ⟨hc, h3⟩
  · exact h.false_of_three_le_pRank_of_le hKn
      (h.le_of_kGenTwoModAbFix hz hzp hK hKn hzK hZ3 hgen) h3
  · exact h.false_of_kOutNormalSylow (h.le_of_kGenTwoModAbFix hz hzp hK hKn hzK hZ3 hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout
  · exact h.false_of_three_le_pRank_of_le hKn (le_of_weakCore_eq_top h T hT hc) h3

end Three

end ReducedNongeneration

section Data

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}

theorem D1CaseTwoDataAt.false_of_in_three (hd : D1CaseTwoDataAt 3 P M H R Rbar)
    (hAut : KFactCycAut)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier)
    (hAT : KFactCaseTwoAlphaThree) (hnosp : D1CaseTwoNoSP 3 M H R)
    (hin : ∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) : False := by
  obtain ⟨z, hz, hout⟩ := hin
  obtain ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ := hz
  have hnSP := hnosp L hL hLX z hzR hzp hRz hzL
  obtain ⟨m, hm, T, hRT, hTP⟩ := hd.cfg.exists_sylow_centralizer hRz
  obtain ⟨Pbar, K, hc⟩ := D1CaseTwoDataAt.exists_czReduced hd hAut hS hSyl
    ⟨L, hL, hLX, hzR, hzp, hRz, hzL⟩ hm hRT hTP
  unfold D1CzOutside at hout
  push Not at hout
  obtain ⟨KC, hKC, hzKC⟩ := hout
  rw [hc.unique KC hKC] at hzKC
  have hiso : IsCaseTwoGroup 3 L :=
    hd.cfg.red.isCaseTwoGroup_of_not_le_of_aut hd.cfg.catalog (hAut _ _ _ _ hd.cfg.red
        hd.cfg.catalog) hS hd.cyclic hd.rank hL hLX
  have hLp : Group.IsPerfect L := ⟨hL.2.2.1⟩
  obtain ⟨A₀, φ, hφ⟩ := D1CaseTwoDataAt.exists_surjective_czQuot hd hL hzp hzL
  obtain ⟨A, f, hf⟩ := hc.exists_surjective_of_surjective hSch hLp φ hφ
  exact ReducedNongeneration.false_of_caseTwoThree_of_mem hc.red (hc.pRank_eq_three hnSP).le
    hc.catalog hc.center hc.order hc.comp hc.normal hzKC hAT hiso f hf

theorem D1CaseTwoData.false_of_in_three (hd : D1CaseTwoData 3 P M H R Rbar) (hβ : KFactBeta)
    (hS : KFactSeitzCyc) (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier)
    (hAT : KFactCaseTwoAlphaThree) (hnosp : D1CaseTwoNoSP 3 M H R)
    (hin : ∃ z : H, D1CaseTwoCand 3 M H R z ∧ ¬ D1CzOutside 3 (z : G)) : False :=
  D1CaseTwoDataAt.false_of_in_three (hd := hd.toAt) (hAut := (kFactCycAut_of_kFactBeta hβ))
    (hS := hS) (hSyl := hSyl) (hSch := hSch) (hAT := hAT) (hnosp := hnosp) (hin := hin)

end Data

theorem d1CaseTwoPosZeroInThree_of (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier) (hAT : KFactCaseTwoAlphaThree) :
    D1CaseTwoPosZeroInThree := by
  intro G _ _ P M H R Rbar hd hnosp hin
  intros
  exact D1CaseTwoData.false_of_in_three hd hβ hS hSyl hSch hAT hnosp hin

theorem d1CaseTwoNTwoAResInThree_of (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier) (hAT : KFactCaseTwoAlphaThree) :
    D1CaseTwoNTwoAResInThree := by
  intro G _ _ P M H R Rbar hd hnosp hin
  intros
  exact D1CaseTwoData.false_of_in_three hd hβ hS hSyl hSch hAT hnosp hin

theorem d1CaseTwoZZThreeIn_of (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hSyl : KFactCaseTwoSylow) (hSch : KFactCatalogSchreier) (hAT : KFactCaseTwoAlphaThree) :
    D1CaseTwoZZThreeIn := by
  intro G _ _ P M H R Rbar hd hnosp hin
  intros
  exact D1CaseTwoData.false_of_in_three hd hβ hS hSyl hSch hAT hnosp hin

end CFSG.AGLEmbedding
