module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixCentral
public import CFSG.RankThree.PartTwo.Sec4.Census.Open46

import CFSG.LocalAnalysis.RankThreeUC.AGL81CKStarComponent
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Sylow
import CFSG.RankThree.PartTwo.Census.CenterThreeTransfer
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
import CFSG.Adapters.LinearFieldTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

open CFSG.LocalAnalysis.AGL81TheoremCD.Section14
open CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

theorem card_center_eq_three_of_isA6Type {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hZ : IsPGroup 3 (Subgroup.center X))
    (hZne : Subgroup.center X ≠ ⊥) (h6 : IsA6Type X) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨e⟩ := h6
  have hdvd :=
    CFSG.RankThree.PartTwo.Sec4.Census.CenterThreeTransfer.card_center_dvd_three_of_mulEquiv
      hq hZ e (m := 40) (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide) (by norm_num)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq (Subgroup.center X) h) hZne
  · exact h

theorem isExtNotation_of_isA6Type {X : Type} [Group X]
    (hq : CFSG.IsQuasisimple X) (hZ3 : Nat.card (Subgroup.center X) = 3)
    (h6 : IsA6Type X) :
    IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
      (fun B _ => Nat.card B = 3) X := by
  obtain ⟨e⟩ := h6
  refine ⟨Subgroup.center X, inferInstance, hZ3, ⟨e⟩, ?_⟩
  rintro ⟨H, hH, hinf, hsup⟩
  haveI : H.Normal := hH
  have hZne : Subgroup.center X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    exact absurd hZ3 (by norm_num)
  have htop : H = ⊤ :=
    (CFSG.SectionRank.perfect_central_supplement hq.1).1 H (by rw [sup_comm]; exact hsup)
  refine hZne ?_
  rw [← inf_top_eq (Subgroup.center X), ← htop, ← hinf]

theorem isSLType_three_four_of_isL34Type
    (hSL : CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46) {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hZ : IsPGroup 3 (Subgroup.center X))
    (hZne : Subgroup.center X ≠ ⊥) (h34 : IsL34Type X) :
    IsSLType 3 (GaloisField 2 2) X := by
  have hpi : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi (X ⧸ Subgroup.center X) 2 2 := by
    obtain ⟨e⟩ := nonempty_mulEquiv_projSL_quotient_center_of_isL34Type h34
    exact Or.inl ⟨by norm_num, ⟨e⟩⟩
  have hEps : CFSG.RankThree.PartTwo.Sec4.IsSLThreeEpsAt X (2 ^ 2) :=
    hSL X hq hZ hZne 2 2 (by norm_num) (Or.inl rfl) hpi
  have hPi := CFSG.RankThree.PartTwo.KFacts.isSLThreePiAt_of_isSLThreeEpsAt (p := 2) (e := 2)
    (by norm_num) hEps (Or.inl (by norm_num)) hZne
  obtain ⟨F, hF, hFfin, hcase⟩ := hPi
  letI : Field F := hF
  letI : Finite F := hFfin
  rcases hcase with ⟨hFcard, -, ⟨φ⟩⟩ | ⟨-, hmod, -⟩
  · refine ⟨φ.trans ?_⟩
    exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.trans
      (CFSG.ClassicalModels.specialLinearFieldEquiv
        (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 2 (by norm_num) hFcard) (Fin 3))
  · norm_num at hmod

theorem nineSixThree_of_kFacts
    (hK35c : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactThreeFiveCentral)
    (hK35r : KFactThreeFiveRankOne)
    (hSL : CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46) : NineSixThree := by
  intro G _ _ M Q H E h hH2 h3 hple hq hrank
  obtain ⟨hKc, hKM⟩ := h.isComponent_kStar_of_isQuasisimple hple hq
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hrank3 : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.openPRank_starGroup_le_three hH2 h3
  have hE9 : CFSG.Open.IsElemAbelian 3 (starImg 3 H E) := h.isElemAbelian_starImg_E
  have hEcard : Nat.card (starImg 3 H E) = 9 := h.card_starImg_E
  have hEnorm : starImg 3 H E ≤
      Subgroup.normalizer (kStar 3 M H : Set (StarGroup 3 H)) :=
    h.starImg_E_le_normalizer hKc hKM
  have hnotGamma : ¬ kStar 3 M H ≤ CFSG.Open.rankThreeGamma 1 3 (starImg 3 H E) :=
    fun hle => hKM (hle.trans h.rankThreeGamma_starImg_E_le)
  have hZ3 : IsPGroup 3 (Subgroup.center ↥(kStar 3 M H)) :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree.isPGroup_center_of_isComponent hKc hO
  rcases hrank with h1 | ⟨h2, hZKne⟩
  · exact Or.inl (hK35r (StarGroup 3 H) hKG hO hrank3 (kStar 3 M H) (starImg 3 H E) hKc h1
      hE9 hEcard hEnorm hnotGamma)
  · rcases hK35c (StarGroup 3 H) hKG hO hrank3 (kStar 3 M H) (starImg 3 H E) hKc hZKne h2.le
      hE9 hEcard hEnorm hnotGamma with h34 | h6
    · exact Or.inr (Or.inr (isSLType_three_four_of_isL34Type hSL hq hZ3 hZKne h34))
    · exact Or.inr (Or.inl (isExtNotation_of_isA6Type hq
        (card_center_eq_three_of_isA6Type hq hZ3 hZKne h6) h6))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
