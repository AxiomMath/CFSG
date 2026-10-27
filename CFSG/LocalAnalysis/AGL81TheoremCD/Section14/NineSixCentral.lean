module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStar
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStarE

import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.RankThree.PartTwo.Census.CenterThreeTransfer
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeStar

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open

@[expose] def KFactThreeFiveCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore 3 X = ⊥ →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
    ∀ K E : Subgroup X, CFSG.IsComponent K → Subgroup.center ↥K ≠ ⊥ →
      CFSG.Open.pRank 3 K ≤ 2 →
      CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 → E ≤ Subgroup.normalizer (K : Set X) →
      ¬ K ≤ CFSG.Open.rankThreeGamma 1 3 E →
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type ↥K ∨
        CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsA6Type ↥K

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G}

private lemma center_starImg_ne_bot_of_inf_ne_bot {L I : Subgroup G}
    (hL : IsKComp M H L) (hI : IsKComp M H I) (hLI : L ≠ I)
    (hcent : starImg 3 H L ⊓ starImg 3 H I ≠ ⊥) :
    Subgroup.center ↥(starImg 3 H L) ≠ ⊥ ∧
      Subgroup.center ↥(starImg 3 H I) ≠ ⊥ := by
  have hLc : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL.isPComponentIn
  have hIc : CFSG.IsComponent (starImg 3 H I) := isComponent_starImg hI.isPComponentIn
  have hne : starImg 3 H L ≠ starImg 3 H I := by
    intro hEq
    exact hLI (eq_of_starImg_eq Nat.prime_three hL.isPComponentIn hI.isPComponentIn hEq)
  have hcomm : ∀ a ∈ starImg 3 H L, ∀ b ∈ starImg 3 H I, a * b = b * a := by
    have hbot : ⁅starImg 3 H L, starImg 3 H I⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hLc hIc with h | h
      · exact absurd h hne
      · exact h
    have hle : starImg 3 H L ≤
        Subgroup.centralizer (starImg 3 H I : Set (StarGroup 3 H)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcent
  have hzL : (z : StarGroup 3 H) ∈ starImg 3 H L := z.2.1
  have hzI : (z : StarGroup 3 H) ∈ starImg 3 H I := z.2.2
  have hzne : (z : StarGroup 3 H) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzLc : (⟨(z : StarGroup 3 H), hzL⟩ : ↥(starImg 3 H L)) ∈
      Subgroup.center ↥(starImg 3 H L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y.1 y.2 (z : StarGroup 3 H) hzI)
  have hzIc : (⟨(z : StarGroup 3 H), hzI⟩ : ↥(starImg 3 H I)) ∈
      Subgroup.center ↥(starImg 3 H I) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm (z : StarGroup 3 H) hzL y.1 y.2).symm
  constructor
  · intro hbot
    rw [hbot] at hzLc
    exact hzne (congrArg Subtype.val (Subgroup.mem_bot.mp hzLc))
  · intro hbot
    rw [hbot] at hzIc
    exact hzne (congrArg Subtype.val (Subgroup.mem_bot.mp hzIc))

private lemma center_threeStar_ne_bot_of_center_starImg_ne_bot {J : Subgroup G}
    (hJ : IsPComponentIn 3 J H) (hZ : Subgroup.center ↥(starImg 3 H J) ≠ ⊥) :
    Subgroup.center (threeStar J) ≠ ⊥ := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hJ
  intro hbot
  apply hZ
  rw [← Subgroup.map_center_eq e, hbot, Subgroup.map_bot]

private lemma isSL34Star_of_isL34Type_of_center_ne_bot
    {J : Subgroup G} (hJ : IsKComp M H J)
    (h34 : IsL34Type (threeStar J)) (hZ : Subgroup.center (threeStar J) ≠ ⊥) :
    IsSL34Star J := by
  have hdvd := hJ.card_center_threeStar_dvd_three h34
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact absurd (Subgroup.eq_bot_of_card_eq (Subgroup.center (threeStar J)) h1) hZ
  · exact ⟨h34, h3⟩

private lemma kFact_image_shape (hK35c : KFactThreeFiveCentral)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hple : ¬ pLayerIn 3 H ≤ M)
    {I : Subgroup G} (hI : IsKComp M H I)
    (hIc : CFSG.IsComponent (starImg 3 H I))
    (hZI : Subgroup.center ↥(starImg 3 H I) ≠ ⊥)
    (hI2 : CFSG.Open.pRank 3 (starImg 3 H I) ≤ 2) :
    IsL34Type ↥(starImg 3 H I) ∨ IsA6Type ↥(starImg 3 H I) := by
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.openPRank_starGroup_le_three hH2 h3
  have hIM : ¬ starImg 3 H I ≤ starImg 3 H M :=
    h.starImg_not_le hI.isPComponentIn.1 (IsKComp.not_le_M hI hple)
  refine hK35c (StarGroup 3 H) hKG hO hrank (starImg 3 H I) (starImg 3 H E) hIc hZI hI2
    (h.isElemAbelian_starImg_E) (h.card_starImg_E)
    (h.starImg_E_le_normalizer hIc hIM) ?_
  exact fun hΓ => hIM (hΓ.trans (h.rankThreeGamma_starImg_E_le))

private lemma isSL34Star_or_is3A6Star_of_image_shape
    {I : Subgroup G} (hI : IsKComp M H I)
    (hshape : IsL34Type ↥(starImg 3 H I) ∨ IsA6Type ↥(starImg 3 H I))
    (hZ : Subgroup.center (threeStar I) ≠ ⊥) : IsSL34Star I ∨ Is3A6Star I := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three
    hI.isPComponentIn
  rcases hshape with h34 | h6
  · exact Or.inl (isSL34Star_of_isL34Type_of_center_ne_bot hI
      (IsL34Type.of_mulEquiv e.symm h34) hZ)
  · obtain ⟨f⟩ := h6
    let eQ := QuotientGroup.congr (Subgroup.center (threeStar I))
      (Subgroup.center ↥(starImg 3 H I)) e (Subgroup.map_center_eq e)
    have h6' : IsA6Type (threeStar I) := ⟨eQ.trans f⟩
    have hZ3 : Nat.card (Subgroup.center (threeStar I)) = 3 := by
      have hdvd :=
        CFSG.RankThree.PartTwo.Sec4.Census.CenterThreeTransfer.card_center_dvd_three_of_mulEquiv
          hI.isQuasisimple
          (CFSG.HardMathSupport.Solomon.Coordinator.i271h_center_isPGroup Nat.prime_three
            (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three))
          (eQ.trans f) (m := 40)
          (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide) (by norm_num)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (Subgroup.eq_bot_of_card_eq (Subgroup.center (threeStar I)) h1) hZ
      · exact h3
    exact Or.inr ⟨h6', hZ3⟩

theorem central_types
    (hK35c : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactThreeFiveCentral)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hple : ¬ pLayerIn 3 H ≤ M)
    {L I : Subgroup G} (hL : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.IsKComp M H L)
    (hI : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.IsKComp M H I) (hLI : L ≠ I)
    (htype : IsL34Type (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.threeStar L) ∨
      CFSG.LocalAnalysis.AGL81TheoremCD.Section14.IsA11Star L)
    (hcent : starImg 3 H L ⊓ starImg 3 H I ≠ ⊥) :
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.IsSL34Star L ∧
      (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.IsSL34Star I ∨
        CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Is3A6Star I) := by
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hLc : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL.isPComponentIn
  have hIc : CFSG.IsComponent (starImg 3 H I) := isComponent_starImg hI.isPComponentIn
  have hne : starImg 3 H L ≠ starImg 3 H I := by
    intro hEq
    exact hLI (eq_of_starImg_eq Nat.prime_three hL.isPComponentIn hI.isPComponentIn hEq)
  obtain ⟨hZLimg, hZIimg⟩ := center_starImg_ne_bot_of_inf_ne_bot hL hI hLI hcent
  have hZL : Subgroup.center (threeStar L) ≠ ⊥ :=
    center_threeStar_ne_bot_of_center_starImg_ne_bot hL.isPComponentIn hZLimg
  have hZI : Subgroup.center (threeStar I) ≠ ⊥ :=
    center_threeStar_ne_bot_of_center_starImg_ne_bot hI.isPComponentIn hZIimg
  have hI2 : CFSG.Open.pRank 3 (starImg 3 H I) ≤ 2 := by
    have hstep := pRank_add_one_le_of_ne hKG hO hLc hIc hne
    have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
      h.openPRank_starGroup_le_three hH2 h3
    omega
  have hL34 : IsL34Type (threeStar L) := by
    rcases htype with h34 | h11
    · exact h34
    · exact absurd h11.center_eq_bot hZL
  have hshape := kFact_image_shape hK35c h hH2 h3 hple hI hIc hZIimg hI2
  exact ⟨isSL34Star_of_isL34Type_of_center_ne_bot hL hL34 hZL,
    isSL34Star_or_is3A6Star_of_image_shape hI hshape hZI⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen
