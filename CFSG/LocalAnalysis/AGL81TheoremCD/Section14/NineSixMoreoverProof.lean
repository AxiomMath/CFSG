module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FiveTypes
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixCentral
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixDirect
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixInner
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]
variable {M Q H E : Subgroup G}

private lemma kSub_eq_sSup (hple : ¬ pLayerIn 3 H ≤ M) :
    kSub 3 M H = sSup {Y : Subgroup G | IsPComponentIn 3 Y H ∧ ¬ Y ≤ M} := by
  unfold kSub
  rw [if_neg hple]

private lemma kSub_eq_of_forall_isPComponentIn_eq (hple : ¬ pLayerIn 3 H ≤ M)
    {L : Subgroup G} (hL : IsPComponentIn 3 L H) (hLM : ¬ L ≤ M)
    (hall : ∀ Y : Subgroup G, IsPComponentIn 3 Y H → ¬ Y ≤ M → Y = L) :
    kSub 3 M H = L := by
  rw [kSub_eq_sSup hple]
  have hset : {Y : Subgroup G | IsPComponentIn 3 Y H ∧ ¬ Y ≤ M} = {L} := by
    ext Y
    constructor
    · rintro ⟨hY, hYM⟩
      exact Set.mem_singleton_iff.mpr (hall Y hY hYM)
    · intro hY
      rw [Set.mem_singleton_iff] at hY
      subst hY
      exact ⟨hL, hLM⟩
  rw [hset, sSup_singleton]

private lemma false_of_three_isKComp (h : NineSettingGen G M 3 Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I J : Subgroup G} (hL : IsKComp M H L) (hI : IsKComp M H I) (hJ : IsKComp M H J)
    (hLI : L ≠ I) (hLJ : L ≠ J) (hIJ : I ≠ J)
    (hL2 : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H L)) : False := by
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.openPRank_starGroup_le_three hH2 h3
  have hLc : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL.isPComponentIn
  have hIc : CFSG.IsComponent (starImg 3 H I) := isComponent_starImg hI.isPComponentIn
  have hJc : CFSG.IsComponent (starImg 3 H J) := isComponent_starImg hJ.isPComponentIn
  have hLI' : starImg 3 H L ≠ starImg 3 H I := fun hEq =>
    hLI (eq_of_starImg_eq Nat.prime_three hL.isPComponentIn hI.isPComponentIn hEq)
  have hLJ' : starImg 3 H L ≠ starImg 3 H J := fun hEq =>
    hLJ (eq_of_starImg_eq Nat.prime_three hL.isPComponentIn hJ.isPComponentIn hEq)
  have hIJ' : starImg 3 H I ≠ starImg 3 H J := fun hEq =>
    hIJ (eq_of_starImg_eq Nat.prime_three hI.isPComponentIn hJ.isPComponentIn hEq)
  obtain ⟨B, hBL, hBe, hBc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) hL2
  have h4 := CFSG.LocalAnalysis.RankThreeUC.AGL81C.add_two_le_pRank_of_three_components
    Nat.prime_three hLc hIc hJc hLI' hLJ' hIJ' hBL hBe hBc
    (exists_noncentral_of_isComponent hKG hO hIc)
    (exists_noncentral_of_isComponent hKG hO hJc)
  have h4' : 2 + 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) := by
    rw [show CFSG.pRank 3 ↥(⊤ : Subgroup (StarGroup 3 H)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) from
      CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup (StarGroup 3 H))] at h4
    exact h4
  omega

private lemma false_of_isA11Star_pair (h : NineSettingGen G M 3 Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    {L I : Subgroup G} (hL : IsKComp M H L) (hI : IsKComp M H I) (hLI : L ≠ I)
    (h11 : IsA11Star L) : False := by
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.openPRank_starGroup_le_three hH2 h3
  have hLc : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL.isPComponentIn
  have hIc : CFSG.IsComponent (starImg 3 H I) := isComponent_starImg hI.isPComponentIn
  have hne : starImg 3 H I ≠ starImg 3 H L := fun hEq =>
    hLI (eq_of_starImg_eq Nat.prime_three hL.isPComponentIn hI.isPComponentIn hEq.symm)
  have hstep := pRank_add_one_le_of_ne hKG hO hIc hLc hne
  have h3L := three_le_pRank_starImg_of_isA11Star hL.isPComponentIn h11
  omega

private lemma false_of_direct_isKComp
    (h : NineSettingGen G M 3 Q H E 2)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M)
    (hple : ¬ pLayerIn 3 H ≤ M) {L I : Subgroup G} (hL : IsKComp M H L)
    (hI : IsKComp M H I) (hLI : L ≠ I) (hL34 : IsL34Type (threeStar L))
    (hbot : starImg 3 H L ⊓ starImg 3 H I = ⊥) : False := by
  have hKG : CFSG.Open.IsKGroup (StarGroup 3 H) := h.isKGroup_quotient 3
  have hO : CFSG.pPrimeCore 3 (StarGroup 3 H) = ⊥ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup Nat.prime_three
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
    h.openPRank_starGroup_le_three hH2 h3
  have hLc : CFSG.IsComponent (starImg 3 H L) := isComponent_starImg hL.isPComponentIn
  have hIc : CFSG.IsComponent (starImg 3 H I) := isComponent_starImg hI.isPComponentIn
  have hne : starImg 3 H L ≠ starImg 3 H I := fun hEq =>
    hLI (eq_of_starImg_eq Nat.prime_three hL.isPComponentIn hI.isPComponentIn hEq)
  have hIM : ¬ starImg 3 H I ≤ starImg 3 H M :=
    h.starImg_not_le hI.isPComponentIn.1 (IsKComp.not_le_M hI hple)
  have h3I : 3 ∣ Nat.card ↥(starImg 3 H I) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three hO hIc
  have hL2 : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H L) :=
    two_le_pRank_starImg_of_isL34Type hL.isPComponentIn hL34
  exact false_of_inner_direct hrank hLc hIc hne hbot h3I hL2
    (h.isElemAbelian_starImg_E) (h.card_starImg_E)
    (h.starImg_E_le_normalizer hIc hIM)
    (fun e he he1 => h.not_le_centralizer_of_mem_starImg_E hIM he he1)
    (h.exists_inner_starImg hple hL hL34)

private lemma isSL34Star_and_of_isL34Type_of_ne
    (hK35c : KFactThreeFiveCentral)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q)
    (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) (hple : ¬ pLayerIn 3 H ≤ M)
    {L I : Subgroup G} (hL : IsKComp M H L) (hI : IsKComp M H I) (hLI : L ≠ I)
    (hL34 : IsL34Type (threeStar L)) :
    IsSL34Star L ∧ (IsSL34Star I ∨ Is3A6Star I) := by
  by_cases hbot : starImg 3 H L ⊓ starImg 3 H I = ⊥
  · exact (false_of_direct_isKComp h hH2 h3 hple hL hI hLI hL34 hbot).elim
  · exact h.central_types hK35c hH2 h3 hple hL hI hLI (Or.inl hL34) hbot

theorem nineSixMoreoverGen_of_kFactThreeFiveCentral
    (hK35c : KFactThreeFiveCentral) : NineSixMoreoverGen := by
  intro G _ _ M Q H E h hH2 h3 hple L hL htype
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL2 : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H L) := by
    rcases htype with h34 | h11
    · exact two_le_pRank_starImg_of_isL34Type hL.isPComponentIn h34
    · have h3L := three_le_pRank_starImg_of_isA11Star hL.isPComponentIn h11
      omega
  by_cases hsingle : ∀ Y : Subgroup G, IsPComponentIn 3 Y H → ¬ Y ≤ M → Y = L
  · left
    exact kSub_eq_of_forall_isPComponentIn_eq hple hL.isPComponentIn
      (IsKComp.not_le_M hL hple) hsingle
  · push Not at hsingle
    obtain ⟨I, hIpi, hIM, hIL⟩ := hsingle
    have hI : IsKComp M H I := isKComp_of_isPComponentIn hIpi hIM hple
    by_cases hthird : ∃ J : Subgroup G,
        IsPComponentIn 3 J H ∧ ¬ J ≤ M ∧ J ≠ L ∧ J ≠ I
    · obtain ⟨J, hJpi, hJM, hJL, hJI⟩ := hthird
      have hJ : IsKComp M H J := isKComp_of_isPComponentIn hJpi hJM hple
      exact (false_of_three_isKComp h hH2 h3 hL hI hJ
        hIL.symm hJL.symm hJI.symm hL2).elim
    · right
      have huniq : ∀ J : Subgroup G, IsKComp M H J → J = L ∨ J = I := by
        intro J hJ
        by_contra hcon
        push Not at hcon
        exact hthird ⟨J, hJ.isPComponentIn, IsKComp.not_le_M hJ hple, hcon.1, hcon.2⟩
      have hpair : {Y : Subgroup G | IsPComponentIn 3 Y H ∧ ¬ Y ≤ M} = {L, I} := by
        ext Y
        constructor
        · rintro ⟨hYpi, hYM⟩
          by_contra hcon
          rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
          push Not at hcon
          exact hthird ⟨Y, hYpi, hYM, hcon.1, hcon.2⟩
        · intro hY
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hY
          rcases hY with hYL | hYI
          · rw [hYL]
            exact ⟨hL.isPComponentIn, IsKComp.not_le_M hL hple⟩
          · rw [hYI]
            exact ⟨hIpi, hIM⟩
      have hkSub : kSub 3 M H = L ⊔ I := by
        rw [kSub_eq_sSup hple, hpair, sSup_pair]
      have hL34 : IsL34Type (threeStar L) := by
        rcases htype with h34 | h11
        · exact h34
        · exact (false_of_isA11Star_pair h hH2 h3 hL hI hIL.symm h11).elim
      obtain ⟨hSL, hrest⟩ :=
        isSL34Star_and_of_isL34Type_of_ne hK35c h hH2 h3 hple hL hI hIL.symm hL34
      exact ⟨I, hIL, hI, hkSub, huniq, hSL, hrest⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
