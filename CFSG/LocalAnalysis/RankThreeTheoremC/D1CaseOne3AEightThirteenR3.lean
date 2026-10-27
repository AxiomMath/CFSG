module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AEightThirteen
public import CFSG.RankThree.PartTwo.Sec20.Item2012
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJ
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111WeakCore
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81EightThirteenC (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → 3 ∈ rankThreeSigmaA G →
  ∀ (P : Sylow 3 G) (M H : Subgroup G), GLBIsMaxTwoLocal M →
    GLBWeakCore 3 (P : Subgroup G) ≤ M → GLBIsMaxTwoLocal H → H ≠ M →
    Open.pRank 3 (H ⊓ M) = 3 →
    ∀ L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H,
      ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
        ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))

@[expose] def AGL81NineTwelveLThreeFour (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → 3 ∈ rankThreeSigmaA G →
  ∀ (P : Sylow 3 G) (M H : Subgroup G), GLBIsMaxTwoLocal M →
    GLBWeakCore 3 (P : Subgroup G) ≤ M → GLBIsMaxTwoLocal H → H ≠ M →
    Open.pRank 3 (H ⊓ M) = 3 →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ → IsLinThreeFour K →
      ∃ L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H, IsLinThreeFour (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def AGL81EightThirteenCKnown : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.InCatalog G → AGL81EightThirteenC G

theorem localRank_lt_of_three_mem_sigmaA (hrank : evenRank G = 3)
    (h3 : 3 ∈ rankThreeSigmaA G) :
    ∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3 := by
  classical
  intro q hq h3q
  have h3' : 3 ∈ CFSG.Assembly.RankThreeEven.sigmaA G := h3
  rw [CFSG.RankThree.LocalRank.sigmaA_eq_of_evenRank_eq_three hrank] at h3'
  split_ifs at h3' with hT hS3
  · exact absurd h3'.2.1 (by norm_num)
  · exact absurd h3'.2.1 (by norm_num)
  · have hle :=
      CFSG.RankThree.LocalRank.localRank_le_three_of_evenRank_eq_three hrank hq (by omega)
    by_contra hge
    exact hS3 ⟨q, hq, h3q, by omega⟩

theorem theoremFourHyp_of_setting (hS : Setting G) (h3 : 3 ∈ rankThreeSigmaA G) :
    CFSG.RankThree.PartTwo.TheoremFourHyp G where
  isSimpleGroup := hS.simple
  nonabelian := hS.nonab
  kProper := hS.kProper
  charTwoType := hS.charTwo
  evenRank_eq := hS.rank
  localRank_lt := localRank_lt_of_three_mem_sigmaA hS.rank h3

theorem isMaximalTwoLocal_of_glbIsMaxTwoLocal {M : Subgroup G} (hM : GLBIsMaxTwoLocal M) :
    CFSG.IsMaximalTwoLocal M :=
  ⟨hM.1, fun H hMH hH => hMH.ne (hM.2 H hH hMH.le).symm⟩

theorem gammaZero_le_of_glbWeakCore_le {P : Sylow 3 G} {M A : Subgroup G}
    (hcore : GLBWeakCore 3 (P : Subgroup G) ≤ M) (hA : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAM : A ≤ M) : CFSG.RankThree.PartTwo.gammaZero A ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : CFSG.RankThree.PartTwo.Late.IsE27 A := ⟨hA, hA27⟩
  have hA3 : 3 ≤ Open.pRank 3 A := hE.pRank_eq.ge
  have hPrank : 3 ≤ Open.pRank 3 (P : Subgroup G) := by
    rw [CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank 3 Nat.prime_three P]
    exact hA3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three le_top)
  have hPM : (P : Subgroup G) ≤ M :=
    (CFSG.PreuniquenessRankFour.Helpers.subgroup_le_weakCore_of_rank 3 Nat.prime_three _
      hPrank).trans hcore
  obtain ⟨m, hm, hAm⟩ := exists_mem_le_smul_sylow hPM hE.isPGroup hAM
  have hcore' := glbWeakCore_smul_le Nat.prime_three hcore hm
  refine (le_of_eq (CFSG.RankThree.PartTwo.aschCore_eq_gamma_of_isMulCommutative 2 hA.1
    hA3)).trans (CFSG.RankThree.PartTwo.gamma_le_iff.mpr fun B hBA hB2 => ?_)
  have hAC : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨b, hBA hb⟩ ⟨a, ha⟩)
  have hBC : 3 ≤ Open.pRank 3 (B ⊔ (((m • P : Sylow 3 G) : Subgroup G) ⊓
      Subgroup.centralizer (B : Set G))) :=
    hA3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three
      (le_sup_of_le_right (le_inf hAm hAC)))
  refine le_trans ?_ hcore'
  unfold GLBWeakCore rankThreeAschCore
  exact le_sSup ⟨B, hBA.trans hAm, hB2, hBC, rfl⟩

theorem agl81EightThirteenC_of_rankThreeII (h2012 : CFSG.RankThree.PartTwo.Item2012)
    (h236 : CFSG.RankThree.PartTwo.Item236) (hK : AGL81EightThirteenCKnown) :
    AGL81EightThirteenC G := by
  intro hS h3 P M H hM hPM hH hne hr L hL
  by_cases hcat : CFSG.Assembly.InCatalog G
  · exact hK G hcat hS h3 P M H hM hPM hH hne hr L hL
  have hst : CFSG.RankThree.PartTwo.PartTwoStanding G :=
    { theoremFourHyp_of_setting hS h3 with not_inCatalog := hcat }
  obtain ⟨A, hAHM, hA, hA27⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (H ⊓ M)
  have hA27' : Nat.card A = 27 := by rw [hA27, hr]; norm_num
  have hHmax := isMaximalTwoLocal_of_glbIsMaxTwoLocal hH
  have hAE : A ∈ CFSG.RankThree.LocalRank.partTwoE G :=
    CFSG.RankThree.PartTwo.Late.mem_partTwoE_of_le ⟨hA, hA27'⟩ hHmax (hAHM.trans inf_le_left)
  exact h2012 G hst (h236 G hst) A M H L hAE
    ⟨isMaximalTwoLocal_of_glbIsMaxTwoLocal hM,
      gammaZero_le_of_glbWeakCore_le hPM hA hA27' (hAHM.trans inf_le_right)⟩
    ⟨hHmax, hAHM.trans inf_le_left⟩ hne hL

theorem agl81EightThirteenCKnown_of_iiModel (h433 : CFSG.RankThree.PartTwo.Item433)
    (h : ∀ (G : Type) [Group G] [Finite G], CFSG.Assembly.RankThreeEven.IIModel G →
      AGL81EightThirteenC G) : AGL81EightThirteenCKnown := by
  intro G _ _ hcat hS h3
  exact h G (h433 G (theoremFourHyp_of_setting hS h3) hcat) hS h3

theorem agl81EightThirteen_of_C (h912 : AGL81NineTwelveLThreeFour G)
    (h : AGL81EightThirteenC G) : AGL81EightThirteen G := by
  intro hS h3 P M H hM hPM hH hne hr K hK hL34
  obtain ⟨L, hL, hLL⟩ := h912 hS h3 P M H hM hPM hH hne hr K hK hL34
  exact h hS h3 P M H hM hPM hH hne hr L hL
    (KFactProofs.UPrimeExcL34.nonempty_equiv_projSL hLL)

theorem agl81EightThirteen_of_rankThreeII (h912 : AGL81NineTwelveLThreeFour G)
    (h2012 : CFSG.RankThree.PartTwo.Item2012) (h236 : CFSG.RankThree.PartTwo.Item236)
    (hK : AGL81EightThirteenCKnown) : AGL81EightThirteen G :=
  agl81EightThirteen_of_C h912 (agl81EightThirteenC_of_rankThreeII h2012 h236 hK)

end CFSG.LocalAnalysis.RankThreeTheoremC
