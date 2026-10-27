module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.ComponentClassification.Foote1978.ClassicalInvolution
public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch
public import CFSG.StandardComponent.AschbacherSeitz.L3NF
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutPowerMap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdOrder
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

theorem isCyclic_sylow_centralizer_of_l34_field

    {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (hnonab : ∃ g h : G, g * h ≠ h * g)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hnonU : ¬ CFSG.ComponentClassification.OutcomeLocal.UOutcome G)
    (A : Subgroup G)
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup A)
    (n : ℕ) (hn : 4 ≤ n)
    (hmodel : CFSG.Blueprint.LieModel (A ⧸ Subgroup.center A) .PSL 3 2 n)
    (S : Sylow 2 (Subgroup.centralizer (A : Set G))) :
    IsCyclic ↥S := by
  have : IsSimpleGroup G := hsimple
  have hSstd : CFSG.Open.standardComponentIsStandard A :=
    CFSG.StandardSubgroupAPI.standardComponentIsStandard_iff_assembly.mpr hstd
  have hsetting : CFSG.OddStandard.StandardSetting G A :=
    ⟨hsimple, hnonab, hK, hSstd⟩
  have hQ : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot A) .PSL 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
  rcases CFSG.ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hstd S with hrank | ⟨hcyc, -⟩ | ⟨r, hr, hquat, -, -⟩
  ·
    have hNF : CFSG.ComponentClassification.RankTwoStandard.RankTwoHypNF G A :=
      (CFSG.OddStandard.GlueL34.rankTwoHyp hsetting hrank).toNF
    have hO : CFSG.Open.standardComponentOddCore G = ⊥ :=
      CFSG.OddStandard.GlueL34.oddCore_eq_bot hsetting
    exact (CFSG.StandardComponent.AschbacherSeitz.l3_part_one_of_foundationNF
      CFSG.ComponentClassification.RankTwoFoundation.section3Config
      CFSG.ComponentClassification.RankTwoFoundation.lemma32
      CFSG.ComponentClassification.RankTwoFoundation.asc75Theorem4
      G A hNF n (by omega) hQ hO).elim
  · exact hcyc
  ·
    have hdvd : Nat.card (A ⧸ Subgroup.center A) ∣ Nat.card G :=
      CFSG.OddStandard.GlueL34.card_quotient_center_dvd A
    have h4096A : 4096 ∣ Nat.card (A ⧸ Subgroup.center A) := by
      have hval : padicValNat 2 (Nat.card (A ⧸ Subgroup.center A)) = 3 * n :=
        CFSG.ComponentClassification.GrSLit.L34Sec5S.padicValNat_card_of_lieModel_psl_three
          (by omega) hmodel
      have hle : 12 ≤ padicValNat 2 (Nat.card (A ⧸ Subgroup.center A)) := by
        rw [hval]
        omega
      have h :=
        (padicValNat_dvd_iff_le (p := 2) (a := Nat.card (A ⧸ Subgroup.center A))
          (n := 12) Nat.card_pos.ne').mpr hle
      simpa using h
    have hCIT :
        CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels :=
      CFSG.ComponentClassification.FooteLit.classicalInvolutionInput_holds
    rcases CFSG.ComponentClassification.StandardRecognition.quaternion_standard_recognition
      hCIT hnonab hstd S hr hquat with hlie | hM11 | hM12
    · exact absurd (CFSG.ComponentClassification.GSLit.uOutcome_of_oddLieType hlie) hnonU
    · obtain ⟨eM⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M11) := hM11
      have hG : Nat.card G = 7920 :=
        (Nat.card_congr eM.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11
      have h4096G : 4096 ∣ Nat.card G := h4096A.trans hdvd
      rw [hG] at h4096G
      norm_num at h4096G
    · obtain ⟨eM⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M12) := hM12
      have hG : Nat.card G = 95040 :=
        (Nat.card_congr eM.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12
      have h4096G : 4096 ∣ Nat.card G := h4096A.trans hdvd
      rw [hG] at h4096G
      norm_num at h4096G


theorem exists_ordinary_cover_of_l34_field

    {G : Type} [Group G] [Finite G]
    (hbase : CFSG.ComponentClassification.GrSLit.L34BaseSetting G)
    (A : Subgroup G)
    (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup A)
    (n : ℕ) (hn : 4 ≤ n)
    (hmodel : CFSG.Blueprint.LieModel (A ⧸ Subgroup.center A) .PSL 3 2 n) :
    Odd (Nat.card (Subgroup.center A)) ∧
    (∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧
      ∃ (e : (A ⧸ Subgroup.center A) ≃*
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
        (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A),
        Function.Surjective φ ∧
        (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F := by
  have hSstd : CFSG.Open.standardComponentIsStandard A :=
    CFSG.StandardSubgroupAPI.standardComponentIsStandard_iff_assembly.mpr hstd
  have hperf : commutator A = ⊤ := hSstd.1.1
  have hQ : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (A ⧸ Subgroup.center A) .PSL 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
  have hodd : Odd (Nat.card (Subgroup.center A)) :=
    CFSG.ComponentClassification.RankTwoL3Even.odd_card_center_of_psl3
      hperf (by omega) hQ
  have hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S :=
    isCyclic_sylow_centralizer_of_l34_field hbase.1 hbase.2.1 hbase.2.2.1
      hbase.2.2.2.2.1 A hstd n hn hmodel
  obtain ⟨K, hKf, hKfin, hKchar, -, α, hcardK, hαsurj, hαker, hαcenter⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_cover_of_odd_center hSstd.1 hmodel hodd
  let : Field K := hKf
  let : Finite K := hKfin
  let : CharP K 2 := hKchar
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) := hperfSL
  let beta :=
    CFSG.SeitzReduction.F4Pilot.centerQuotientEquivOfSurjective α hαsurj
      (hαker.trans (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K).le)
  let sigma := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K).symm
  let e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    beta.symm.trans sigma
  refine ⟨hodd, hcyc, K, hKf, hKfin, hKchar, hcardK, e, α, hαsurj, ?_⟩
  ext g
  change e (QuotientGroup.mk' (Subgroup.center A) (α g)) =
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K g
  change sigma (beta.symm (QuotientGroup.mk' (Subgroup.center A) (α g))) =
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K g
  have hbeta : beta
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) g) =
      QuotientGroup.mk' (Subgroup.center A) (α g) :=
    CFSG.SeitzReduction.F4Pilot.centerQuotientEquivOfSurjective_mk α hαsurj
      (hαker.trans (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K).le) g
  rw [← hbeta, MulEquiv.symm_apply_apply]
  rfl


end CFSG.ComponentClassification.GS79bSec5
