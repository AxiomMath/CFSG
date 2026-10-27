module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.Models.PGLSimple
public import CFSG.Assembly.InCatalogConverse
public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Fi23.StarKernel
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate16005
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate9124
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti
open CFSG.TauCetiBridge CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4


theorem simple_chev_of_index {R : Type} [Group R] {d : ValidLieTypeIndex}
    (hd : d.1.characteristic = 2) (e : Nonempty (R ≃* (CFSGIndex.lie d).Group)) :
    IsSimpleGroup R ∧ IsChevSimple 2 R := by
  obtain ⟨e⟩ := e
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mpr (lie_finite_simple d).2, Or.inl ⟨.lie d, hd, ⟨e⟩⟩⟩

theorem simple_chev_of_alt {R : Type} [Group R] {n : ℕ} (hn : 5 ≤ n) (h : n = 5 ∨ n = 6 ∨ n = 8)
    (e : Nonempty (R ≃* alternatingGroup (Fin n))) : IsSimpleGroup R ∧ IsChevSimple 2 R := by
  obtain ⟨e⟩ := e
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mpr inferInstance, Or.inr ⟨.alternating n hn, ?_, ⟨e⟩⟩⟩
  rcases h with rfl | rfl | rfl <;> simp [ambiguousChev]

theorem simple_chev_of_classical {R : Type} [Group R] {t : StatedLieTag} {n f : ℕ}
    (hm : StatedClassicalModel R t n 2 f) :
    IsSimpleGroup R ∧ (IsChevSimple 2 R ∨ Nat.card R = 168) := by
  rcases classical_two_cases hm with ⟨d, hd, e⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · exact ⟨(simple_chev_of_index hd e).1, Or.inl (simple_chev_of_index hd e).2⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inl (by rw [hK]; norm_num))
    obtain ⟨h1, h2⟩ := simple_chev_of_alt (n := 5) le_rfl (Or.inl rfl) ⟨e.trans e₅⟩
    exact ⟨h1, Or.inl h2⟩
  · have hc : Nat.card R = 168 := by
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hm]
      decide
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
    exact ⟨(MulEquiv.isSimpleGroup_congr e).mpr
      (CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 3) (by norm_num)
        (Or.inl (by norm_num)) (Or.inl (by norm_num))), Or.inr hc⟩
  · obtain ⟨h1, h2⟩ := simple_chev_of_alt (n := 8) (by norm_num) (by simp)
      (CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (Or.inl ⟨by decide, hm⟩))
    exact ⟨h1, Or.inl h2⟩

theorem simple_chev_of_markedModel {lab : LargeEvenLabel} (hG : lab.tag ≠ .G2der)
    {R : Type} [Group R] (h : MarkedModel lab R) :
    IsSimpleGroup R ∧ (IsChevSimple 2 R ∨ Nat.card R = 168) := by
  obtain ⟨tag, rank, n⟩ := lab
  have hclass : ∀ {t' : StatedLieTag} {n' f' : ℕ}, LieModel R t' n' 2 f' → t' ∈ classicalTags →
      IsSimpleGroup R ∧ (IsChevSimple 2 R ∨ Nat.card R = 168) := fun hm ht =>
    simple_chev_of_classical (hm.statedClassicalModel ht)
  have hval : ∀ {d : ValidLieTypeIndex}, d.1.characteristic = 2 →
      Nonempty (R ≃* (CFSGIndex.lie d).Group) →
      IsSimpleGroup R ∧ (IsChevSimple 2 R ∨ Nat.card R = 168) := fun hd e =>
    ⟨(simple_chev_of_index hd e).1, Or.inl (simple_chev_of_index hd e).2⟩
  have hchev : ∀ {t' : StatedLieTag} {n' f' : ℕ}, LieModel R t' n' 2 f' →
      t' ∈ chevalleyExceptionalTags → IsSimpleGroup R ∧ (IsChevSimple 2 R ∨ Nat.card R = 168) :=
    fun hm ht => by
      obtain ⟨d, hd, e⟩ := index_of_chevalleyExceptional ht (hm.chevalleyExceptionalModel ht)
      exact hval hd e
  cases tag
  · exact hclass (t' := .PSL) h (by simp [classicalTags])
  · exact hclass (t' := .PSU) h (by simp [classicalTags])
  · exact hclass (t' := .PSp) h (by simp [classicalTags])
  · exact hclass (t' := .PSp) h (by simp [classicalTags])
  · by_cases hr : rank = 3
    · subst hr
      exact hclass (t' := .PSL) h (by simp [classicalTags])
    · have h' : LieModel R .POmegaPlus rank 2 n := by
        simpa [MarkedModel, markTag, markRank, markChar, markDeg, hr] using h
      exact hclass h' (by simp [classicalTags])
  · by_cases hr2 : rank = 2
    · subst hr2
      exact hclass (t' := .PSL) h (by simp [classicalTags])
    · by_cases hr3 : rank = 3
      · subst hr3
        exact hclass (t' := .PSU) h (by simp [classicalTags])
      · have h' : LieModel R .POmegaMinus rank 2 n := by
          simpa [MarkedModel, markTag, markRank, markChar, markDeg, hr2, hr3] using h
        exact hclass h' (by simp [classicalTags])
  · exact hchev (t' := .E6) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .E7) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .E8) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .F4) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .twistedE6) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .trialityD4) h (by simp [chevalleyExceptionalTags])
  · exact hchev (t' := .G2) h (by simp [chevalleyExceptionalTags])
  · obtain ⟨-, -, hS⟩ : (0 = 0) ∧ (StatedLieTag.twistedB2 = .twistedB2) ∧ SuzukiModel R 2 n := by
      rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
      · exact absurd ht (by simp [classicalTags, markTag])
      · exact absurd ht (by simp [chevalleyExceptionalTags, markTag])
      · exact absurd ht (by simp [reeTitsTags, markTag])
      · exact ⟨rfl, rfl, hS⟩
    obtain ⟨d, hd, e⟩ := index_of_suzuki hS
    exact hval hd e
  · obtain ⟨-, hR⟩ := LieModel.reeTitsModel (t := .twistedF4) h (by simp [reeTitsTags])
    obtain ⟨d, hd, e⟩ := index_of_reeTits_two (Or.inl rfl) hR
    exact hval hd e
  · obtain ⟨h1, h2⟩ := simple_chev_of_alt (n := 6) (by norm_num) (by simp)
      (LieModel.nonempty_mulEquiv_alternating_six h)
    exact ⟨h1, Or.inl h2⟩
  · exact absurd rfl hG
  · obtain ⟨-, hR⟩ := LieModel.reeTitsModel (t := .Tits) h (by simp [reeTitsTags])
    obtain ⟨d, hd, e⟩ := index_of_reeTits_two (Or.inr rfl) hR
    exact hval hd e

end FR

end CFSG.LocalAnalysis.GLTheoremA
