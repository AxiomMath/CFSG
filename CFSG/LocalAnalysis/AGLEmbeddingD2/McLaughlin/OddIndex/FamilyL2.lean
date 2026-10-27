module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenGroup

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer
  CFSG.BenderSuzuki.MatrixGroups CFSG.Models CFSG.Assembly.LowTwoRank

theorem not_isPSolvable_of_isLThreeTwo {K : Type} [Group K] [Finite K] {Y : Subgroup K}
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) : ¬ CFSG.HallHigman.IsPSolvable 3 ↥Y := by
  intro hsolv
  have hperf : commutator (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ :=
    Group.isPerfect_def.mp (CFSG.AGLEmbedding.TrialityTwo.Seven.isPerfect_of_isLThreeTwo hY)
  have hnc : ¬ IsMulCommutative (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    intro hc
    have hbot : commutator (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [commutator_def]
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hc.is_comm.comm g₁ g₂)
    rw [hbot] at hperf
    have h1 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      have ha : a ∈ (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) := Subgroup.mem_top a
      have hb : b ∈ (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) := Subgroup.mem_top b
      rw [← hperf] at ha hb
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    rw [isLThreeTwo_card_eq hY] at h1
    omega
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.false_of_isPSolvable_surj (N := ↥Y)
    hsolv (⊤ : Subgroup ↥Y)
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.topEquiv (G := ↥Y)).toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := ↥Y)).surjective)
    (isLThreeTwo_simple hY) hnc (isLThreeTwo_three_dvd_card hY)

section Main

set_option linter.unusedSectionVars false


theorem overgroupL32L2_proved : OvergroupL32L2 := by
  intro K _ _ d q hq hd ⟨e2⟩ _ _ _ hcyc A W Y hA hNW hYW hAY hY
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hmodel :=
    ThreeRankCls.statedClassical_of_lieModel (by omega) (lieModel_A 1 q hv e2)
  obtain ⟨-, F, instF, instFin, hF, ⟨eF⟩⟩ := hmodel
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e3 : K ≃* PSL2MatrixGroup F :=
    eF.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W := by
    intro hW
    exact not_isPSolvable_of_isLThreeTwo hY
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hW hYW)
  have htop := overgroupEqTop_of_mulEquiv e3
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.overgroupEqTop_psl2 hF hq) hcyc A W hA hNW
    hWns
  exact Or.inl htop

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
