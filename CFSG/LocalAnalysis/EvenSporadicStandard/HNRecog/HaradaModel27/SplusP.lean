module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.NoLiftP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.SplusReduce

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.EvenSporadicStandard.HNRecog.Harada.S25

section Cert


theorem pZ_mem_R0 : pZ ∈ wordSubgroupP nWords1 := by
  have h1 := tableI1OK_true
  simp only [tableI1OK, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hN⟩, -⟩, -⟩, -⟩, hmz⟩, -⟩ := h1
  exact ((enumW_spec hN).2.memT_iff rep_elemZ).1 hmz

theorem card_R0 : Nat.card ↥(wordSubgroupP nWords1) = 2 ^ 8 := by
  have h1 := tableI1OK_true
  simp only [tableI1OK, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hN⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h1
  have h256 : Nat.card ↥(wordSubgroup nWords1) = 256 := (enumW_spec hN).1
  rw [card_wordSubgroupP, h256]
  norm_num

theorem isPGroup_R0 : IsPGroup 2 (wordSubgroupP nWords1) :=
  IsPGroup.of_card card_R0

theorem splusFact_P (hP : Nat.card ↥P1408 = 177408000) (hlift : liftOK = true) :
    SplusFact pZ := by
  haveI : Finite ↥P1408 := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨ψ, -, hker, hno⟩ := exists_noLift_pZ hP hlift
  exact splusFact_of_noLiftV4 pZ_mem_R0 isPGroup_R0 hker hno

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
