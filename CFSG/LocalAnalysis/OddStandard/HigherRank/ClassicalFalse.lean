module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Trichotomy
public import CFSG.LocalAnalysis.OddStandard.HigherRank.ClassicalMember
public import CFSG.LocalAnalysis.OddStandard.HigherRank.FourGroup
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Pumpup
public import CFSG.LocalAnalysis.OddStandard.HigherRank.BlowUpBC
public import CFSG.LocalAnalysis.OddStandard.ChildHeHeld

public section

namespace CFSG.OddStandard.HigherRank

open Subgroup CFSG.Yardstones.M0362f3a873a3 CFSG.ComponentClassification.HarrisLit

section


theorem classicalFalse (hI : ComponentClassification.RankTwoOddLie.OddLieInputs)
    (h4 : ComponentClassification.RankTwoOddLie.TrialityD4SL2Unique)
    (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hL35 : Harris81Lemma35Step) (hS : ComponentClassification.GSThmB.Solomon2AnInput)
    (hA : BlowUpAFalse) (hD4 : TrialityD43Member) : ClassicalFalse := by
  intro G _ _ L hset hcl
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm, hfund, hne, h5or⟩ := hcl
  have hstd := hset.std.standard
  have hq : CFSG.Open.IsQuasisimple L := hstd.1
  have hmem : HasClassicalMember L := by
    by_cases h5 : 5 ≤ p ^ f
    · exact hasClassicalMember_of_lieModel hI h4 hq hp hp2 hadm hfund hne h5 hm
    · obtain rfl : t = .trialityD4 := h5or.resolve_left h5
      obtain ⟨rfl, rfl⟩ := eq_three_of_pow_lt_five hp hp2 hadm.2.1 (by omega)
      obtain rfl : n = 0 := hadm.2.2
      exact hD4 L hq hm
  obtain ⟨p', f', hfact, hp2', h5', J, u, hJ, hu⟩ := hmem
  have hp' : p'.Prime := hfact.out
  have hf' : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with rfl | h
    · simp at h5'
    · exact h
  obtain ⟨t₀, ht₀, ht₀2⟩ := CFSG.OddStandard.exists_involution_of_standard hstd
  obtain ⟨hLt, hLp⟩ := CFSG.OddStandard.isPComponent_two_of_standard hstd ht₀ ht₀2
    (even_iff_two_dvd.mp (CFSG.OddStandard.even_card_of_standard hstd))
  obtain ⟨W, hW2, hW4, htW, huW, htu, hu1, huJ, hJc, hM, hsl⟩ :=
    exists_fourGroup_of_classicalMember hGA ht₀2 hLt hLp hp2' hf' h5' hJ hu
  have hu2 : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hJ.orderOf_eq_two
  haveI : IsSimpleGroup G := hset.std.simple
  obtain ⟨K, hKc, huK, hout⟩ := exists_blowUp_of_fourGroup hL35 hset.std.nonab hset.std.kProper
    hset.notCat hp' hp2' hf' h5' hW2 hW4 hJc hM hsl huJ huW hu1 htW htu
  rcases hout with ⟨-, -, -, hZ, hL34⟩ | ⟨-, -, h5⟩ | ⟨-, -, h3⟩
  · exact hA G hset.std.simple hset.std.nonab hset.std.kProper hset.notCat hset.balanced (u : G) K
      hu2 hKc.1 ((isTwoComponentIn_iff hKc.1).1 hKc) hL34 hZ
  · exact false_of_blowUp_five hS hset.notCat hu2 hKc huK h5
  · exact false_of_blowUp_three hS hset.notCat hu2 hKc huK h3

end

end CFSG.OddStandard.HigherRank
