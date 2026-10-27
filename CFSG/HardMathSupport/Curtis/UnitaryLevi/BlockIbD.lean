module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbD8Inner
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.ModelPlus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeD.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

variable {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}

theorem blockIb_false_of_perfThreeCent (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (h : ∀ v : ↥Lb ⧸ Subgroup.center ↥Lb, v ^ 3 = 1 → PerfThreeCent v) : False := by
  obtain ⟨u, huP, hu3, -, -, hfree⟩ := exists_inner_three hP hD
  have hPL : Pb ≤ Lb := hP.parab.1
  set l : ↥Lb := ⟨u, hPL huP⟩ with hl
  have hv3 : (QuotientGroup.mk l : ↥Lb ⧸ Subgroup.center ↥Lb) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : l ^ 3 = 1 := Subtype.ext hu3
    rw [this]
    rfl
  obtain ⟨V, hVC, hVp, hV3⟩ := h _ hv3
  have hbot : V = ⊥ := perfect_cent_trivial_one (x := u) (l := l) (c := 1) (Subgroup.one_mem _)
    (by simp [hl]) hfree hVC hVp
  rw [hbot] at hV3
  simp at hV3

theorem exists_model_d8_of_blockIb (hP : BlockIbParab Lb Pb) (hD : BlockIbData Lb Pb D x)
    (hX : IsLieOf IdxD (↥Lb ⧸ Subgroup.center ↥Lb)) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) .POmegaPlus 4 2 1 := by
  rcases isLieOf_idxD_cases hX with hc | hr
  · exact (blockIb_false_of_centPerfectNoncyc kFactCentNoncycThree_d hP hc hD).elim
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hr
    cases d
    case D r q =>
      obtain ⟨hp2, hcard, hr45⟩ : q.p = 2 ∧ q.card = 2 ∧ (r = 4 ∨ r = 5) := hd
      have hexp : q.exponent = 1 := by
        have hpos := q.exponent_pos
        by_contra hne
        have h2 : 2 ≤ q.exponent := by omega
        have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
        rw [TauCeti.PrimePower.card_def, hp2] at hcard
        omega
      have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp2 e
      rw [hp2, hexp] at hmodel
      rcases hr45 with rfl | rfl
      · exact hmodel
      · exact (blockIb_false_of_perfThreeCent hP hD fun v hv3 =>
          perfThreeCent_of_model_pomegaPlus (by norm_num) hmodel v hv3).elim
    all_goals exact hd.elim

theorem isClassicalTwoOrG2_of_isLieOf_d {X : Type} [Group X] (h : IsLieOf IdxD X) :
    IsClassicalTwoOrG2 X := by
  obtain ⟨⟨d, hv⟩, hd, he⟩ := h
  exact Or.inl ⟨⟨d, hv⟩, isClassicalOrG2Index_of_idxD hd, he⟩

theorem blockIbRankFam_d : BlockIbRankFam (IsLieOf IdxD) := by
  intro Y _ _ Lb Pb D x hP hX hD E hEL hEP hED hEab hE9 t ht htE htF
  exact hBR_d8 hP hD (isClassicalTwoOrG2_of_isLieOf_d hX) (exists_model_d8_of_blockIb hP hD hX)
    hEL hEP hED hE9

theorem blockIbAbFam_d : BlockIbAbFam (IsLieOf IdxD) := by
  intro Y _ _ Lb Pb D x hP hX hD U hUL hUP hUD hU3
  exact hBA_d8 hP hD (isClassicalTwoOrG2_of_isLieOf_d hX) (exists_model_d8_of_blockIb hP hD hX)
    hUL hUP hUD hU3

end CFSG.HardMathSupport.Curtis.UnitaryLevi
