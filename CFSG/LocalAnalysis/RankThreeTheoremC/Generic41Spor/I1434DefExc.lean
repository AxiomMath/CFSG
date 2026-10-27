module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434General
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.RankThree.PartOne.CTP.StrongPG2

public section

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair hasNoncommPair_adjointQuotient_G2)

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

theorem Data.false_of_four_le_pRank {K : Type} [Group K] [Finite K] {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂)
    (h4 : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup K)) : False := by
  obtain ⟨E, -, hE, hc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) (⊤ : Subgroup K)
  have h1 : 5 ^ 4 ≤ Nat.card E := hc ▸ Nat.pow_le_pow_right (by norm_num) h4
  have h2 := (card_le_of_isElemAbelian hD.rank hE)
  have : 5 ^ 4 ≤ 5 ^ 3 := h1.trans h2
  norm_num at this

theorem Data.false_of_hasNoncommPair {K : Type} [Group K] [Finite K] {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂) (h : HasNoncommPair 5 K) : False := by
  obtain ⟨a, b, -, -, hab, hP⟩ := h
  exact hab (commute_of_mem_isPGroup hD.abelian hP (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)))

theorem chevalley_five_false
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {f : ℕ}
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel K t 5 f)
    {Q : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K} (hD : I1434.Data K Q x J₁ J₂) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨-, hf, -⟩, hm⟩ := hM
  cases t
  case G2 =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := (hm : CFSG.Blueprint.UntwistedChevalleyModel K .G2 (5 ^ f))
    haveI : CharP F 5 := CFSG.SectionRank.charP_of_natCard_eq_pow hF
    exact hD.false_of_hasNoncommPair
      (hasNoncommPair_adjointQuotient_G2.map e.symm.toMonoidHom e.symm.injective)
  case F4 =>
    exact hD.false_of_four_le_pRank
      (le_trans (by omega) (CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (Or.inl rfl) hm))
  case E6 =>
    exact hD.false_of_four_le_pRank (le_trans (by omega)
      (CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inl rfl)) hm))
  case E7 =>
    exact hD.false_of_four_le_pRank (le_trans (by omega)
      (CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inl rfl))) hm))
  case E8 =>
    exact hD.false_of_four_le_pRank (le_trans (by omega)
      (CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inr rfl))) hm))
  case twistedE6 =>
    exact hD.false_of_four_le_pRank (CFSG.SectionRank.four_le_pRank_of_twistedE6Model hf hm)
  case trialityD4 =>
    exact hD.false_of_four_le_pRank (CFSG.SectionRank.four_le_pRank_of_trialityD4Model hf hm)
  all_goals exact hm.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
