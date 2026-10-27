module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Inputs
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.GH74.E2.ComponentsShape

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

private theorem card_of_formula {S : Type} [Group S] {t : Open.StatedLieTag} {n p f m : ℕ}
    (hO : LieOrderFormulasInput) (h : LieModel S t n p f)
    (hd : lieOrderDivisor t n (p ^ f) = 1) (hm : lieOrderNumerator t n (p ^ f) = m) :
    Nat.card S = m := by
  have h1 := (hO S t n p f h.admissible h).2.1
  rwa [hd, hm, mul_one] at h1

section


theorem chevOddInChev2_holds : HypA2.ChevOddInChev2 := by
  intro S _ _ r _ hr2 hS hIn
  have hO : LieOrderFormulasInput :=
    ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨τ', n', f', hY⟩ := hS
  rcases hIn with hEven | hA | hU
  · obtain ⟨t, n, f, hadm, hX⟩ := hEven
    rcases SeitzReduction.CrossChar.crossChar_arith hadm hY.admissible hr2
        (hO S t n 2 f hadm hX).2.1 (hO S τ' n' r f' hY.admissible hY).2.1 with
      ⟨h1, h2, h3, -, -, -⟩ | ⟨h1, h2, h3, -, -, -⟩ | ⟨-, -, -, h4, h5, h6⟩
    · subst h1; subst h2; subst h3
      have hc : Nat.card S = 60 := card_of_formula hO hX (by decide) (by decide)
      exact Or.inl (by rw [hc]; decide)
    · subst h1; subst h2; subst h3
      have hc : Nat.card S = 168 := card_of_formula hO hX (by decide) (by decide)
      exact Or.inl (by rw [hc]; decide)
    · subst h4; subst h5
      obtain ⟨hp3, hg1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 h6
      subst hp3; subst hg1
      exact Or.inr (Or.inr hY)
  · exact Or.inr (Or.inl (GH74.E2.lieModel_psl_two_nine_of_alt_six hA))
  · have hc : Nat.card S = 6048 := card_of_formula hO hU (by decide) (by decide)
    exact Or.inl (by rw [hc]; decide)

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
