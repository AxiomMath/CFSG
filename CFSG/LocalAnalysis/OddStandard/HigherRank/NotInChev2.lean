module

public import CFSG.Yardstones.M0362f3a873a3.Definitions
public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.OddStandard.HigherRank

open CFSG.Blueprint CFSG.Yardstones.M0362f3a873a3

section


theorem not_inChev2 {Q : Type} [Group Q] (hodd : OddLieType Q)
    (hF3 : ¬ SmallF3LieQuotient Q) (hL2 : ¬ L2OrReeLieQuotient Q)
    (hA6 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 6))) : ¬ GH74.GLS.InChev2 Q := by
  intro h
  have hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases h with hEven | hA | hU
  · obtain ⟨t, n, f, hadm, hX⟩ := hEven
    obtain ⟨t', n', p, g, hp, hp2, hadm', hY⟩ := hodd
    rcases CFSG.SeitzReduction.CrossChar.crossChar_arith hadm hadm' hp2
        (hO Q t n 2 f hadm hX).2.1 (hO Q t' n' p g hadm' hY).2.1 with
      ⟨h1, h2, h3, -, -, -⟩ | ⟨-, -, -, h4, h5, -⟩ | ⟨-, -, -, h4, h5, h6⟩
    · subst h1; subst h2; subst h3
      exact hL2 (Or.inl ⟨2, 2, hX⟩)
    · subst h4; subst h5
      exact hL2 (Or.inl ⟨p, g, hY⟩)
    · subst h4; subst h5
      obtain ⟨hp3, hg1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 h6
      subst hp3; subst hg1
      exact hF3 (Or.inr (Or.inr (Or.inl hY)))
  · exact hA6 hA
  · exact hF3 (Or.inr (Or.inl hU))

end

end CFSG.OddStandard.HigherRank
