module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6RatDefs
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoRat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TStdCovDiag
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HStdExcl

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType
  CFSG.StandardType.ExcThreeAtTwo

theorem not_smallOrd_of_ggNotExcThreeOrder {S : Type} [Group S] (I : Subgroup S)
    (h : GGNotExcThreeOrder (ggCQ I)) : ¬ SmallOrd I := by
  intro hS
  unfold SmallOrd at hS
  unfold GGNotExcThreeOrder ggCQ at h
  rcases hS with hS | hS
  · exact h.2.1 hS
  · exact h.2.2 hS

theorem e6TwoRatNotSmall_of_d4
    (hD4 : E6TwoD4NotSmall) : E6TwoRatNotSmall := by
  intro L _ _ p₀ S hq2 a hT hap h1 i hqs
  classical
  have h3L : ((3 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_three
      (ringChar_ne_of_pow_eq_one Nat.prime_three hap h1)
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · by_cases hr3 : compRank (componentRoots (rootCharHom a) i) = 3
    · exact (not_a3Shape_of_three_E6 S h3L hTp i ⟨hr3, by rw [hA.2, hr3]⟩).elim
    · exact not_smallOrd_of_ggNotExcThreeOrder _
        (typeA_ggCQ_ne_three_two S hq2 hT hap h1 i hA hr3 hqs)
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S
        Nat.prime_three h3L hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    · by_cases hr4 : compRank (componentRoots (rootCharHom a) i) = 4
      · exact hD4 L p₀ S hq2 a hT hap h1 i hr4 (by rw [hD.2, hr4]) hqs
      · have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
        have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
          rw [hD.2, Nat.mul_assoc]
          have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
          have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) :=
            le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
          omega
        by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
            ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
              (componentRoots (rootCharHom a) i)])
        · exact not_smallOrd_of_ggNotExcThreeOrder _
            (inner_big_ggCQ_ne S hq2 hT i (Or.inr (Or.inl rfl)) hinner h26)
        · exact not_smallOrd_of_ggNotExcThreeOrder _
            (outerD_ggCQ_ne S hq2 hT hap h1 i hr5 hD.2 hinner)
    · exact (false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim

end CFSG.LocalAnalysis.GLTheoremA.HStdExcl

end
