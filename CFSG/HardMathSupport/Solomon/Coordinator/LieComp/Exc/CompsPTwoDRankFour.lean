module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDRest2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section RankFour


@[expose] def ExcRationalLieTypesOuterD_rank4 : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1)) →
      compRank (componentRoots (rootCharHom a) i) = 4 →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excRationalLieTypesOuterD_of_rank4 (h : ExcRationalLieTypesOuterD_rank4) :
    ExcRationalLieTypesOuterD := by
  refine excRationalLieTypesOuterD_of_rest2 ?_
  intro τ L _ _ p₀ S a hT hap h1 i hshape hout hnhigh hqs
  refine h τ L p₀ S a hT hap h1 i hshape ?_ hout hqs
  by_contra hne
  have h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
  have hl3 : ringChar L ≠ 3 := ringChar_ne_of_pow_eq_one Nat.prime_three hap h1
  have hnq : ¬ (ringChar L = 2 ∨ 5 ≤ S.D.q) := fun hq => hnhigh ⟨h5, hq⟩
  obtain ⟨r, e, hr, hchar, he, hq⟩ := LangSetup.exists_char_pow S
  have hrc : ringChar L = r := ringChar.eq L r
  apply hnq
  by_cases h2 : r = 2
  · exact Or.inl (hrc.trans h2)
  · right
    have h3 : r ≠ 3 := fun h => hl3 (hrc.trans h)
    have h4 : r ≠ 4 := by
      rintro rfl
      exact absurd hr (by norm_num)
    have hr5 : 5 ≤ r := by
      have := hr.two_le
      omega
    rw [hq]
    exact hr5.trans (Nat.le_self_pow (Nat.ne_of_gt he) r)

end RankFour

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
