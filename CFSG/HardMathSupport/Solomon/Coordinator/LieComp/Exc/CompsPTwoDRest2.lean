module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMainG
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction

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

section Rest2

theorem rationalLieType_of_twoD_highG {p : ℕ} (hp : p.Prime) {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (Q : ℕ → ℕ → Prop) (hrec : CompsPTwoDRecog.TwoDChainRecogAll L Q)
    (hQ : Q (ringChar L) S.D.q) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD := by
    unfold twistKind
    rw [if_neg hout, if_neg, if_pos ⟨by omega, hn⟩]
    rintro (⟨h6, h72⟩ | ⟨h4', -, -⟩)
    · rw [hn, h6] at h72
      omega
    · omega
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | F4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | D4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | E6 =>
    exact CompsPTwoDMainG.rationalLieType_of_dClassTwistedG_E6 S hp hpL hT hTp i h5 hn hkind Q hrec
      hQ
  | E7 =>
    exact CompsPTwoDMainG.rationalLieType_of_dClassTwistedG_E7 S hp hpL hT hTp i h5 hn hkind Q hrec
      hQ
  | E8 =>
    exact CompsPTwoDMainG.rationalLieType_of_dClassTwistedG_E8 S hp hpL hT hTp i h5 hn hkind Q hrec
      hQ

@[expose] def ExcRationalLieTypesOuterDP_rest2 (p : ℕ) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1)) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      ¬ (5 ≤ compRank (componentRoots (rootCharHom a) i) ∧ (ringChar L = 2 ∨ 5 ≤ S.D.q)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excRationalLieTypesOuterDP_of_rest2 {p : ℕ} (hp : p.Prime)
    (h : ExcRationalLieTypesOuterDP_rest2 p) : ExcRationalLieTypesOuterDP p := by
  intro τ L _ _ p₀ S a hT hap h1 i hshape hout hqs
  by_cases hhigh : 5 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (ringChar L = 2 ∨ 5 ≤ S.D.q)
  · exact rationalLieType_of_twoD_highG hp S hT hap h1 i hhigh.1 hshape.2 hout
      (fun r q => r = 2 ∨ 5 ≤ q) (CompsPTwoDRecog.twoDChainRecogAll_even_or_five L) hhigh.2
  · exact h τ L p₀ S a hT hap h1 i hshape hout hhigh hqs

theorem excRationalLieTypesOuterD_of_rest2 (h : ExcRationalLieTypesOuterDP_rest2 3) :
    ExcRationalLieTypesOuterD :=
  excRationalLieTypesOuterDP_of_rest2 Nat.prime_three h

end Rest2

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
