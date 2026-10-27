module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelSuN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement


@[expose] def InnerKindSmallCompAction :
    Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀), p.Prime → p ≠ 2 →
    ∀ {a : Fin τ.rank → Lˣ}, rootDiagUnit τ a ∈ S.D.torus →
    (∀ j, a j ^ p = 1) → rootDiagUnit τ a ^ p = 1 → rootDiagUnit τ a ≠ 1 →
    (τ = .G2 → 4 ≤ S.D.q) →
    ∀ (i : KernelComponent (rootCharHom a)),
    twistKind S.ρ (rootCharHom a) i = .inner →
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360 →
    S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4 →
    ∀ {y : ModGL τ L}
      (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
      (hyF : S.D.step y = y)
      (hyStab : MulAut.conj y ∈ subgroupStabAut
        (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
            ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

@[expose] def TwoDExcFixedPointsPerfectAll :
    Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ},
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (i : KernelComponent (rootCharHom a)), TwoDOrExcRankFour S a i →
      TwoDExcFixedPointsPerfect S a i
        (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))

@[expose] def ExcHighRankCompAction :
    Prop :=
  ∀ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀), p.Prime → p ≠ 2 →
    (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ {a : Fin τ.rank → Lˣ}, rootDiagUnit τ a ∈ S.D.torus →
    (∀ j, a j ^ p = 1) → rootDiagUnit τ a ^ p = 1 → rootDiagUnit τ a ≠ 1 →
    (τ = .G2 → 4 ≤ S.D.q) →
    ∀ (i : KernelComponent (rootCharHom a)),
    twistKind S.ρ (rootCharHom a) i = .exc →
    compRank (componentRoots (rootCharHom a) i) ≠ 4 →
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360 →
    ∀ {y : ModGL τ L}
      (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
      (hyF : S.D.step y = y)
      (hyStab : MulAut.conj y ∈ subgroupStabAut
        (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
      centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
          (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
            ⟨MulAut.conj y, hyStab⟩) ∈
        innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))

theorem excKernelCompAction_of (hP : TwoDExcFixedPointsPerfectAll)
    (hInner : InnerKindSmallCompAction) (hExc : ExcHighRankCompAction) :
    ExcKernelCompAction := by
  intro τ L _ _ _ p₀ S hp₀ hp₀2 p hp hp2 hτ a hT hap hTp h1 hG2 i hQS h360 y hyZ hyF hyStab
  classical
  have hτD4 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h | h <;> simp [h]
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner =>
      by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
      · exact centerQuotientHom_mem_innAutDerived_innerKind_of_four_leT S hT i hk hQ
          hyZ hyF hyStab
      · have hQlt : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4 :=
          not_le.mp hQ
        exact hInner S hp hp2 hT hap hTp h1 hG2 i hk hQS h360 hQlt hyZ hyF hyStab
  | suN =>
      have hnot := suN_not_small_of_isQuasisimple S hp hp2 hT hTp i hk hQS
      exact centerQuotientHom_mem_innAutDerived_unitaryKind_of_elementOrder S hp hp2 hT hTp i hk
        hnot hyZ hyF hyStab
  | twoD =>
      obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
      haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
        ⟨hs0.ne'⟩
      exact centerQuotientHom_mem_innAutDerived_twoDExcRankFour S i hT (Or.inl hk) hs hmin
        (hP S hT i (Or.inl hk)) hyZ hyF hyStab
  | exc =>
      by_cases hr : compRank (componentRoots (rootCharHom a) i) = 4
      · obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
        haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
          ⟨hs0.ne'⟩
        exact centerQuotientHom_mem_innAutDerived_twoDExcRankFour S i hT (Or.inr ⟨hk, hr⟩) hs hmin
          (hP S hT i (Or.inr ⟨hk, hr⟩)) hyZ hyF hyStab
      · exact hExc S hp hp2 hτD4 hT hap hTp h1 hG2 i hk hr hQS h360 hyZ hyF hyStab

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
