module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Main

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem false_of_component_fixed_by_twist (hτ : τ ≠ .G2) {a : Fin τ.rank → Lˣ}
    (hE : rootDiagUnit τ a ∈ S.E) (i : KernelComponent (rootCharHom a))
    (_hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {r f j : ℕ} [ExpChar L r] (hr : r.Prime) (hq : S.D.q = r ^ f)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ)
    (hj0 : 0 < j) (hjf : j < f) (z' : ModGL τ L)
    (hfix : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      z' * Units.map (entrywiseHom (iterateFrobenius L r j)) x * z'⁻¹ = x) : False :=
  outer_false_of_component_fixed_by_twist S hτ (S.E_le hE).1 i hr hq hq4 hj0 hjf z' hfix

end Main

section Big

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

@[expose] def HasBigInnerComponent (S : LangSetup τ L p) (D₁ : Subgroup (ModGL τ L)) : Prop :=
  ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧
    ∃ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) ∧
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])

theorem noFrobeniusInner_of_big_inner (S : LangSetup τ L p) (hτ : τ ≠ .G2)
    (hq4 : S.D.q ≠ 4 ∨ SimplyLacedTag τ)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (h : HasBigInnerComponent S D₁) :
    NoFrobeniusInner S D₁ := by
  intro r f j _ hr hqf hj0 hjf z hz
  obtain ⟨a, haD, ha1, i, hbig, hinner⟩ := h
  exact false_of_component_fixed_by_twist S hτ (hD₁E haD) i hinner hr hqf hq4 hj0 hjf z
    (fun x hx => hz x (Or.inl ⟨a, haD, ha1, i, hbig, hx⟩))

end Big

end CFSG.HardMathSupport.Timmesfeld.LangTorus
