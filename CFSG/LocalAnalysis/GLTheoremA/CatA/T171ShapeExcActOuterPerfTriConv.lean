module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints d4Nodes D4TrialityLayer)

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p : ℕ}

theorem excTri_perfect_of_layer (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hq : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    TwoDExcFixedPointsPerfect S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ]
  have hfix : fixedPointSubgroup (iterHom S.D.step 1) (rootSpan τ L Ψ) =
      rootSpan τ L Ψ ⊓ S.D.model := by
    refine le_antisymm ?_ ?_
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨hx.1, ?_⟩
      rw [LangDatum.model, Subgroup.mem_inf]
      exact ⟨rootSpan_le_adjointGroup L Ψ hx.1, by simpa [iterHom_succ, LangDatum.step] using hx.2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      refine ⟨hx1, ?_⟩
      rw [LangDatum.model, Subgroup.mem_inf] at hx2
      simpa [iterHom_succ, LangDatum.step] using hx2.2
  rw [TwoDExcFixedPointsPerfect, hfix]
  exact hq.1

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
