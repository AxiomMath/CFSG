module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcE6Lane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T

section Fix


theorem fixedPointSubgroup_step_one {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (Ψ : Set (Fin τ.rank → ℤ)) :
    fixedPointSubgroup (iterHom S.D.step 1) (rootSpan τ L Ψ) = rootSpan τ L Ψ ⊓ S.D.model := by
  ext x
  constructor
  · rintro ⟨hx, hfix⟩
    exact ⟨hx, rootSpan_le_adjointGroup L Ψ hx, hfix⟩
  · rintro ⟨hx, -, hfix⟩
    exact ⟨hx, hfix⟩

end Fix

section Layer


theorem twoDExcFixedData_of_e6Class {τ : Tag} [hτ : M27Ok τ] [E6Sub τ] {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (haT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ)) :
    Nonempty (TwoDExcFixedData S a i
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) := by
  classical
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρ := CFSG.HardMathSupport.Dickson.Sec6.ssTw_rho_stable_e6 S haT i v hΨ
  have hw : ∀ γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ),
      w • γ ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
    rw [← hΨ]
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  rw [componentOrbitLength_eq_one hfin hρ]
  refine ⟨twoDExcFixedData_of_perfect ?_⟩
  unfold TwoDExcFixedPointsPerfect
  rw [fixedPointSubgroup_step_one, hΨ]
  exact (rootSpan_inf_model_quasisimple hτ' S hn v hw).2.1

end Layer

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
