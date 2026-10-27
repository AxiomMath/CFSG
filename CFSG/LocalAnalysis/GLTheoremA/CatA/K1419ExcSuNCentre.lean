module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInnerA2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
open scoped MatrixGroups

section Frame


theorem l3u3_suN_frame_ker_ne_top {τ : Tag} {L : Type} [Field L] {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ) :
    ψ.ker ≠ ⊤ := by
  intro h
  have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
  rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
  exact Units.ne_zero _ (pinnedX_injective τ L _ h1)

end Frame

section Centre


theorem l3u3_suN_exists_central_frame {τ : Tag} (hRDg : RDGlue τ) {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {a : Fin τ.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    ∃ X : SL(3, L), X ∈ Subgroup.center SL(3, L) ∧ ψ X = rootDiagUnit τ a := by
  classical
  obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ := hRDg L a hap i h6
  have ha1 : ∃ j, a j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply h1
    have : a = 1 := funext hcon
    rw [this, rootDiagUnit_one]
  obtain ⟨j0, hj0⟩ := ha1
  obtain ⟨ε, hε, hglue⟩ := hglueAll (a j0) (hap j0) hj0
  have hrel := rootDiagUnit_eq_or_inv_of_glue hε hglue
  have hz0 : z0 τ γ₁ γ₂ (a j0) ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine z0_mem_rootSpan hP ?_ ?_ ?_ ?_ (a j0) <;> rw [hΨeq] <;> simp
  have hdS : rootDiagUnit τ a ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rcases hrel with h | h
    · rw [h]
      exact hz0
    · rw [h]
      exact inv_mem hz0
  have hψS : ∀ Y : SL(3, L), ψ Y ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun Y => by
    rw [hΨ, ← hψ.range]
    exact ⟨Y, rfl⟩
  have hdS' := hdS
  rw [hΨ, ← hψ.range] at hdS'
  obtain ⟨X, hX⟩ := hdS'
  refine ⟨X, ?_, hX⟩
  refine mem_center_SL_of_commute le_rfl ψ (l3u3_suN_frame_ker_ne_top le_rfl hψ) fun Y => ?_
  rw [hX]
  exact rootDiagUnit_mul_comm_of_mem_Z a
    (Subgroup.mem_sup_right (rootSpan_mono (fun γ hγ => hγ.1) (hψS Y)))

end Centre

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
