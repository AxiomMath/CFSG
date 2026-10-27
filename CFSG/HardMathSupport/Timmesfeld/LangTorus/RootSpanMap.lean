module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem FrobRootMap.map_rootSpan
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) :
    (rootSpan τ L Ψ).map D.step = rootSpan τ L (ρ '' Ψ) := by
  simp only [rootSpan, Subgroup.map_iSup]
  rw [iSup_image]
  refine iSup_congr fun γ => iSup_congr fun hγ => ?_
  exact hρ.map_rootSubgroup γ (hΨ γ hγ)

theorem FrobRootMap.map_rootSpan_iterHom
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ)
    (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) (n : ℕ) :
    (rootSpan τ L Ψ).map (iterHom D.step n) =
      rootSpan τ L ((ρ : (Fin τ.rank → ℤ) → _)^[n] '' Ψ) := by
  have hroots : ∀ k (γ : Fin τ.rank → ℤ), IsRoot τ γ →
      IsRoot τ ((ρ : (Fin τ.rank → ℤ) → _)^[k] γ) := by
    intro k
    induction k with
    | zero => intro γ hγ; exact hγ
    | succ k ih =>
        intro γ hγ
        rw [Function.iterate_succ_apply']
        exact (hρ.isRoot_iff _).2 (ih γ hγ)
  induction n with
  | zero =>
      have h0 : iterHom D.step 0 = MonoidHom.id _ := by
        ext x : 1
        exact iterHom_zero D.step x
      simp only [h0, Subgroup.map_id, Function.iterate_zero, Set.image_id]
  | succ n ih =>
      have hstep : iterHom D.step (n + 1) = D.step.comp (iterHom D.step n) := by
        ext x : 1
        exact iterHom_succ D.step n x
      rw [hstep, ← Subgroup.map_map, ih,
        hρ.map_rootSpan _ (by rintro γ ⟨δ, hδ, rfl⟩; exact hroots n δ (hΨ δ hδ))]
      congr 1
      rw [Set.image_image]
      congr 1
      funext γ
      exact (Function.iterate_succ_apply' (ρ : (Fin τ.rank → ℤ) → _) n γ).symm

end CFSG.HardMathSupport.Timmesfeld.LangTorus
