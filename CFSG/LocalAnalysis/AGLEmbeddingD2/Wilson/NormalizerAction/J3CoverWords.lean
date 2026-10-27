module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3GammaWords

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.CosetTable CFSG.Quasithin.C48Cover

theorem phi_mk_eq_evalW {X : Type*} [Group X] {ws : List (List (Fin 6 × Bool))}
    (φ : PG 6 ws →* X) (k : Fin 6 → X) (hφ : ∀ i, φ (PresentedGroup.of i) = k i)
    (u : List (Fin 6 × Bool)) :
    φ (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u)) =
      evalW k u := by
  have h : φ.comp (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ ws.map FreeGroup.mk}) =
      FreeGroup.lift k :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply]
      exact hφ i
  have := congrArg (fun f => f (FreeGroup.mk u)) h
  simp only [MonoidHom.comp_apply] at this
  rw [this, lift_mk_eq_evalW]

theorem eq_ne_of_gammaWordFacts (hchk : GammaWordFacts)
    {X : Type*} [Group X] (k : Fin 6 → X) (φ : PG 6 j3GammaWords →* X)
    (hinj : Function.Injective φ) (hφ : ∀ i, φ (PresentedGroup.of i) = k i) :
    (∀ u ∈ eqWords, evalW k u = 1) ∧ (∀ u ∈ moveWords, evalW k u ≠ 1) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h2 := phi_mk_eq_evalW φ k hφ u
    rw [hchk.1 u hu, map_one] at h2
    exact h2.symm
  · intro h1
    have h2 := phi_mk_eq_evalW φ k hφ u
    rw [h1] at h2
    exact hchk.2 u hu (hinj (by rw [h2, map_one]))

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
