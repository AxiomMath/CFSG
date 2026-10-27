module

public import CFSG.RankThree.PartOne.KE.CTTorusFixed
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {L : Type} [Field L]

theorem exists_rootCharHom
    {E : Type*} [Group E] (ψ : E →* ModGL τ L)
    (hb : ∀ e, ∃ b : Fin τ.rank → Lˣ, rootDiagUnit τ b = ψ e)
    (v : Fin τ.rank → ℤ) :
    ∃ χ : E →* Lˣ, ∀ (e : E) (b : Fin τ.rank → Lˣ), rootDiagUnit τ b = ψ e →
      χ e = rootChar b v := by
  classical
  have hinj : Function.Injective (rootDiagUnitHom τ L) :=
    CFSG.LieType.Chevalley.rootDiagUnit_injective
  have hunique : ∀ (e : E) (b b' : Fin τ.rank → Lˣ), rootDiagUnit τ b = ψ e →
      rootDiagUnit τ b' = ψ e → b = b' := fun e b b' h h' => hinj (h.trans h'.symm)
  let b₀ : E → (Fin τ.rank → Lˣ) := fun e => Classical.choose (hb e)
  have hb₀ : ∀ e, rootDiagUnit τ (b₀ e) = ψ e := fun e => Classical.choose_spec (hb e)
  refine ⟨
    { toFun := fun e => rootChar (b₀ e) v
      map_one' := ?_
      map_mul' := ?_ }, ?_⟩
  · have h1 : rootDiagUnit τ (1 : Fin τ.rank → Lˣ) = ψ 1 := by
      rw [map_one]; exact rootDiagUnit_one
    have := hunique 1 (b₀ 1) 1 (hb₀ 1) h1
    simp only [this]
    exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_one v
  · intro e e'
    have hm : rootDiagUnit τ (b₀ e * b₀ e') = ψ (e * e') := by
      rw [map_mul, ← hb₀ e, ← hb₀ e']
      exact rootDiagUnit_mul _ _
    have := hunique (e * e') _ _ hm (hb₀ (e * e'))
    simp only [← this]
    exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_mul _ _ _
  · intro e b hbe
    have := hunique e b (b₀ e) hbe (hb₀ e)
    simp [this]

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
