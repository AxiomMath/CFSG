module

public import CFSG.Assembly.E6FourCentOrbit
public import CFSG.Assembly.E6FourCentTyped
public import CFSG.Assembly.E6FourCentTwist

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.E6FourCentChk
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix


theorem e6Four_table_spec {L : Type} [Field L] (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = (wordMat Tag.E6 e6TwoWord) *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    {v : Fin Tag.E6.rank → ZMod 5} (hv : E6FourIsSol v) (hv0 : v ≠ 0)
    (i : KernelComponent (rootCharHom (fun j => ζ ^ (v j).val)))
    (hle : Nat.card {w : Fin Tag.E6.rank → ZMod 5 // E6FourIsSol w ∧
      ∀ γ ∈ rationalRoots ρ (rootCharHom (fun j => ζ ^ (v j).val)) i, e6Pair w γ = 0} ≤ 5) :
    (compRank (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i) = 5 ∧
      (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i).ncard = 30 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i) = 1 ∧
      twistInner (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i)
        (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) ∨
    (compRank (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i) = 4 ∧
      (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i).ncard = 24 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i) = 1 ∧
      ¬ twistInner (componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i)
        (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) := by
  obtain ⟨c, hc, hcomp, htyped, horb⟩ := e6Four_typed_row ρ hρ ζ hζ hv hv0 i hle
  rw [hcomp] at horb ⊢
  rcases typedOK_popc htyped with hp | hp
  · obtain ⟨hr, hn⟩ := e6Four_a5_rank_card hc hp htyped
    exact Or.inl ⟨hr, hn, horb, e6Four_a5_twist hρ hc hp htyped⟩
  · obtain ⟨hr, hn⟩ := e6Four_d4_rank_card hc hp htyped
    exact Or.inr ⟨hr, hn, horb, e6Four_d4_twist hρ hc hp htyped⟩

end CFSG.Assembly

end
