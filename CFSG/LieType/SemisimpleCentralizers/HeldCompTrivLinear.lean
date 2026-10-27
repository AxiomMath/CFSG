module

public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix

theorem held_linear_components_unconditional {F : Type} [Field F] [Finite F]
    {n : ℕ} (s : GL (Fin n) F) (hs : s ∈ StatedSL n F) (hord : (orderOf s : F) ≠ 0)
    (J : Subgroup (GL (Fin n) F))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) F)) ⊓ StatedSL n F)) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Finite E), 2 ≤ a ∧
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)) :=
  held_linear_components SLComponentsTrivial_holds s hs hord J hJ

end CFSG.LieType.SemisimpleCentralizers.Held

end
