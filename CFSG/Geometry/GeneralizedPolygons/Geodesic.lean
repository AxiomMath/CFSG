module

public import CFSG.Geometry.GeneralizedPolygons.Basic
public import CFSG.Quasithin.Background.F3Geodesic
import CFSG.Quasithin.Background.GirthGeodesic

public section

namespace CFSG.Geometry.GeneralizedPolygons

open SimpleGraph

universe u

variable {V : Type u} {Γ : SimpleGraph V} {m : ℕ}

namespace IsGeneralizedPolygon

theorem uniqueGeod (hP : IsGeneralizedPolygon Γ m) : CFSG.Quasithin.UniqueGeod Γ m :=
  CFSG.Quasithin.uniqueGeod_of_le_egirth hP.connected (by
    rw [← hP.girth_eq]
    exact SimpleGraph.natCast_girth_le_egirth)

theorem isGeodesic_of_noBack (hP : IsGeneralizedPolygon Γ m) {k : ℕ} (hk : k ≤ m)
    {p : CFSG.Quasithin.GPath Γ k} (hp : p.NoBack) : p.IsGeodesic := by
  obtain ⟨c⟩ := hP.isBipartite
  let c' : Γ.Coloring Bool := Γ.recolorOfEquiv finTwoEquiv c
  have hc : ∀ a b, Γ.Adj a b → c' a ≠ c' b := fun _ _ h => c'.valid h
  exact CFSG.Quasithin.GPath.isGeodesic_of_noBack hP.connected hc hP.uniqueGeod k hk p hp

end IsGeneralizedPolygon

end CFSG.Geometry.GeneralizedPolygons

