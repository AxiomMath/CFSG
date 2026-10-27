module

public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG

theorem exists_pComponent_of_component {X : Type} [Group X] [Finite X]
    {Kc : Subgroup (X ⧸ pPrimeCore 2 X)} (hKc : IsComponent Kc) :
    ∃ L : Subgroup X, IsPComponent 2 L ∧ L.map (QuotientGroup.mk' (pPrimeCore 2 X)) = Kc := by
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S : Set (Subgroup X) := {J | J.IsSubnormal ∧ J.map π = Kc}
  have hne : S.Nonempty :=
    ⟨Kc.comap π, hKc.2.comap π, Subgroup.map_comap_eq_self_of_surjective hsurj Kc⟩
  obtain ⟨L, hLS, hmin⟩ := wellFounded_lt.has_min S hne
  exact ⟨L, ⟨Kc, hKc, hLS.1, hLS.2, fun J hJ hJsn hJmap => hmin J ⟨hJsn, hJmap⟩ hJ⟩, hLS.2⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
