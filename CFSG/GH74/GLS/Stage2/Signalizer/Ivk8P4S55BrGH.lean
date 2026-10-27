module

public import CFSG.GH74.Generic.Sections

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74

theorem ghList_of_quotient_component {G : Type} [Group G] (hK : KGH G) {H : Subgroup G}
    (hH : H ≠ ⊤) {Q : Type} [Group Q] (π : ↥H →* Q) (hπ : Function.Surjective π)
    {K : Subgroup Q} (hq : IsQuasisimple ↥K) : GHList (↥K ⧸ center ↥K) := by
  let Kpre : Subgroup ↥H := K.comap π
  let H' : Subgroup G := Kpre.map H.subtype
  have hHle : H' ≤ H := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH' : H' ≠ ⊤ := fun h => hH (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H' := Kpre.equivMapOfInjective H.subtype H.subtype_injective
  let q : ↥Kpre →* ↥K := (π.comp Kpre.subtype).codRestrict K fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := hπ (k : Q)
    exact ⟨⟨c, show π c ∈ K by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H' →* ↥K ⧸ center ↥K :=
    ((QuotientGroup.mk' (center ↥K)).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq').comp e₁.symm.surjective
  exact Generic.ghList_of_surjection hK hH' f hf hq.2.1 hq.2.2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
