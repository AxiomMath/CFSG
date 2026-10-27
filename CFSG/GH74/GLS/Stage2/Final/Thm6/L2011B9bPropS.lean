module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Defs
public import CFSG.GH74.Generic.Sections
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open CFSG CFSG.GH74 CFSG.GH74.GLS.Stage2.Final.Thm6.I414 CFSG.GH74.GLS.Stage2.Local.P34

theorem hasPropS_of_kgh {G : Type} [Group G] (hK : KGH G) (hSch : GHSchreier) {H : Subgroup G}
    (hH : H ≠ ⊤) : HasPropS ↥H := by
  intro S _ _ hs hn hsec
  obtain ⟨Y1, f, hf⟩ := hsec
  let H' : Subgroup G := Y1.map H.subtype
  have hH' : H' ≠ ⊤ := fun h => hH (top_le_iff.1 (h ▸ Subgroup.map_subtype_le Y1))
  let e : ↥H' ≃* ↥Y1 := (Y1.equivMapOfInjective H.subtype H.subtype_injective).symm
  let f' : ↥H' →* S := f.comp e.toMonoidHom
  have hf' : Function.Surjective f' := hf.comp e.surjective
  exact hSch S hs hn (Generic.ghList_of_surjection hK hH' f' hf' hs hn)

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
