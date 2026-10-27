module

public import CFSG.GH74.GLS.Stage4.Q9.CFacts3b
public import CFSG.GH74.GLS.Stage4.Q9.CFacts82
public import CFSG.GH74.GLS.Stage4.Q9.Transfer

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

theorem q9_false_of_model
    {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Q9Setting G z K₁ K₂ F₁ F₂) (hθ : ModelThetaData)
    (hc : ModelCounts) : False := by
  obtain ⟨E⟩ := isoC S
  obtain ⟨hN2, hN3, hN5⟩ := E.counts S.le_centralizer₁ S.le_centralizer₂ hc
  obtain ⟨hG5, h5conj, hexp⟩ := S.sylow5
  exact q9_false_of_facts K₁ K₂ S.z_ord S.one_class S.le_centralizer₁ S.le_centralizer₂ S.normal₁
    S.normal₂ S.hK3 S.hK5 S.card_C S.card2 S.card3 hG5 h5conj hexp S.seven
    (IsoC.thetaData E hθ (inst := Fintype.ofFinite _)) hN2 hN3 hN5

end CFSG.GH74.GLS.Stage4.Q9
