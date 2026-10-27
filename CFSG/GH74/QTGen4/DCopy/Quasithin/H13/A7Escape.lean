module

public import CFSG.Quasithin.H13.A7Escape
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB

section Escape

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7NatConfig.exists_escape_F4 (h12213 : Stmt12_2_13_F4) [CFSG.GH74.QTGen4.Finite4 G] (hyp : Hyp1223 G T L V)
    (hA7 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7))) :
    ∃ v : V, v ≠ 1 ∧ ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G) := by
  rcases h12213 G T L V hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hyp.notAlt hyp.maximal
      hyp.faithful hyp.quasisimple hyp.normalizes hyp.irrPlus with
    ⟨v, hv, hv1, hesc⟩ | ⟨n, hn, hQ, -⟩ | ⟨hQ, -⟩ | ⟨hQ, -⟩
  · exact ⟨⟨v, hv⟩, fun h => hv1 (congrArg Subtype.val h), hesc⟩
  · exact absurd hQ (not_mulEquiv_SL_of_alternating_seven hA7 hn)
  · exact absurd hQ (not_mulEquiv_SL_of_alternating_seven hA7 (Or.inl rfl))
  · exact absurd hQ (not_mulEquiv_SL_of_alternating_seven hA7 (Or.inr rfl))

end Escape

end CFSG.Quasithin.H13.A7
