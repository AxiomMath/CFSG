module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin

section Block

variable {G : Type*} [Group G]

theorem blockU_map_equiv (f : G ≃* G) (L : Subgroup G) :
    blockU (L.map f.toMonoidHom) = (blockU L).map f.toMonoidHom := by
  unfold blockU blockQ
  rw [pCoreOf_map_equiv 2 f L, Subgroup.map_commutator]

theorem map_conj_eq_of_conjJoin_eq [Finite G] {S L : Subgroup G} (h : conjJoin S L = L) {s : G}
    (hs : s ∈ S) : L.map (MulAut.conj s).toMonoidHom = L := by
  have hle : L.map (MulAut.conj s).toMonoidHom ≤ L := by
    conv_rhs => rw [← h]
    exact le_iSup (fun t : S => L.map (MulAut.conj (t : G)).toMonoidHom) ⟨s, hs⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]

theorem blockU0_eq_blockU [Finite G] {S L : Subgroup G} (h : conjJoin S L = L) :
    blockU0 S L = blockU L := by
  unfold blockU0 conjJoin
  have : ∀ t : S, (blockU L).map (MulAut.conj (t : G)).toMonoidHom = blockU L := fun t => by
    rw [← blockU_map_equiv, map_conj_eq_of_conjJoin_eq h t.2]
  simp_rw [this]
  exact iSup_const

end Block

end CFSG.QuasithinUnique.A5
