module

public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves
public import CFSG.GH74.QTGen4.Recog.G23.P7.HModel
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFactsModel
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HFactsMap

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData HFactsAux

theorem leafHFacts :
    LeafHFacts := by
  intro G _ _ H H₁ H₂ e hH hL
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_Hc hH hL
  let ι : ↥Hc →* G := H.subtype.comp φ.symm.toMonoidHom
  have hι : Function.Injective ι := H.subtype_injective.comp φ.symm.injective
  have hlet : ∀ i : Fin 5, ι (gA i) = e i.castSucc := by
    intro i
    have h1 : φ ⟨e i.castSucc, hL.mem_castSucc i⟩ = gA i := by
      apply Subtype.ext
      rw [hφ i]
      exact hf_f5_eq i
    show ((φ.symm (gA i) : H) : G) = e i.castSucc
    rw [← h1, MulEquiv.symm_apply_apply]
  have hrange : ι.range = H := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (φ.symm y).2
    · intro hx
      refine ⟨φ ⟨x, hx⟩, ?_⟩
      show ((φ.symm (φ ⟨x, hx⟩) : H) : G) = x
      rw [MulEquiv.symm_apply_apply]
  have hpair : ∀ a b : ↥Hc, Subgroup.map ι (clsub [a, b]) = Subgroup.closure {ι a, ι b} := by
    intro a b
    rw [clsub, MonoidHom.map_closure]
    congr 1
    ext x
    simp [eq_comm]
  have hH₁ : H₁ = (clsub sH1).map ι := by
    rw [sH1, hpair, hlet 0, hlet 1]
    exact hL.gen₁.symm
  have hH₂ : H₂ = (clsub sH2).map ι := by
    rw [sH2, hpair, hlet 2, hlet 3]
    exact hL.gen₂.symm
  exact HFacts.of_map hι (a := aX) (H₁X := clsub sH1) (H₂X := clsub sH2)
    (hlet 0).symm (hlet 1).symm (hlet 2).symm (hlet 4).symm hrange.symm hH₁ hH₂ hfacts_model

end CFSG.GH74.QTGen4.Recog.G23.P7
