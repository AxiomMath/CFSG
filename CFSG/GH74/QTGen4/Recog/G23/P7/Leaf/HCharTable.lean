module

public import CFSG.GH74.QTGen4.Recog.G23.P7.HModel
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableC
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.HCharTableModel

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
  CFSG.GH74.QTGen4.Recog.G23.HFactsData CFSG.GH74.QTGen4.Recog.G23.HCharData HChar

theorem leafHCharTable :
    LeafHCharTable := by
  intro G _ _ H H₁ H₂ e hH hL
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_Hc hH hL
  have hlet : ∀ i : Fin 5, φ ⟨e i.castSucc, hL.mem_castSucc i⟩ = gA i := by
    intro i
    apply Subtype.ext
    rw [hφ i]
    exact hc_f5_eq i
  have h0 : e 0 ∈ H := hL.mem_castSucc 0
  have h1 : e 1 ∈ H := hL.mem_castSucc 1
  have hz : zOf e ∈ H := H.pow_mem (H.mul_mem h0 h1) 2
  have hzφ : φ ⟨zOf e, hz⟩ = zA := by
    have e1 : (⟨zOf e, hz⟩ : ↥H) = (⟨e 0, h0⟩ * ⟨e 1, h1⟩) ^ 2 := rfl
    rw [e1, map_pow, map_mul]
    have a0 := hlet 0
    have a1 := hlet 1
    exact congrArg (fun w => w ^ 2) (congrArg₂ (· * ·) a0 a1)
  have hT := TabHyp.of_mulEquiv φ tabHyp_Hc
  have hzφ' : φ.symm zA = ⟨zOf e, hz⟩ := by rw [← hzφ, MulEquiv.symm_apply_apply]
  rw [hzφ'] at hT
  exact hcharProps_of_tabHyp H (zOf e) hz _ hT

end CFSG.GH74.QTGen4.Recog.G23.P7
