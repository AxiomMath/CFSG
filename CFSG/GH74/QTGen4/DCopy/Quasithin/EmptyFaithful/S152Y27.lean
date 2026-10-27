module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.EmptyFaithful.S152Y02

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M : Subgroup G}

section Star

variable (h : Data T Mc M)

include h

theorem isUniqueM_of_five_F4 (h5 : StageLemma15205_F4) (hs : Setting152 T Mc M) {Y₁ : Subgroup G}
    (hY₁ : Y₁ ≤ M) (hnot : ¬ Y₁ ≤ Mc) : IsUniqueM (Y₁ ⊔ T) M := by
  refine ⟨⟨h.inM.1, sup_le hY₁ h.T_le⟩, fun M' hM' => ?_⟩
  have hT' : InM T M' := ⟨hM'.1, le_sup_right.trans hM'.2⟩
  rcases (h5 G T Mc M hs M').mp hT' with hM | hM
  · exact hM
  · exfalso
    exact hnot (by rw [← hM]; exact le_sup_left.trans hM'.2)

end Star

end S152Y

end CFSG.Quasithin
