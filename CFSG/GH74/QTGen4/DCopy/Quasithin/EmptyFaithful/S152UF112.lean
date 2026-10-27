module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152L08

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Input15208F112At_F4 (X Y : Type) [Group X] [Group Y] : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ Y₁ : Subgroup G, IsY1 T Mc M Y₁ →
      Nonempty (OTwoQuot H ≃* X) → Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* Y) → False

theorem input15208F112_of_cases_F4 (h15206 : StageLemma15206_F4)
    (h33 : Input15208F112At_F4 (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)))
    (h3d : Input15208F112At_F4 (Equiv.Perm (Fin 3)) (DihedralGroup 5))
    (h3s : Input15208F112At_F4 (Equiv.Perm (Fin 3)) ↥(CFSG.Open.Sz 0))
    (h53 : Input15208F112At_F4 (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3)))
    (h5d : Input15208F112At_F4 (Equiv.Perm (Fin 5)) (DihedralGroup 5))
    (h5s : Input15208F112At_F4 (Equiv.Perm (Fin 5)) ↥(CFSG.Open.Sz 0)) : Input15208F112_F4 := by
  intro G _ _ T Mc M hs H hH
  obtain ⟨Y₁, hY₁⟩ := h15206 G T Mc M hs
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases hY₁.quot with q | q | q
    · exact h33 G T Mc M hs H hH Y₁ hY₁ h q
    · exact h3d G T Mc M hs H hH Y₁ hY₁ h q
    · exact h3s G T Mc M hs H hH Y₁ hY₁ h q
  · rcases hY₁.quot with q | q | q
    · exact h53 G T Mc M hs H hH Y₁ hY₁ h q
    · exact h5d G T Mc M hs H hH Y₁ hY₁ h q
    · exact h5s G T Mc M hs H hH Y₁ hY₁ h q

end CFSG.Quasithin
