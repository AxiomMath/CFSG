module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Statements

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.Quasithin.Asc94
open scoped Pointwise

@[expose] def Stmt5_2_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T →
      Nonempty (G ≃* ↥NativeSporadic.M23)

@[expose] def Stmt5_2_11_22_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T → M23CloseData G

theorem stmt5_2_10_of_F4
    (h : Stmt5_2_11_22_F4) : Stmt5_2_10_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hM23
  exact nonempty_mulEquiv_m23_of_m23CloseData (h G T M L V H B D L₂ n hyp hM23)

end CFSG.Quasithin.H13
