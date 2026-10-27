module

public import CFSG.Quasithin.Background.F6SQTK
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality

public section

namespace CFSG.GroupTheory

theorem isPGL2_of_mulEquiv {A B : Type} [Group A] [Group B] {q : ℕ} (e : A ≃* B)
    (h : CFSG.Quasithin.F6.IsPGL2 q B) : CFSG.Quasithin.F6.IsPGL2 q A := by
  obtain ⟨F, hF, hFfin, hFcard, ⟨eQ⟩⟩ := h
  exact ⟨F, hF, hFfin, hFcard, ⟨e.trans eQ⟩⟩

theorem card_of_isPGL2_seven {X : Type} [Group X]
    (h : CFSG.Quasithin.F6.IsPGL2 7 X) : Nat.card X = 336 := by
  obtain ⟨F, hF, hFfin, hFcard, ⟨e⟩⟩ := h
  have hcs : Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) =
      CFSG.Open.StatedScalars (Fin 2) F := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rfl
  calc Nat.card X = Nat.card (Matrix.GeneralLinearGroup (Fin 2) F ⧸
        CFSG.Open.StatedScalars (Fin 2) F) := Nat.card_congr e.toEquiv
    _ = Nat.card (CFSG.GorensteinWalter.PGL2 F) :=
        (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcs).toEquiv).symm
    _ = 336 := by
        rw [CFSG.GorensteinWalter.pgl2_card_formula F, hFcard]
        norm_num

end CFSG.GroupTheory

end
