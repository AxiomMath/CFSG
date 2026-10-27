module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowU3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowM12
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowG23

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Rows


variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {K Q : Subgroup G}

theorem S5Hyp.false_of_rows (h : S5Hyp Φ K Q) [Q.Normal]
    (hrow : Thm3RowsG (barFam Φ Q) (⊤ : Subgroup (G ⧸ Q))) : False := by
  set e := secQuotTopEquiv' h.oddCore_quot with he
  set ρ : G →* SecQuot (⊤ : Subgroup (G ⧸ Q)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' Q) with hρdef
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hker : ρ.ker = Q := by
    rw [hρdef, MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hX : NoNormalTwo (SecQuot (⊤ : Subgroup (G ⧸ Q))) :=
    noNormalTwo_of_mulEquiv e h.noNormalTwo_quot
  rcases hrow with hrow | hrow | hrow | hrow | hrow
  · exact h.false_of_rowG23 hρ hker hrow
  · exact h.false_of_rowU3 hρ hker hX hrow
  · exact h.false_of_rowM12 hρ hker hrow
  · exact not_isL3E8_of_noNormalTwo hX hrow
  · exact not_thm3RowW_top h.oddCore_quot h.noNormalTwo_quot _ hrow

theorem s5RowsTop_proved : S5RowsTop :=
  fun _ _ _ _ _ _ _ h _ hrow => h.false_of_rows hrow

end Rows

section Step


theorem thm3RO2Lift_proved (m : ℕ) : Thm3RO2Lift m :=
  thm3RO2Lift_of_rowsTop s5RowsTop_proved m

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
