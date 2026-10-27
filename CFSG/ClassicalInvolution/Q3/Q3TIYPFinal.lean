module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPRank
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutAll
public import CFSG.ClassicalInvolution.Q3.Q3TIYPMinGlue
public import CFSG.ClassicalInvolution.Q3.Q3TIYSmall
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W


theorem twinYSp2Small3_true : TwinYSp2Small3 := by
  intro h3 G _ _ _ hnab K z hR hshape T hT clsT e hP1 hO3 ι _ D hcard i t' n' hk hsmall
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact false_of_small_component3 h3 hnab hR hshape hT clsT e hP1 hO3 D i hone hk
      Q3Z.statedLieAdmissible_psp2 (Or.inl ⟨rfl, rfl⟩)
  · exact false_of_small_component3 h3 hnab hR hshape hT clsT e hP1 hO3 D i hone hk
      ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide, by decide⟩
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact false_of_small_component3 h3 hnab hR hshape hT clsT e hP1 hO3 D i hone hk
      ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide⟩ (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact false_of_minus_component3 h3 hnab hR hshape hT clsT e hP1 hO3 D i hone hk

theorem twinYType3On_sp2 (h3 : OddThreeFreeInput) : Q3TY.TwinYType3On TwinRowSp2 :=
  twinYType3On_sp2_of_small h3 twinYSp2Small3_true

end CFSG.ClassicalInvolution.Q3.Q3TIY
