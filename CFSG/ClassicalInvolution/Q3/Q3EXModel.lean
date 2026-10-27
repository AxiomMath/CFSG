module

public import CFSG.ClassicalInvolution.Q3.Q3EXDef
public import CFSG.ClassicalInvolution.Q3.Q3EXOrth
public import CFSG.ClassicalInvolution.Uniform.U8Final

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic


theorem mfTwin3 : MFTwin3 := by
  intro t n a hfund hG2 hD4 hadm hnA1 ha h
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have tab : ∀ {a' : ℕ} {t' : StatedLieTag} {n' : ℕ},
      (CoreAssembly.ShapeTwinD a' t' n' ∨ CoreAssembly.ShapeTwinSL4 a' t' n' ∨
        CoreAssembly.ShapeTwinB a' t' n' ∨ CoreAssembly.ShapeTwinSp2 a' t' n' ∨
        CoreAssembly.ShapeTwinTD a' t' n' ∨ CoreAssembly.ShapeTwinSU4 a' t' n') →
        CoreAssembly.ShapeTable a' t' n' := by
    intro a' t' n' h'
    unfold CoreAssembly.ShapeTable
    tauto
  cases t
  ·
    have hn3 : 3 ≤ n := by
      have h1 := hadm.2.2.1
      have h2 : n ≠ 2 := fun hn => hnA1 ⟨rfl, hn⟩
      omega
    obtain ⟨hn4, ha2⟩ := modelTwinClass_psl hp2 hn3 ha h
    exact Or.inl (tab (Or.inr (Or.inl ⟨ha2, rfl, hn4⟩)))
  ·
    obtain ⟨hn4, ha2⟩ := modelTwinClass_psu hp2 hadm ha h
    exact Or.inl (tab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha2, rfl, hn4⟩))))))
  ·
    obtain ⟨hn2, ha2⟩ := modelTwinClass_psp hp2 hadm ha h
    exact Or.inl (tab (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha2, rfl, hn2⟩)))))
  ·
    have ha2 := modelTwinClass_odd3 hadm ha h
    exact Or.inl (tab (Or.inr (Or.inr (Or.inl ⟨ha2, rfl, hadm.2.2.1⟩))))
  ·
    rcases modelTwinClass_plus3 hadm h with h2 | ⟨hn4, ha4⟩
    · have ha2 : a = 2 := by omega
      exact Or.inl (tab (Or.inl ⟨ha2, rfl, hadm.2.2⟩))
    · exact Or.inr ⟨rfl, hn4, ha4⟩
  ·
    have ha2 := modelTwinClass_minus3 hadm ha h
    exact Or.inl (tab (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha2, rfl, hadm.2.2⟩))))))
  · exact absurd rfl hG2
  · exact absurd h (Uniform.noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (Uniform.excLayer3 _ n (by simp) hadm) ha)
  · exact absurd h (Uniform.noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (Uniform.excLayer3 _ n (by simp) hadm) ha)
  · exact absurd h (Uniform.noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (Uniform.excLayer3 _ n (by simp) hadm) ha)
  · exact absurd h (Uniform.noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (Uniform.excLayer3 _ n (by simp) hadm) ha)
  · exact absurd h (Uniform.noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (Uniform.excLayer3 _ n (by simp) hadm) ha)
  · exact absurd rfl hD4
  all_goals exact absurd hfund (by simp [IsFundTag])

end CFSG.ClassicalInvolution.Q3.Q3W.EX
