module

public import CFSG.ClassicalInvolution.Uniform.U8Final
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups commutatorElement

section Shape

variable {E : Type} [Group E] [Finite E] {Φ : Set (Subgroup E)}
  {t : StatedLieTag} {k e : ℕ}


theorem twin_tag_cases3 (M : Ih8Model 3 1 Φ t k e) (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    (hne : Φ.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {A B : Subgroup (modelUniv t k 3 e Fact.out).K} (hA : A ∈ M.cls) (hB : B ∈ M.cls)
    (hAB : A ≠ B) {z : E} (hzA : IsUniqueInvolution (A.map M.ψ) z)
    (hzB : IsUniqueInvolution (B.map M.ψ) z) :
    (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4) ∨ (t = .PSU ∧ k = 4) ∨ (t = .POmegaOdd ∧ 3 ≤ k) ∨
      (t = .POmegaPlus ∧ 4 ≤ k) ∨ (t = .POmegaMinus ∧ 4 ≤ k) := by
  have hmtc := modelTwinClass_two3 M hΦ hne hG2 hD4 hA hB hAB hzA hzB
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hadm := M.admissible
  have hfund := M.isFundTag
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  cases t
  ·
    have hk3 : 3 ≤ k := by
      have h1 := hadm.2.2.1
      have h2 : k ≠ 2 := fun hk => hadm.2.2.2.2 (by simp [hk])
      omega
    obtain ⟨hk4, -⟩ := CFSG.ClassicalInvolution.RouteD.Exotic.modelTwinClass_psl hp2 hk3 le_rfl hmtc
    exact Or.inr (Or.inl ⟨rfl, hk4⟩)
  ·
    obtain ⟨hk4, -⟩ :=
      CFSG.ClassicalInvolution.RouteD.Exotic.modelTwinClass_psu hp2 hadm le_rfl hmtc
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hk4⟩))
  ·
    obtain ⟨hk2, -⟩ :=
      CFSG.ClassicalInvolution.RouteD.Exotic.modelTwinClass_psp hp2 hadm le_rfl hmtc
    exact Or.inl ⟨rfl, hk2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hadm.2.2.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hadm.2.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hadm.2.2⟩))))
  · exact absurd rfl hG2
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (excLayer3 _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (excLayer3 _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (excLayer3 _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (excLayer3 _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4
      (excLayer3 _ k (by simp) hadm) le_rfl)
  · exact absurd rfl hD4
  all_goals exact absurd hfund (by simp [IsFundTag])

end Shape

end CFSG.ClassicalInvolution.Asc77.C25J
