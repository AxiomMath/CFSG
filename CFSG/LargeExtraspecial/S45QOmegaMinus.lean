module

public import CFSG.LargeExtraspecial.S45QOmega
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Module QuadraticMap Subgroup CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem isSimpleGroup_omegaGroup_of_six_le (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) : IsSimpleGroup (omegaGroup Q hQ) := by
  by_cases hT : ∃ T : Submodule (ZMod 2) V, 3 ≤ finrank (ZMod 2) T ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ hT3 hTQ
    exact isSimpleGroup_omegaGroup_of_hypPairs hQ h6 h₁₂ h₁₃ h₂₃
  push Not at hT
  have halt : (polarBilin Q).IsAlt := fun x => by
    rw [polarBilin_apply_apply]
    exact CFSG.RankThree.Literature.FSmith.polar_self_zmod2 x
  have heven := LinearMap.BilinForm.IsAlt.even_finrank halt hQ
  have h6' : finrank (ZMod 2) V = 6 := by
    by_contra hne
    obtain ⟨m, hm⟩ := heven
    obtain ⟨P₁, P₂, h₁₂, hW, hd⟩ := exists_two_hypPairs hQ (by omega)
    obtain ⟨P₃, h₁₃, h₂₃⟩ := exists_third_hypPair hW (by omega)
    obtain ⟨T, hT3, hTQ⟩ := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
    obtain ⟨x, hx, hQx⟩ := hT T (by omega)
    exact hQx (hTQ x hx)
  have hts : ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = finrank (ZMod 2) V / 2 →
      ∃ u ∈ U, Q u ≠ 0 := fun U hU => hT U (by omega)
  obtain ⟨hS, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ (Or.inr h6') hts
  rw [← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6]
  exact hS

theorem isSimpleGroup_omegaGroup_and_nonabelianSylowTwo (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) :
    IsSimpleGroup (omegaGroup Q hQ) ∧ S5.NonabelianSylowTwo (omegaGroup Q hQ) :=
  ⟨isSimpleGroup_omegaGroup_of_six_le hQ h6, nonabelianSylowTwo_omegaGroup hQ h6⟩

end CFSG.LargeExtraspecial.S45Q
