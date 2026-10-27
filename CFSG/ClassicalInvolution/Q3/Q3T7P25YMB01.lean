module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25Y01
public import CFSG.ClassicalInvolution.Asc77.AscC5OM3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem exists_frame {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
    {z' a₀ b₀ : Y} (hD : Om5Data Y Φ A A' z' a₀ b₀) :
    Nonempty (Frame (GaloisField 3 1) Y Φ A A' z') := by
  obtain ⟨D, hD1, i, hi⟩ := hD.lie
  have hsub : Subsingleton (Fin D.card) := by
    rw [hD1]
    infer_instance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top]
    have hall : ∀ l : Fin D.card, (D.hom l).range ≤ (D.hom i).range := by
      intro l
      rw [Subsingleton.elim l i]
    refine eq_top_iff.mpr ?_
    rw [← D.generate]
    exact iSup_le hall
  have hcase : D.tag i = .PSp ∧ D.rank i = 2 := by
    simp only [IsOrthTag] at hi
    rcases hi with ⟨-, ht, hn⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · exact ⟨ht, hn⟩
    all_goals omega
  have hexp : D.exp i = 1 := by
    rcases D.exp_eq i with h | ⟨hT, -⟩
    · exact h
    · rw [hcase.1] at hT
      exact absurd hT (by decide)
  obtain ⟨i₁, R, hR, hAR⟩ := D.fundamental A hD.twin.hA
  obtain ⟨i₂, R', hR', hAR'⟩ := D.fundamental A' hD.twin.hA'
  obtain rfl : i₁ = i := Subsingleton.elim _ _
  obtain rfl : i₂ = i₁ := Subsingleton.elim _ _
  have hfund : D.tag i₂ ≠ .G2 ∧ D.tag i₂ ≠ .trialityD4 := by
    rw [hcase.1]
    exact ⟨by decide, by decide⟩
  have hsingle := CFSG.ClassicalInvolution.RouteD.Gaps.fundamentalSingleClass_of_ne D i₂
    hfund.1 hfund.2
  refine frame_of_hom (by norm_num : (3 : ℕ) ≠ 2) (D.tag i₂) (D.rank i₂) (D.exp i₂) (D.admissible
      i₂) (D.hom i₂)
    (D.ker_le_center i₂) hsurj hcase.1 hcase.2 hexp hR hR' hAR hAR' hD.twin.ne hD.twin.hzA
    hD.twin.hzA' ?_ ?_
  · intro J hJ
    obtain ⟨i₃, R₃, hR₃, hJR⟩ := D.fundamental J hJ
    obtain rfl : i₃ = i₂ := Subsingleton.elim _ _
    exact ⟨R₃, hR₃, hJR⟩
  · intro R₃ hR₃
    exact D.map_mem_of_single_class (fun g L hL => hD.conj L hL g) i₂ hsingle hR₃
end Asc77.C5O.M

end

end CFSG.ClassicalInvolution.Q3.Q3T8
