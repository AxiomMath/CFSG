module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGRed
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3FGChar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieEven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieOdd

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup Assembly.LowTwoRank Equiv Equiv.Perm

theorem rowCore3_alt :
    RowCore3 (fun S => (∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∧
      ¬ LieChar 3 S) := by
  intro S _ _ _ _ hS t ht J hJC hJs htJ hJq _ _ _ _ _
  obtain ⟨⟨n, -, ⟨e⟩⟩, -⟩ := hS
  set ε : S →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom with hε
  have hinj : Function.Injective ε := Subtype.val_injective.comp e.injective
  have hsurj : ∀ q ∈ alternatingGroup (Fin n), ∃ x, ε x = q := fun q hq =>
    ⟨e.symm ⟨q, hq⟩, by simp [hε]⟩
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have ht1 : ε t ≠ 1 := fun h => by
    have h1 : t = 1 := hinj (by rw [h, map_one])
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : ε t * ε t = 1 := by rw [← map_mul, htt, map_one]
  set u : centralizer ({t} : Set S) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have huL : u ∈ J.subgroupOf (centralizer {t}) := htJ
  have hLq : IsTwoQuasisimple ↥(J.subgroupOf (centralizer {t})) :=
    isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC).symm hJq
  exact RowAlt.false_of_perfect hinj hsurj ht1 ht2 hJs hLq.1 rfl huL
    (RowAlt.jointKer_commute_of_isTwoQuasisimple hinj ht2 hLq)

section Certified


theorem rowCore3_lieOther :
    RowCore3 (fun S => (∃ r : ℕ, r ≠ 3 ∧ LieChar r S) ∧ ¬ LieChar 3 S) := by
  intro S _ _ _ hna hS t ht J hJC hJs htJ hJq L _ _ hT ⟨eLJ⟩
  obtain ⟨⟨r, hr3, hr⟩, -⟩ := hS
  by_cases hr2 : r = 2
  · subst hr2
    exact RowLie.false_of_lieChar_two hr ht hJC hJs hJq
  · obtain ⟨τ', n', f', hadm', hJr⟩ :=
      RowLie.exists_lieModel_of_lieChar_odd hna hr2 hr ht hJC hJs htJ hJq
    rcases hT with hI | ⟨τ, n, hm⟩
    · exact RowLie.false_of_inductionTypeField Nat.prime_three (by norm_num) hI eLJ hr2 hr3
        hadm' hJr
    · exact false_of_lieModel_three_of_lieModel_odd (GSThmB.OddQuot.lieModel_of_equiv eLJ hm)
        hr2 hr3 hJr

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
