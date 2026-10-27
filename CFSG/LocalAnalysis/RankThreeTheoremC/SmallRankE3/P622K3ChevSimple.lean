module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple onLie ambiguousChev)

theorem isSimpleGroup_alt_five_six_eight {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8) :
    IsSimpleGroup (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl | rfl
  · exact alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  · exact alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
  · exact alternatingGroup.isSimpleGroup (α := Fin 8) (by simp)

theorem isSimpleGroup_of_isChevSimple_two {S : Type} [Group S]
    (h : IsChevSimple 2 S) : IsSimpleGroup S := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | lie d =>
      haveI : IsSimpleGroup d.Group := (CFSG.Assembly.lie_finite_simple d).2
      exact MulEquiv.isSimpleGroup (e : S ≃* d.Group)
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | alternating n _ =>
      simp only [ambiguousChev] at hi
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · haveI := isSimpleGroup_alt_five_six_eight (n := 5) (Or.inl rfl)
        exact MulEquiv.isSimpleGroup (e : S ≃* alternatingGroup (Fin 5))
      · haveI := isSimpleGroup_alt_five_six_eight (n := 6) (Or.inr (Or.inl rfl))
        exact MulEquiv.isSimpleGroup (e : S ≃* alternatingGroup (Fin 6))
      · haveI := isSimpleGroup_alt_five_six_eight (n := 8) (Or.inr (Or.inr rfl))
        exact MulEquiv.isSimpleGroup (e : S ≃* alternatingGroup (Fin 8))
    | lie d =>
      haveI : IsSimpleGroup d.Group := (CFSG.Assembly.lie_finite_simple d).2
      exact MulEquiv.isSimpleGroup (e : S ≃* d.Group)
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
