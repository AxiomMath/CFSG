module

public import CFSG.Quasithin.H13.U3S135Gen
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem hyp1223_of_F4 (h1332 : Stmt13_3_2_F4) {T L V : Subgroup G} (hH : QTH13 G T L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) : Hyp1223 G T L V := by
  obtain ⟨-, ⟨hTL, hmax, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, hfsu, -⟩ := hall V hV
  exact hyp1223_of_fsu hH hTL hmax hfsu hV

theorem exists_centralizer_not_le_F4 (h12213 : Stmt12_2_13_F4) {T L V : Subgroup G}
    (hH : QTH13 G T L) (hyp : Hyp1223 G T L V) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  rcases (stmt12_2_13_iff_F4.mp h12213) G T L V hyp with h | ⟨n, hn, -, hlie⟩ | ⟨-, hA9⟩ |
      ⟨-, hM24⟩
  · exact h
  · exfalso
    apply hH.not_excluded
    rcases hn with rfl | rfl
    · exact Or.inr (Or.inl (Or.inl hlie))
    · exact Or.inr (Or.inl (Or.inr hlie))
  · exact absurd (Or.inr (Or.inr (Or.inl hA9))) hH.not_excluded
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM24)))))) hH.not_excluded

end CFSG.Quasithin.H13.U3
