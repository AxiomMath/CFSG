module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Config
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZQ7

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration.ExcWideThree (d4F2Theta)


local instance : NeZero Tag.D4.rank := ⟨by decide⟩

theorem ofFn_four (v : Fin Tag.D4.rank → ℤ) : List.ofFn v = [v 0, v 1, v 2, v 3] := rfl

theorem d4_coords_mem {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot Tag.D4 v) :
    [v 0, v 1, v 2, v 3] ∈ d4ArtifactRoots := by
  have h := (d4_root_certificate.1 v).1 hv
  rwa [ofFn_four v] at h

theorem d4_list_two_le : ∀ l ∈ d4ArtifactRoots, l.getD 2 0 ≤ 2 := by decide

theorem d4_list_two_eq : ∀ l ∈ d4ArtifactRoots, l.getD 2 0 = 2 →
    l.getD 0 0 = 1 ∧ l.getD 1 0 = 1 ∧ l.getD 3 0 = 1 := by decide

theorem d4_list_sub : ∀ l ∈ d4ArtifactRoots, l.getD 2 0 = 1 →
    [1 - l.getD 0 0, 1 - l.getD 1 0, 2 - l.getD 2 0, 1 - l.getD 3 0] ∈ d4ArtifactRoots := by
  decide

theorem coord_two_le_of_isRoot {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot Tag.D4 v) : v 2 ≤ 2 := by
  simpa using d4_list_two_le _ (d4_coords_mem hv)

theorem eq_d4F2Theta_of_coord_two {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot Tag.D4 v) (h2 : v 2 = 2) :
    v = d4F2Theta := by
  have h := d4_list_two_eq _ (d4_coords_mem hv) (by simpa using h2)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h
  obtain ⟨h0, h1, h3⟩ := h
  have hv' : v = ![v 0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hv', h0, h1, h2, h3]
  rfl

theorem isRoot_d4F2Theta : IsRoot Tag.D4 d4F2Theta :=
  (d4_root_certificate.1 d4F2Theta).2 (by decide)

theorem height_pos_d4F2Theta : 0 < height d4F2Theta :=
  (IsRoot.height_pos_iff isRoot_d4F2Theta).2 (by
    have key : ∀ j : Fin Tag.D4.rank, 0 ≤ d4F2Theta j := by decide
    exact key)

theorem isRoot_d4F2Theta_sub {v : Fin Tag.D4.rank → ℤ} (hv : IsRoot Tag.D4 v) (h2 : v 2 = 1) :
    IsRoot Tag.D4 (d4F2Theta - v) := by
  have h := d4_list_sub _ (d4_coords_mem hv) (by simpa using h2)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h
  refine (d4_root_certificate.1 (d4F2Theta - v)).2 ?_
  have e : List.ofFn (d4F2Theta - v) = [1 - v 0, 1 - v 1, 2 - v 2, 1 - v 3] := by
    rw [ofFn_four (d4F2Theta - v)]
    rfl
  rw [e]
  exact h

theorem eq_two_of_not_mem {i : Fin Tag.D4.rank} (hi : i ∉ ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    i = 2 := by
  have key : ∀ j : Fin Tag.D4.rank, ¬(j = 0 ∨ j = 1 ∨ j = 3) → j = 2 := by decide
  exact key i (by simpa using hi)

theorem two_not_mem : (2 : Fin Tag.D4.rank) ∉ ({0, 1, 3} : Set (Fin Tag.D4.rank)) := by
  simp

theorem parabolicDegree_d4J (v : Fin Tag.D4.rank → ℤ) :
    parabolicDegree Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) v = v 2 := by
  have hcov : ∀ b : Fin Tag.D4.rank, b ≠ 2 → b = 0 ∨ b = 1 ∨ b = 3 := by decide
  unfold parabolicDegree
  rw [Finset.sum_eq_single (2 : Fin Tag.D4.rank)]
  · simp
  · intro b _ hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [if_pos (hcov b hb)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_radical_iff_d4J {α : Fin Tag.D4.rank → ℤ} :
    α ∈ parabolicRadicalRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) ↔
      IsRoot Tag.D4 α ∧ 0 < height α ∧ α 2 ≠ 0 := by
  rw [mem_parabolicRadicalRoots_iff]
  constructor
  · rintro ⟨h1, h2, i, hi, hαi⟩
    rw [eq_two_of_not_mem hi] at hαi
    exact ⟨h1, h2, hαi⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, 2, two_not_mem, h3⟩

theorem one_le_coord_two_of_mem_radical {α : Fin Tag.D4.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank))) : 1 ≤ α 2 := by
  obtain ⟨h1, h2, h3⟩ := mem_radical_iff_d4J.1 hα
  have hnn := (IsRoot.height_pos_iff h1).1 h2 2
  omega

theorem mem_radical_d4F2Theta :
    d4F2Theta ∈ parabolicRadicalRoots Tag.D4 ({0, 1, 3} : Set (Fin Tag.D4.rank)) :=
  mem_radical_iff_d4J.2 ⟨isRoot_d4F2Theta, height_pos_d4F2Theta, by simp [d4F2Theta]⟩

end CFSG.LocalAnalysis.GLTheoremA
