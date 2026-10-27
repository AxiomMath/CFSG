module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem forall_mem_add_F4 : ∀ l ∈ Tag.F4.artifactRoots,
    (∀ k : Fin 4, 0 ≤ l.getD k 0) → l ≠ [2, 3, 4, 2] →
    ∃ j : Fin 4, List.ofFn (fun k : Fin 4 => l.getD k 0 + if k = j then (1 : ℤ) else 0) ∈
      Tag.F4.artifactRoots := by
  decide +kernel

private theorem forall_mem_sub_F4 : ∀ l ∈ Tag.F4.artifactRoots,
    (∀ k : Fin 4, 0 ≤ l.getD k 0) →
    (∀ j : Fin 4, l ≠ List.ofFn (Pi.single j (1 : ℤ))) →
    ∃ j : Fin 4, List.ofFn (fun k : Fin 4 => l.getD k 0 - if k = j then (1 : ℤ) else 0) ∈
      Tag.F4.artifactRoots ∧
      ∀ k : Fin 4, 0 ≤ l.getD k 0 - if k = j then (1 : ℤ) else 0 := by
  decide +kernel

private theorem forall_mem_add_E6 : ∀ l ∈ Tag.E6.artifactRoots,
    (∀ k : Fin 6, 0 ≤ l.getD k 0) → l ≠ [1, 2, 2, 3, 2, 1] →
    ∃ j : Fin 6, List.ofFn (fun k : Fin 6 => l.getD k 0 + if k = j then (1 : ℤ) else 0) ∈
      Tag.E6.artifactRoots := by
  decide +kernel

private theorem forall_mem_sub_E6 : ∀ l ∈ Tag.E6.artifactRoots,
    (∀ k : Fin 6, 0 ≤ l.getD k 0) →
    (∀ j : Fin 6, l ≠ List.ofFn (Pi.single j (1 : ℤ))) →
    ∃ j : Fin 6, List.ofFn (fun k : Fin 6 => l.getD k 0 - if k = j then (1 : ℤ) else 0) ∈
      Tag.E6.artifactRoots ∧
      ∀ k : Fin 6, 0 ≤ l.getD k 0 - if k = j then (1 : ℤ) else 0 := by
  decide +kernel

private theorem forall_mem_add_E7 : ∀ l ∈ Tag.E7.artifactRoots,
    (∀ k : Fin 7, 0 ≤ l.getD k 0) → l ≠ [2, 2, 3, 4, 3, 2, 1] →
    ∃ j : Fin 7, List.ofFn (fun k : Fin 7 => l.getD k 0 + if k = j then (1 : ℤ) else 0) ∈
      Tag.E7.artifactRoots := by
  decide +kernel

private theorem forall_mem_sub_E7 : ∀ l ∈ Tag.E7.artifactRoots,
    (∀ k : Fin 7, 0 ≤ l.getD k 0) →
    (∀ j : Fin 7, l ≠ List.ofFn (Pi.single j (1 : ℤ))) →
    ∃ j : Fin 7, List.ofFn (fun k : Fin 7 => l.getD k 0 - if k = j then (1 : ℤ) else 0) ∈
      Tag.E7.artifactRoots ∧
      ∀ k : Fin 7, 0 ≤ l.getD k 0 - if k = j then (1 : ℤ) else 0 := by
  decide +kernel

private theorem forall_mem_add_E8 : ∀ l ∈ Tag.E8.artifactRoots,
    (∀ k : Fin 8, 0 ≤ l.getD k 0) → l ≠ [2, 3, 4, 6, 5, 4, 3, 2] →
    ∃ j : Fin 8, List.ofFn (fun k : Fin 8 => l.getD k 0 + if k = j then (1 : ℤ) else 0) ∈
      Tag.E8.artifactRoots := by
  decide +kernel

private theorem forall_mem_sub_E8 : ∀ l ∈ Tag.E8.artifactRoots,
    (∀ k : Fin 8, 0 ≤ l.getD k 0) →
    (∀ j : Fin 8, l ≠ List.ofFn (Pi.single j (1 : ℤ))) →
    ∃ j : Fin 8, List.ofFn (fun k : Fin 8 => l.getD k 0 - if k = j then (1 : ℤ) else 0) ∈
      Tag.E8.artifactRoots ∧
      ∀ k : Fin 8, 0 ≤ l.getD k 0 - if k = j then (1 : ℤ) else 0 := by
  decide +kernel


private theorem exists_isRoot_add_single_of_forall_list {τ : Tag} {θ : Fin τ.rank → ℤ}
    (hlist : ∀ l ∈ τ.artifactRoots, (∀ k : Fin τ.rank, 0 ≤ l.getD k 0) →
      l ≠ List.ofFn θ →
      ∃ j : Fin τ.rank, List.ofFn (fun k : Fin τ.rank =>
        l.getD k 0 + if k = j then (1 : ℤ) else 0) ∈ τ.artifactRoots) :
    ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → γ ≠ θ →
      ∃ j, IsRoot τ (γ + Pi.single j 1) := by
  intro γ hγ hγ0 hγθ
  have hget : ∀ k : Fin τ.rank, (List.ofFn γ).getD k 0 = γ k := fun k => by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  obtain ⟨j, hj⟩ := hlist (List.ofFn γ) (isRoot_iff_mem_artifactRoots.1 hγ)
    (fun k => by rw [hget k]; exact hγ0 k) (fun h => hγθ (List.ofFn_injective h))
  refine ⟨j, isRoot_iff_mem_artifactRoots.2 ?_⟩
  have hfun : (fun k : Fin τ.rank => (List.ofFn γ).getD k 0 + if k = j then (1 : ℤ) else 0)
      = γ + Pi.single j 1 := by
    funext k
    rw [Pi.add_apply, Pi.single_apply, hget k]
  rwa [hfun] at hj

private theorem exists_isRoot_sub_single_of_forall_list {τ : Tag}
    (hlist : ∀ l ∈ τ.artifactRoots, (∀ k : Fin τ.rank, 0 ≤ l.getD k 0) →
      (∀ j : Fin τ.rank, l ≠ List.ofFn (Pi.single j (1 : ℤ))) →
      ∃ j : Fin τ.rank, List.ofFn (fun k : Fin τ.rank =>
          l.getD k 0 - if k = j then (1 : ℤ) else 0) ∈ τ.artifactRoots ∧
        ∀ k : Fin τ.rank, 0 ≤ l.getD k 0 - if k = j then (1 : ℤ) else 0) :
    ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
      ∃ j, IsRoot τ (γ - Pi.single j 1) ∧
        ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin τ.rank → ℤ) k := by
  intro γ hγ hγ0 hγs
  have hget : ∀ k : Fin τ.rank, (List.ofFn γ).getD k 0 = γ k := fun k => by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  obtain ⟨j, hj, hj0⟩ := hlist (List.ofFn γ) (isRoot_iff_mem_artifactRoots.1 hγ)
    (fun k => by rw [hget k]; exact hγ0 k) (fun j h => hγs j (List.ofFn_injective h))
  refine ⟨j, isRoot_iff_mem_artifactRoots.2 ?_, fun k => ?_⟩
  · have hfun : (fun k : Fin τ.rank => (List.ofFn γ).getD k 0 - if k = j then (1 : ℤ) else 0)
        = γ - Pi.single j 1 := by
      funext k
      rw [Pi.sub_apply, Pi.single_apply, hget k]
    rwa [hfun] at hj
  · have hk := hj0 k
    rwa [show ((List.ofFn γ).getD k 0 - (if k = j then (1 : ℤ) else 0))
        = (γ - Pi.single j 1 : Fin τ.rank → ℤ) k by
      rw [Pi.sub_apply, Pi.single_apply, hget k]] at hk

theorem exists_isRoot_add_single_F4 : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ →
    (∀ j, 0 ≤ γ j) → γ ≠ kacF4.θ → ∃ j, IsRoot Tag.F4 (γ + Pi.single j 1) := by
  refine exists_isRoot_add_single_of_forall_list (θ := kacF4.θ) ?_
  have hθ : List.ofFn kacF4.θ = [2, 3, 4, 2] := rfl
  intro l hl h0 hne
  rw [hθ] at hne
  exact forall_mem_add_F4 l hl h0 hne

theorem exists_isRoot_sub_single_F4 : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ →
    (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
    ∃ j, IsRoot Tag.F4 (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin Tag.F4.rank → ℤ) k := by
  exact exists_isRoot_sub_single_of_forall_list forall_mem_sub_F4

theorem exists_isRoot_add_single_E6 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ →
    (∀ j, 0 ≤ γ j) → γ ≠ kacE6.θ → ∃ j, IsRoot Tag.E6 (γ + Pi.single j 1) := by
  refine exists_isRoot_add_single_of_forall_list (θ := kacE6.θ) ?_
  have hθ : List.ofFn kacE6.θ = [1, 2, 2, 3, 2, 1] := rfl
  intro l hl h0 hne
  rw [hθ] at hne
  exact forall_mem_add_E6 l hl h0 hne

theorem exists_isRoot_sub_single_E6 : ∀ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ →
    (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
    ∃ j, IsRoot Tag.E6 (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin Tag.E6.rank → ℤ) k := by
  exact exists_isRoot_sub_single_of_forall_list forall_mem_sub_E6

theorem exists_isRoot_add_single_E7 : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 γ →
    (∀ j, 0 ≤ γ j) → γ ≠ kacE7.θ → ∃ j, IsRoot Tag.E7 (γ + Pi.single j 1) := by
  refine exists_isRoot_add_single_of_forall_list (θ := kacE7.θ) ?_
  have hθ : List.ofFn kacE7.θ = [2, 2, 3, 4, 3, 2, 1] := rfl
  intro l hl h0 hne
  rw [hθ] at hne
  exact forall_mem_add_E7 l hl h0 hne

theorem exists_isRoot_sub_single_E7 : ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 γ →
    (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
    ∃ j, IsRoot Tag.E7 (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin Tag.E7.rank → ℤ) k := by
  exact exists_isRoot_sub_single_of_forall_list forall_mem_sub_E7

theorem exists_isRoot_add_single_E8 : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ →
    (∀ j, 0 ≤ γ j) → γ ≠ kacE8.θ → ∃ j, IsRoot Tag.E8 (γ + Pi.single j 1) := by
  refine exists_isRoot_add_single_of_forall_list (θ := kacE8.θ) ?_
  have hθ : List.ofFn kacE8.θ = [2, 3, 4, 6, 5, 4, 3, 2] := rfl
  intro l hl h0 hne
  rw [hθ] at hne
  exact forall_mem_add_E8 l hl h0 hne

theorem exists_isRoot_sub_single_E8 : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ →
    (∀ j, 0 ≤ γ j) → (∀ j, γ ≠ Pi.single j 1) →
    ∃ j, IsRoot Tag.E8 (γ - Pi.single j 1) ∧ ∀ k, 0 ≤ (γ - Pi.single j 1 : Fin Tag.E8.rank → ℤ) k := by
  exact exists_isRoot_sub_single_of_forall_list forall_mem_sub_E8

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end
