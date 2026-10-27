module

public import CFSG.Blueprint.ChevalleyRootArtifact

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Blueprint.Chevalley


@[expose] def n8 : Fin Tag.E8.rank := ⟨7, by decide⟩

@[expose] def e8Theta : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem isRoot_E8_iff (v : Fin Tag.E8.rank → ℤ) : IsRoot .E8 v ↔ List.ofFn v ∈ e8ArtifactRoots :=
  isRoot_iff_mem_artifactRoots

theorem isRoot_theta : IsRoot .E8 e8Theta := by
  rw [isRoot_E8_iff]; decide +kernel

theorem isRoot_theta_sub : IsRoot .E8 (e8Theta - Pi.single n8 1) := by
  rw [isRoot_E8_iff]; decide +kernel

theorem not_isRoot_theta_add : ∀ i : Fin Tag.E8.rank, ¬ IsRoot .E8 (e8Theta + Pi.single i 1) := by
  intro i
  rw [isRoot_E8_iff]
  revert i
  decide +kernel

theorem not_isRoot_two_single : ∀ i : Fin Tag.E8.rank,
    ¬ IsRoot .E8 (Pi.single i 1 + Pi.single i 1) := by
  intro i
  rw [isRoot_E8_iff]
  revert i
  decide +kernel

theorem reflect_theta_of_ne : ∀ i : Fin Tag.E8.rank, i ≠ n8 → reflect .E8 i e8Theta = e8Theta := by
  decide +kernel

theorem reflect_theta_seven : reflect .E8 n8 e8Theta = e8Theta - Pi.single n8 1 := by
  decide +kernel


theorem e8_string_check : ∀ k < 240, ∀ i : Fin Tag.E8.rank,
    (Tag.rootCertificate .E8).root k = Pi.single i 1 ∨
      (Tag.rootCertificate .E8).root k = -Pi.single i 1 ∨
        (Tag.stringData .E8).up k i + (Tag.stringData .E8).down k i ≤ 1 := by
  decide +kernel

theorem e8_succ_check : ∀ k < 240, (Tag.rootCertificate .E8).root k = e8Theta ∨
    (∃ j : Fin Tag.E8.rank, (Tag.rootCertificate .E8).root k = -Pi.single j 1) ∨
      ∃ i : Fin Tag.E8.rank, (Tag.rootCertificate .E8).root k ≠ Pi.single i 1 ∧
        (Tag.rootCertificate .E8).root k ≠ -Pi.single i 1 ∧ 1 ≤ (Tag.stringData .E8).up k i := by
  decide +kernel

theorem stringUp_add_stringDown_le_one {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (i : Fin Tag.E8.rank) (hne : α ≠ Pi.single i 1) (hne' : α ≠ -Pi.single i 1) :
    stringUp .E8 i α + stringDown .E8 i α ≤ 1 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E8) hα
  have hk' : k < 240 := by
    have := Tag.rootCertificate_length .E8
    have h240 : Tag.E8.rootCount = 240 := rfl
    omega
  rcases e8_string_check k hk' i with h | h | h
  · exact absurd h hne
  · exact absurd h hne'
  obtain ⟨-, h1⟩ := StringData.isRoot_root_add_iff (Tag.rootCertificate_check .E8)
    (Tag.stringData_check .E8) hk i hne hne'
  obtain ⟨-, h2⟩ := isRoot_add_smul_single_iff hα i hne hne'
  have key : ∀ m : ℤ, (-((Tag.stringData .E8).down k i : ℤ) ≤ m ∧
      m ≤ (Tag.stringData .E8).up k i) ↔
      (-(stringDown .E8 i ((Tag.rootCertificate .E8).root k) : ℤ) ≤ m ∧
        m ≤ stringUp .E8 i ((Tag.rootCertificate .E8).root k)) := fun m => (h1 m).symm.trans (h2 m)
  have a1 := (key ((Tag.stringData .E8).up k i : ℤ)).1 ⟨by omega, le_rfl⟩
  have a2 := (key (stringUp .E8 i ((Tag.rootCertificate .E8).root k) : ℤ)).2 ⟨by omega, le_rfl⟩
  have b1 := (key (-((Tag.stringData .E8).down k i : ℤ))).1 ⟨le_rfl, by omega⟩
  have b2 := (key (-(stringDown .E8 i ((Tag.rootCertificate .E8).root k) : ℤ))).2
    ⟨le_rfl, by omega⟩
  omega

theorem exists_succ_of_ne_theta {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) (hθ : α ≠ e8Theta)
    (hneg : ∀ j : Fin Tag.E8.rank, α ≠ -Pi.single j 1) :
    ∃ i : Fin Tag.E8.rank, α ≠ Pi.single i 1 ∧ α ≠ -Pi.single i 1 ∧
      IsRoot .E8 (α + Pi.single i 1) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E8) hα
  have hk' : k < 240 := by
    have := Tag.rootCertificate_length .E8
    have h240 : Tag.E8.rootCount = 240 := rfl
    omega
  rcases e8_succ_check k hk' with h | ⟨j, h⟩ | ⟨i, hne, hne', hup⟩
  · exact absurd h hθ
  · exact absurd h (hneg j)
  refine ⟨i, hne, hne', ?_⟩
  obtain ⟨-, h1⟩ := StringData.isRoot_root_add_iff (Tag.rootCertificate_check .E8)
    (Tag.stringData_check .E8) hk i hne hne'
  have := (h1 1).2 ⟨by omega, by omega⟩
  simpa using this

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
