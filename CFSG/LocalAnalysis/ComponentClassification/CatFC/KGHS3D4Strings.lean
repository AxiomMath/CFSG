module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4Table
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.Blueprint.ChevalleySimpleRootOperators

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3.D4

open CFSG.Blueprint.Chevalley


theorem d4Roots_mem_iff_ofFn (β : Fin 4 → ℤ) : β ∈ d4Roots ↔ List.ofFn β ∈ d4ArtifactRoots := by
  constructor
  · intro h
    have key : ∀ γ ∈ d4Roots, List.ofFn γ ∈ d4ArtifactRoots := by decide +kernel
    exact key β h
  · intro h
    have key : ∀ l ∈ d4ArtifactRoots, ∃ γ ∈ d4Roots, List.ofFn γ = l := by decide +kernel
    obtain ⟨γ, hγ, hγβ⟩ := key _ h
    rw [List.ofFn_injective hγβ] at hγ
    exact hγ

theorem isRoot_D4_iff {β : Fin 4 → ℤ} : IsRoot Tag.D4 β ↔ β ∈ d4Roots :=
  (d4_root_certificate.1 β).trans (d4Roots_mem_iff_ofFn β).symm

theorem d4_string_decide : ∀ α ∈ d4Roots, ∀ i : Fin 4, α ≠ e i → α ≠ -e i →
    α + (2:ℤ) • e i ∉ d4Roots ∧ α + (-2:ℤ) • e i ∉ d4Roots ∧
      ¬ (α + (1:ℤ) • e i ∈ d4Roots ∧ α + (-1:ℤ) • e i ∈ d4Roots) := by
  decide +kernel

theorem mem_d4_add_smul_iff {α : Fin 4 → ℤ} (hα : α ∈ d4Roots) (i : Fin 4) (h1 : α ≠ e i)
    (h2 : α ≠ -e i) (m : ℤ) :
    α + m • e i ∈ d4Roots ↔ -(stringDown Tag.D4 i α : ℤ) ≤ m ∧ m ≤ stringUp Tag.D4 i α :=
  isRoot_D4_iff.symm.trans ((isRoot_add_smul_single_iff (isRoot_D4_iff.2 hα) i h1 h2).2 m)

theorem string_D4 {α : Fin 4 → ℤ} (hα : α ∈ d4Roots) (i : Fin 4) (h1 : α ≠ e i)
    (h2 : α ≠ -e i) :
    stringUp Tag.D4 i α ≤ 1 ∧ stringDown Tag.D4 i α ≤ 1 ∧
      (stringUp Tag.D4 i α = 1 → stringDown Tag.D4 i α = 0) ∧
      (stringDown Tag.D4 i α = 1 → stringUp Tag.D4 i α = 0) ∧
      (α + e i ∈ d4Roots ↔ 1 ≤ stringUp Tag.D4 i α) ∧
      (α - e i ∈ d4Roots ↔ 1 ≤ stringDown Tag.D4 i α) := by
  obtain ⟨d2, dm2, dboth⟩ := d4_string_decide α hα i h1 h2
  have hP2 := mem_d4_add_smul_iff hα i h1 h2 2
  have hQ2 := mem_d4_add_smul_iff hα i h1 h2 (-2)
  have hP1 := mem_d4_add_smul_iff hα i h1 h2 1
  have hQ1 := mem_d4_add_smul_iff hα i h1 h2 (-1)
  have a1 : ¬ (-(stringDown Tag.D4 i α : ℤ) ≤ 2 ∧ (2:ℤ) ≤ stringUp Tag.D4 i α) :=
    fun h => d2 (hP2.2 h)
  have a2 : ¬ (-(stringDown Tag.D4 i α : ℤ) ≤ -2 ∧ (-2:ℤ) ≤ stringUp Tag.D4 i α) :=
    fun h => dm2 (hQ2.2 h)
  have a3 : ¬ ((-(stringDown Tag.D4 i α : ℤ) ≤ 1 ∧ (1:ℤ) ≤ stringUp Tag.D4 i α) ∧
      (-(stringDown Tag.D4 i α : ℤ) ≤ -1 ∧ (-1:ℤ) ≤ stringUp Tag.D4 i α)) :=
    fun h => dboth ⟨hP1.2 h.1, hQ1.2 h.2⟩
  have em : α - e i = α + (-1:ℤ) • e i := by
    rw [sub_eq_add_neg, neg_one_smul]
  have ep : α + e i = α + (1:ℤ) • e i := by rw [one_smul]
  rw [em, ep]
  refine ⟨by omega, by omega, fun h => by omega, fun h => by omega, ?_, ?_⟩
  · constructor
    · intro h
      have := (hP1.1 h).2
      omega
    · intro h
      exact hP1.2 ⟨by omega, by omega⟩
  · constructor
    · intro h
      have := (hQ1.1 h).1
      omega
    · intro h
      exact hQ1.2 ⟨by omega, by omega⟩

theorem rootVec_eq_zero_of_not_root {τ : Tag} {R : Type*} [CommRing R] {β : Fin τ.rank → ℤ}
    (hβ : ¬ IsRoot τ β) : rootVec τ R β = 0 :=
  dite_eq_right hβ

theorem xOp_rootVec_of_string {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h1 : α ≠ Pi.single i 1) (h2 : α ≠ -Pi.single i 1)
    (hP : stringUp τ i α ≤ 1) (hPQ : stringUp τ i α = 1 → stringDown τ i α = 0) :
    xOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α + Pi.single i 1) := by
  have hone : IsRoot τ (α + Pi.single i 1) ↔
      -(stringDown τ i α : ℤ) ≤ 1 ∧ (1:ℤ) ≤ (stringUp τ i α : ℤ) := by
    have h := (isRoot_add_smul_single_iff hα i h1 h2).2 1
    rwa [one_smul] at h
  rw [xOp_apply_rootVec_of_ne i c hα h1 h2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hP with h0 | h0
  · have hn : ¬ IsRoot τ (α + Pi.single i 1) := fun h => by
      have := (hone.1 h).2
      omega
    rw [rootVec_eq_zero_of_not_root hn, smul_zero, add_zero]
    simp [h0]
  · rw [h0, Finset.sum_range_succ, Finset.sum_range_one]
    simp [hPQ h0]

theorem yOp_rootVec_of_string {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h1 : α ≠ Pi.single i 1) (h2 : α ≠ -Pi.single i 1)
    (hQ : stringDown τ i α ≤ 1) (hQP : stringDown τ i α = 1 → stringUp τ i α = 0) :
    yOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α - Pi.single i 1) := by
  have hsub : α - Pi.single i 1 = α + (-1:ℤ) • Pi.single i 1 := by
    rw [sub_eq_add_neg, neg_one_smul]
  have hone : IsRoot τ (α - Pi.single i 1) ↔ 1 ≤ stringDown τ i α := by
    rw [hsub]
    have h := (isRoot_add_smul_single_iff hα i h1 h2).2 (-1)
    constructor
    · intro hm
      have := (h.1 hm).1
      omega
    · intro hq
      exact h.2 ⟨by omega, by omega⟩
  rw [yOp_apply_rootVec_of_ne i c hα h1 h2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hQ with h0 | h0
  · have hn : ¬ IsRoot τ (α - Pi.single i 1) := fun h => by
      have := hone.1 h
      omega
    rw [rootVec_eq_zero_of_not_root hn, smul_zero, add_zero]
    simp [h0]
  · rw [h0, Finset.sum_range_succ, Finset.sum_range_one]
    simp [hQP h0]

theorem xOp_D4_rootVec_of_ne {R : Type*} [CommRing R] (i : Fin 4) (c : R) {α : Fin 4 → ℤ}
    (hα : α ∈ d4Roots) (h1 : α ≠ e i) (h2 : α ≠ -e i) :
    xOp Tag.D4 R i c (rootVec Tag.D4 R α) = rootVec Tag.D4 R α + c • rootVec Tag.D4 R (α + e i) := by
  obtain ⟨hP, -, hPQ, -, -, -⟩ := string_D4 hα i h1 h2
  exact xOp_rootVec_of_string (τ := Tag.D4) i c (isRoot_D4_iff.2 hα) h1 h2 hP hPQ

theorem yOp_D4_rootVec_of_ne {R : Type*} [CommRing R] (i : Fin 4) (c : R) {α : Fin 4 → ℤ}
    (hα : α ∈ d4Roots) (h1 : α ≠ e i) (h2 : α ≠ -e i) :
    yOp Tag.D4 R i c (rootVec Tag.D4 R α) = rootVec Tag.D4 R α + c • rootVec Tag.D4 R (α - e i) := by
  obtain ⟨-, hQ, -, hQP, -, -⟩ := string_D4 hα i h1 h2
  exact yOp_rootVec_of_string (τ := Tag.D4) i c (isRoot_D4_iff.2 hα) h1 h2 hQ hQP

end CFSG.ComponentClassification.CatFC.KGHS3.D4
