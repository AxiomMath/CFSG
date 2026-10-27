module

public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.Universal.RootData

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.RootSystem CFSG.LieType.Universal

section Cartan

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}

@[expose] def IsIrreducible (A : Matrix I I ℤ) : Prop :=
  ∀ S : Set I, S.Nonempty → (∀ i ∈ S, ∀ j, A i j ≠ 0 → j ∈ S) → ∀ j, j ∈ S

omit [Fintype I] in
theorem isIrreducible_of_parent (r : I) (par : I → I) (h : I → ℕ)
    (hpar : ∀ j, j ≠ r → A (par j) j ≠ 0 ∧ A j (par j) ≠ 0 ∧ h (par j) < h j) :
    IsIrreducible A := by
  intro S ⟨i₀, hi₀⟩ hS
  have hr_mem : ∀ m, ∀ i ∈ S, h i ≤ m → r ∈ S := by
    intro m
    induction m with
    | zero =>
      intro i hi hhi
      by_cases hir : i = r
      · exact hir ▸ hi
      · have := (hpar i hir).2.2
        omega
    | succ m ih =>
      intro i hi hhi
      by_cases hir : i = r
      · exact hir ▸ hi
      · obtain ⟨-, h2, h3⟩ := hpar i hir
        exact ih (par i) (hS i hi (par i) h2) (by omega)
  have hrS : r ∈ S := hr_mem (h i₀) i₀ hi₀ le_rfl
  have key : ∀ m, ∀ j, h j ≤ m → j ∈ S := by
    intro m
    induction m with
    | zero =>
      intro j hj
      by_cases hjr : j = r
      · exact hjr ▸ hrS
      · have := (hpar j hjr).2.2
        omega
    | succ m ih =>
      intro j hj
      by_cases hjr : j = r
      · exact hjr ▸ hrS
      · obtain ⟨h1, -, h3⟩ := hpar j hjr
        exact hS (par j) (ih (par j) (by omega)) j h1
  exact fun j => key (h j) j le_rfl

variable (hA : TauCeti.IsFiniteType A)

@[expose] noncomputable def lenSq (γ : I → ℤ) : ℚ := form hA (toRat γ) (toRat γ)

theorem lenSq_pos {γ : I → ℤ} (hγ : γ ≠ 0) : 0 < lenSq hA γ :=
  form_pos hA fun h => hγ (toRat_injective (by rw [h, map_zero]))

theorem lenSq_weylAction (w : (coxeterMatrix hA).Group) (γ : I → ℤ) :
    lenSq hA (weylAction hA w γ) = lenSq hA γ :=
  form_weylAction hA w γ γ

theorem lenSq_single (i : I) : lenSq hA (Pi.single i 1) = 2 * symmetrizer hA i := by
  rw [lenSq, toRat_single, form_single_single]

theorem lenSq_neg (γ : I → ℤ) : lenSq hA (-γ) = lenSq hA γ := by
  simp [lenSq, map_neg]

theorem lenSq_two_nsmul (γ : I → ℤ) : lenSq hA (2 • γ) = 4 * lenSq hA γ := by
  simp only [lenSq, two_nsmul, map_add, LinearMap.add_apply]
  rw [form_comm hA (toRat γ) (toRat γ)]
  ring

theorem lenSq_of_mem_roots {D : Set I} {γ : I → ℤ} (hγ : γ ∈ roots hA D) :
    (∃ i, lenSq hA γ = 2 * symmetrizer hA i) ∨ ∃ i ∈ D, lenSq hA γ = 8 * symmetrizer hA i := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact Or.inl ⟨i, by rw [lenSq_weylAction, lenSq_single]⟩
  · refine Or.inr ⟨i, hi, ?_⟩
    rw [lenSq_two_nsmul, lenSq_weylAction, lenSq_single]
    ring

@[expose] def IsLongest (D : Set I) (γ : I → ℤ) : Prop :=
  γ ∈ roots hA D ∧ ∀ δ ∈ roots hA D, lenSq hA δ ≤ lenSq hA γ

variable {hA}

theorem IsLongest.mem {D : Set I} {γ : I → ℤ} (h : IsLongest hA D γ) : γ ∈ roots hA D := h.1

theorem IsLongest.lenSq_eq {D : Set I} {γ γ' : I → ℤ} (h : IsLongest hA D γ)
    (h' : IsLongest hA D γ') : lenSq hA γ = lenSq hA γ' :=
  le_antisymm (h'.2 γ h.1) (h.2 γ' h'.1)

theorem IsLongest.map_weylAction {D : Set I} {γ : I → ℤ} (h : IsLongest hA D γ)
    (w : (coxeterMatrix hA).Group) : IsLongest hA D (weylAction hA w γ) := by
  refine ⟨weylAction_mem_roots hA w h.1, fun δ hδ => ?_⟩
  have := h.2 _ (weylAction_mem_roots hA w⁻¹ hδ)
  rw [lenSq_weylAction] at this ⊢
  exact this

theorem IsLongest.neg {D : Set I} {γ : I → ℤ} (h : IsLongest hA D γ) : IsLongest hA D (-γ) := by
  refine ⟨CFSG.LieType.Steinberg.OfCartan.neg_mem_roots hA h.1, fun δ hδ => ?_⟩
  rw [lenSq_neg]
  exact h.2 δ hδ

variable (hA)

theorem symmetrizer_mul_apply (i j : I) :
    symmetrizer hA i * A i j = symmetrizer hA j * A j i := by
  have h1 := form_single_left hA i (Pi.single j (1 : ℚ))
  have h2 := form_single_left hA j (Pi.single i (1 : ℚ))
  rw [form_comm hA, h1] at h2
  simpa [Pi.single_apply] using h2

variable {hA}

theorem exists_symmetrizer_eq_smul (hirr : IsIrreducible A) {d : I → ℚ} (hd : ∀ i, 0 < d i)
    (hsym : ∀ i j, d i * A i j = d j * A j i) :
    ∃ c : ℚ, 0 < c ∧ ∀ i, symmetrizer hA i = c * d i := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  set c := symmetrizer hA i₀ / d i₀ with hc
  refine ⟨c, div_pos (symmetrizer_pos hA i₀) (hd i₀), ?_⟩
  have h0 : symmetrizer hA i₀ = c * d i₀ := by
    rw [hc]
    field_simp [(hd i₀).ne']
  have hS := hirr {j | symmetrizer hA j = c * d j} ⟨i₀, h0⟩ ?_
  · exact fun i => hS i
  · intro i hi j hij
    have hji : A j i ≠ 0 := fun h => hij (hA.apply_eq_zero_iff.mpr h)
    have hji' : (A j i : ℚ) ≠ 0 := by exact_mod_cast hji
    have h1 := symmetrizer_mul_apply hA i j
    have h2 := hsym i j
    change symmetrizer hA i = c * d i at hi
    change symmetrizer hA j = c * d j
    have h1' : symmetrizer hA i * (A i j : ℚ) = symmetrizer hA j * (A j i : ℚ) := by
      exact_mod_cast h1
    have h2' : d i * (A i j : ℚ) = d j * (A j i : ℚ) := by exact_mod_cast h2
    refine mul_right_cancel₀ hji' ?_
    rw [← h1', hi]
    linear_combination c * h2'

variable (hA)

theorem isLongest_single (hirr : IsIrreducible A) {d : I → ℚ} (hd : ∀ i, 0 < d i)
    (hsym : ∀ i j, d i * A i j = d j * A j i) {k : I} (hk : ∀ j, d j ≤ d k) :
    IsLongest hA ∅ (Pi.single k 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_symmetrizer_eq_smul hirr hd hsym
  refine ⟨Or.inl ⟨1, k, by simp⟩, fun δ hδ => ?_⟩
  rcases hδ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · rw [lenSq_weylAction, lenSq_single, lenSq_single, hcd, hcd]
    nlinarith [hk i]
  · exact absurd hi (Set.notMem_empty i)

theorem isLongest_two_nsmul_single (hirr : IsIrreducible A) {d : I → ℚ} (hd : ∀ i, 0 < d i)
    (hsym : ∀ i j, d i * A i j = d j * A j i) {D : Set I} {k : I} (hkD : k ∈ D)
    (hk1 : ∀ i ∈ D, d i ≤ d k) (hk2 : ∀ j, d j ≤ 4 * d k) :
    IsLongest hA D (2 • Pi.single k 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_symmetrizer_eq_smul hirr hd hsym
  refine ⟨Or.inr ⟨1, k, hkD, by simp⟩, fun δ hδ => ?_⟩
  have hk : lenSq hA (2 • (Pi.single k 1 : I → ℤ)) = 8 * (c * d k) := by
    rw [lenSq_two_nsmul, lenSq_single, hcd]
    ring
  rw [hk]
  rcases hδ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · rw [lenSq_weylAction, lenSq_single, hcd]
    nlinarith [hk2 i]
  · rw [lenSq_two_nsmul, lenSq_weylAction, lenSq_single, hcd]
    nlinarith [hk1 i hi]

end Cartan

section Datum

variable {K : Type*} [Group K]

@[expose] def IsLongestRoot (D : UniversalRootDatum K) (γ : Fin D.rank → ℤ) : Prop :=
  IsLongest D.isFiniteType D.divisible γ

theorem isLongestRoot_iff (D : UniversalRootDatum K) (γ : Fin D.rank → ℤ) :
    IsLongestRoot D γ ↔ γ ∈ D.roots ∧ ∀ δ ∈ D.roots,
      form D.isFiniteType (toRat δ) (toRat δ) ≤ form D.isFiniteType (toRat γ) (toRat γ) :=
  Iff.rfl

end Datum

end CFSG.ClassicalInvolution.ModelFacts
