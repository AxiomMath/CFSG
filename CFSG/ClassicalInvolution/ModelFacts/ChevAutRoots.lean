module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalInvolution.ModelFacts.RootLength

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts

section Roots

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}

@[expose] def pair (A : Matrix (Fin r) (Fin r) ℤ) (γ : Fin r → ℤ) (j : Fin r) : ℤ :=
  ∑ l, A j l * γ l

theorem form_single_right_int (hA : TauCeti.IsFiniteType A) (γ : Fin r → ℤ) (j : Fin r) :
    form hA (toRat γ) (toRat (Pi.single j 1)) = symmetrizer hA j * (pair A γ j : ℚ) := by
  rw [toRat_single, form_single_right]
  simp [pair, toRat_apply]

theorem eq_zero_of_pair_eq_zero (hA : TauCeti.IsFiniteType A) {v : Fin r → ℤ}
    (h : ∀ j, pair A v j = 0) : v = 0 := by
  by_contra hv
  have hpos := form_pos hA (x := toRat v) (fun h0 => hv (toRat_injective (by rw [h0, map_zero])))
  have hsum := form_eq_sum hA (toRat v) (toRat v)
  have h0 : form hA (toRat v) (toRat v) = 0 := by
    rw [hsum]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := form_single_right_int hA v l
    rw [toRat_single] at this
    rw [this, h l]
    simp
  linarith

variable (hA : TauCeti.IsFiniteType A) (hlong : ∀ k, IsLongest hA ∅ (Pi.single k 1))
include hlong

theorem symmetrizer_const (i j : Fin r) : symmetrizer hA i = symmetrizer hA j := by
  have h1 := (hlong i).2 (Pi.single j 1) (hlong j).1
  have h2 := (hlong j).2 (Pi.single i 1) (hlong i).1
  rw [lenSq_single, lenSq_single] at h1 h2
  linarith

theorem lenSq_root {γ : Fin r → ℤ} (hγ : γ ∈ roots hA ∅) (k : Fin r) :
    lenSq hA γ = 2 * symmetrizer hA k := by
  rcases lenSq_of_mem_roots hA hγ with ⟨i, hi⟩ | ⟨i, hi, -⟩
  · rw [hi, symmetrizer_const hA hlong i k]
  · exact absurd hi (Set.notMem_empty i)

theorem abs_pair_le {γ : Fin r → ℤ} (hγ : γ ∈ roots hA ∅) (j : Fin r) : |pair A γ j| ≤ 2 := by
  have hd := symmetrizer_pos hA j
  have hcs := sq_form_le hA (toRat γ) (toRat (Pi.single j 1))
  rw [form_single_right_int hA] at hcs
  have h2 : form hA (toRat (Pi.single j 1 : Fin r → ℤ)) (toRat (Pi.single j 1)) =
      2 * symmetrizer hA j := by
    rw [toRat_single, form_single_single]
  have h1 : form hA (toRat γ) (toRat γ) = 2 * symmetrizer hA j := by
    have := lenSq_root hA hlong hγ j
    rwa [lenSq] at this
  rw [h1, h2, mul_pow] at hcs
  have h3 : ((pair A γ j : ℤ) : ℚ) ^ 2 ≤ 4 := by
    have : symmetrizer hA j ^ 2 * ((pair A γ j : ℤ) : ℚ) ^ 2 ≤ symmetrizer hA j ^ 2 * 4 := by
      nlinarith [hcs]
    exact le_of_mul_le_mul_left this (by positivity)
  have h4 : (pair A γ j) ^ 2 ≤ 4 := by exact_mod_cast h3
  nlinarith [abs_nonneg (pair A γ j), sq_abs (pair A γ j)]

theorem eq_single_of_pair_eq_two {γ : Fin r → ℤ} (hγ : γ ∈ roots hA ∅) {j : Fin r}
    (h : pair A γ j = 2) : γ = Pi.single j 1 := by
  have hd := symmetrizer_pos hA j
  have h1 : form hA (toRat γ) (toRat γ) = 2 * symmetrizer hA j := by
    have := lenSq_root hA hlong hγ j
    rwa [lenSq] at this
  have h2 : form hA (toRat (Pi.single j 1 : Fin r → ℤ)) (toRat (Pi.single j 1)) =
      2 * symmetrizer hA j := by
    rw [toRat_single, form_single_single]
  have h3 := form_single_right_int hA γ j
  rw [h] at h3
  have hz : form hA (toRat (γ - Pi.single j 1)) (toRat (γ - Pi.single j 1)) = 0 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [form_comm hA (toRat (Pi.single j 1 : Fin r → ℤ)) (toRat γ)]
    push_cast at h3
    rw [h1, h2, h3]
    ring
  by_contra hne
  have := form_pos hA (x := toRat (γ - Pi.single j 1)) (fun h0 =>
    hne (sub_eq_zero.1 (toRat_injective (by rw [h0, map_zero]))))
  linarith

theorem eq_neg_single_of_pair_eq_neg_two {γ : Fin r → ℤ} (hγ : γ ∈ roots hA ∅) {j : Fin r}
    (h : pair A γ j = -2) : γ = -Pi.single j 1 := by
  have hd := symmetrizer_pos hA j
  have h1 : form hA (toRat γ) (toRat γ) = 2 * symmetrizer hA j := by
    have := lenSq_root hA hlong hγ j
    rwa [lenSq] at this
  have h2 : form hA (toRat (Pi.single j 1 : Fin r → ℤ)) (toRat (Pi.single j 1)) =
      2 * symmetrizer hA j := by
    rw [toRat_single, form_single_single]
  have h3 := form_single_right_int hA γ j
  rw [h] at h3
  have hz : form hA (toRat (γ + Pi.single j 1)) (toRat (γ + Pi.single j 1)) = 0 := by
    simp only [map_add, LinearMap.add_apply]
    rw [form_comm hA (toRat (Pi.single j 1 : Fin r → ℤ)) (toRat γ)]
    push_cast at h3
    rw [h1, h2, h3]
    ring
  by_contra hne
  have := form_pos hA (x := toRat (γ + Pi.single j 1)) (fun h0 =>
    hne (eq_neg_of_add_eq_zero_left (toRat_injective (by rw [h0, map_zero]))))
  linarith

theorem exists_odd_pair (hnb : ∀ k, ∃ j, A j k = -1) {γ : Fin r → ℤ} (hγ : γ ∈ roots hA ∅) :
    ∃ j, ¬ Even (pair A γ j) := by
  by_contra hall
  have hall' : ∀ j, Even (pair A γ j) := fun j => by
    by_contra h
    exact hall ⟨j, h⟩
  have hb := abs_pair_le hA hlong hγ
  obtain ⟨i⟩ : Nonempty (Fin r) := by
    rcases hγ with ⟨w, i, -⟩ | ⟨w, i, -, -⟩
    exacts [⟨i⟩, ⟨i⟩]
  by_cases h2 : ∃ j, pair A γ j = 2 ∨ pair A γ j = -2
  · obtain ⟨j, hj⟩ := h2
    obtain ⟨j', hj'⟩ := hnb j
    have hs : pair A (Pi.single j 1 : Fin r → ℤ) j' = -1 := by
      simp [pair, Pi.single_apply, hj']
    rcases hj with hj | hj
    · have := eq_single_of_pair_eq_two hA hlong hγ hj
      have h3 := hall' j'
      rw [this, hs] at h3
      exact (by decide : ¬ Even (-1 : ℤ)) h3
    · have := eq_neg_single_of_pair_eq_neg_two hA hlong hγ hj
      have hs' : pair A γ j' = 1 := by
        rw [this]
        have : pair A (-(Pi.single j 1 : Fin r → ℤ)) j' = -pair A (Pi.single j 1) j' := by
          simp [pair]
        rw [this, hs]
        norm_num
      have h3 := hall' j'
      rw [hs'] at h3
      exact (by decide : ¬ Even (1 : ℤ)) h3
  · have h2' : ∀ j, pair A γ j ≠ 2 ∧ pair A γ j ≠ -2 := fun j => by
      by_contra h
      exact h2 ⟨j, by tauto⟩
    have h0 : ∀ j, pair A γ j = 0 := by
      intro j
      have h1 := hb j
      obtain ⟨m, hm⟩ := hall' j
      rw [abs_le] at h1
      have h2j := h2' j
      omega
    have hγ0 := eq_zero_of_pair_eq_zero hA h0
    have hpos := lenSq_root hA hlong hγ i
    rw [hγ0] at hpos
    have := symmetrizer_pos hA i
    simp [lenSq] at hpos
    linarith

end Roots

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
