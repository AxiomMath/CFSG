module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Nat.Even

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma insert_eq_symmDiff_singleton {n : ℕ} {i : Fin n} {A : Finset (Fin n)}
    (hi : i ∉ A) : insert i A = symmDiff A {i} := by
  rw [Finset.symmDiff_eq_union (Finset.disjoint_singleton_right.mpr hi), Finset.union_singleton]

private lemma two_mul_two_pow_pred {n : ℕ} (hn : 0 < n) :
    2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
  have hpred : n = (n - 1) + 1 := by omega
  calc
    2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := (Nat.mul_two _).symm
    _ = 2 ^ ((n - 1) + 1) := (pow_succ _ _).symm
    _ = 2 ^ n := by rw [← hpred]

private lemma tau_mem_iff_not_mem {n : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (hcard : 𝒜.card = 2 ^ (n - 1))
    (hΔ : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, symmDiff A B ∈ 𝒜)
    (hs : ∀ i : Fin n, ({i} : Finset (Fin n)) ∉ 𝒜)
    (i : Fin n) (w : Finset (Fin n)) :
    symmDiff w {i} ∈ 𝒜 ↔ w ∉ 𝒜 := by
  let τ : Finset (Fin n) → Finset (Fin n) := fun v => symmDiff v {i}
  have hτ_invol : Function.Involutive τ := fun v => symmDiff_symmDiff_cancel_right {i} v
  have hτ_inj : Function.Injective τ := hτ_invol.injective
  have hnot : ∀ v, v ∈ 𝒜 → τ v ∉ 𝒜 := by
    intro v hv hvτ
    have hsingle : ({i} : Finset (Fin n)) ∈ 𝒜 := by
      simpa [τ, symmDiff_symmDiff_cancel_left] using hΔ v hv (τ v) hvτ
    exact hs i hsingle
  let 𝒜' : Finset (Finset (Fin n)) := 𝒜.image τ
  have hcard' : 𝒜'.card = 2 ^ (n - 1) := by
    rw [Finset.card_image_of_injective 𝒜 hτ_inj, hcard]
  have hdisj : Disjoint 𝒜 𝒜' := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv'
    exact hnot u hu hv
  have hunion : 𝒜 ∪ 𝒜' = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hcard, hcard', two_mul_two_pow_pred i.pos]
    rw [Fintype.card_finset, Fintype.card_fin]
  have hmem_union : ∀ v, v ∈ 𝒜 ∪ 𝒜' := by
    intro v
    rw [hunion]
    exact Finset.mem_univ v
  have hatleast : ∀ v, v ∈ 𝒜 ∨ τ v ∈ 𝒜 := by
    intro v
    rcases Finset.mem_union.mp (hmem_union v) with hv | hv
    · exact Or.inl hv
    · right
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      simpa [hτ_invol u] using hu
  constructor
  · intro hvτ hv
    exact hnot w hv hvτ
  · intro hw
    rcases hatleast w with hw' | hτw
    · exact absurd hw' hw
    · exact hτw

theorem sec9e_even_of_no_singleton {n : ℕ} (hn : 1 ≤ n) (𝒜 : Finset (Finset (Fin n)))
    (hcard : 𝒜.card = 2 ^ (n - 1)) (h0 : ∅ ∈ 𝒜)
    (hΔ : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, symmDiff A B ∈ 𝒜)
    (hs : ∀ i : Fin n, ({i} : Finset (Fin n)) ∉ 𝒜) : ∀ A ∈ 𝒜, Even A.card := by
  have hAE : ∀ A : Finset (Fin n), A ∈ 𝒜 ↔ Even A.card := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        simpa using h0
    | insert i A hi ih =>
        have hmem : insert i A ∈ 𝒜 ↔ A ∉ 𝒜 := by
          rw [insert_eq_symmDiff_singleton hi]
          exact tau_mem_iff_not_mem 𝒜 hcard hΔ hs i A
        have hc : (insert i A).card = A.card + 1 := Finset.card_insert_of_notMem hi
        rw [hmem, ih, hc]
        exact Nat.even_add_one.symm
  intro A hA
  exact (hAE A).mp hA

end CFSG.OddStandard.SmallF3.Omega
