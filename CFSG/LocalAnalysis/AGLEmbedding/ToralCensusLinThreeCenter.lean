module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeCuts

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

variable {K : Type} [Field K] {n : ℕ}

theorem pow_three_apply_of_eq_one {m : ℕ} (hm : m = 1) (M : Matrix (Fin m) (Fin m) K)
    (i j : Fin m) : (M ^ 3) i j = M i j ^ 3 := by
  subst hm
  fin_cases i
  fin_cases j
  simp [pow_succ, Matrix.mul_apply]

theorem cutBlock_succ_mulVec {k : ℕ} (hk : k + 1 ≤ n) (M : Matrix (Fin n) (Fin n) K) :
    cutBlock M k (k + 1) hk *ᵥ (fun _ => (1 : K)) =
      M ⟨k, by omega⟩ ⟨k, by omega⟩ • fun _ => (1 : K) := by
  ext i
  have hi : (i : ℕ) = 0 := by have := i.isLt; omega
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · have e : (⟨k + (i : ℕ), by omega⟩ : Fin n) = ⟨k, by omega⟩ := Fin.ext (by simp [hi])
    simp only [cutBlock_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [e]
  · intro j _ hj
    exact absurd (Fin.ext (by have := j.isLt; omega)) hj
  · intro h
    exact absurd (Finset.mem_univ i) h

variable [Finite K] [CharP K 2] {I : Set ℕ}

theorem mem_of_ne_of_centerCensus (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty)
    (hq : 3 ∣ Nat.card K - 1)
    (hcyc : ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K),
      Q ≤ perfectJoin (flagStabilizer n K I) → IsPGroup 3 Q →
      Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q)
    {i₀ : ℕ} (hi₀ : 1 ≤ i₀) (hi₀n : i₀ < n) (hi₀I : i₀ ∉ I) {i : ℕ} (hi : 1 ≤ i) (hin : i < n)
    (hii₀ : i ≠ i₀) : i ∈ I := by
  by_contra hiI
  have hq4 := four_le_card_of_three_dvd hq
  obtain ⟨a, b, h, ha, hb⟩ := exists_isConsecutiveCut_le_lt I hin
  obtain ⟨a₀, b₀, h₀, ha₀, hb₀⟩ := exists_isConsecutiveCut_le_lt I hi₀n
  have hai : a < i := lt_of_le_of_ne ha fun hai => by
    rcases h.2.2.1 with h0 | hI'
    · omega
    · exact hiI (hai ▸ hI')
  have hai₀ : a₀ < i₀ := lt_of_le_of_ne ha₀ fun hai => by
    rcases h₀.2.2.1 with h0 | hI'
    · omega
    · exact hi₀I (hai ▸ hI')
  have hperf : ∀ {c d : ℕ}, c + 2 ≤ d → 3 ≤ d - c ∨ (d - c = 2 ∧ 4 ≤ Nat.card K) := by
    intro c d hcd
    by_cases h3 : 3 ≤ d - c
    · exact Or.inl h3
    · exact Or.inr ⟨by omega, hq4⟩
  rcases lt_trichotomy a a₀ with hlt | heq | hgt
  · exact false_of_two_perfect_cuts hcyc h h₀ (le_of_isConsecutiveCut_of_lt h h₀ hlt)
      (hperf (by omega)) (hperf (by omega))
  · subst heq
    obtain ⟨-, rfl⟩ := eq_of_isConsecutiveCut_of_mem h h₀ ⟨le_rfl, by omega⟩ ⟨le_rfl, by omega⟩
    exact false_of_three_le_cut hcyc h (by omega) (isConsecutiveCut_sub_lt hI hne h) hq
  · exact false_of_two_perfect_cuts hcyc h₀ h (le_of_isConsecutiveCut_of_lt h₀ h hgt)
      (hperf (by omega)) (hperf (by omega))

theorem le_five_of_centerCensus (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty)
    (hnb : ∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) (hq : 3 ∣ Nat.card K - 1)
    {t : SpecialLinearGroup (Fin n) K}
    (ht3 : t ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (hC : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin n) K)) ≤
      flagStabilizer n K I)
    (hcyc : ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K),
      Q ≤ perfectJoin (flagStabilizer n K I) → IsPGroup 3 Q →
      Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q) :
    n ≤ 5 := by
  classical
  have htI : t ∈ flagStabilizer n K I :=
    hC (Subgroup.mem_centralizer_iff.mpr fun x hx => by rw [Set.mem_singleton_iff.mp hx])
  obtain ⟨ζ, -, hζ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ht3
  have ht : (t : Matrix (Fin n) (Fin n) K) ^ 3 = scalar (Fin n) ζ := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hζ]
  obtain ⟨i₀, hi₀, hi₀n, hi₀I⟩ := hnb
  have hall : ∀ i, 1 ≤ i → i < n → i ≠ i₀ → i ∈ I := fun i hi hin hii₀ =>
    mem_of_ne_of_centerCensus hI hne hq hcyc hi₀ hi₀n hi₀I hi hin hii₀
  set S := (Finset.range n).filter (fun k => (k = 0 ∨ k ∈ I) ∧ (k + 1 = n ∨ k + 1 ∈ I)) with hS
  have hScut : ∀ k ∈ S, IsConsecutiveCut n I k (k + 1) := by
    intro k hk
    rw [hS, Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨by omega, by omega, hk.2.1, hk.2.2, fun c _ hc => by omega⟩
  have hcard : n ≤ S.card + 2 := by
    have hsub : (Finset.range n).filter
        (fun k => ¬ ((k = 0 ∨ k ∈ I) ∧ (k + 1 = n ∨ k + 1 ∈ I))) ⊆ {i₀ - 1, i₀} := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_contra hk'
      push Not at hk'
      refine hk.2 ⟨?_, ?_⟩
      · by_cases hk0 : k = 0
        · exact Or.inl hk0
        · exact Or.inr (hall k (by omega) hk.1 hk'.2)
      · by_cases hkn : k + 1 = n
        · exact Or.inl hkn
        · exact Or.inr (hall (k + 1) (by omega) (by omega) (by omega))
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range n)
      (fun k => (k = 0 ∨ k ∈ I) ∧ (k + 1 = n ∨ k + 1 ∈ I))
    have h2 := Finset.card_le_card hsub
    have h3 : ({i₀ - 1, i₀} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_range, ← hS] at h1
    omega
  set μ : ℕ → K := fun k => if hk : k < n then
    (t : Matrix (Fin n) (Fin n) K) ⟨k, hk⟩ ⟨k, hk⟩ else 0 with hμ
  have hblock : ∀ k (hk : k ∈ S), cutBlock (t : Matrix (Fin n) (Fin n) K) k (k + 1)
      (hScut k hk).2.1 *ᵥ (fun _ => (1 : K)) = μ k • fun _ => (1 : K) := by
    intro k hk
    have hkn : k < n := by have := (hScut k hk).2.1; omega
    rw [cutBlock_succ_mulVec, hμ]
    simp only [dite_eq_left hkn]
  have hcube : ∀ k ∈ S, μ k ^ 3 = ζ := by
    intro k hk
    have hkn : k < n := by have := (hScut k hk).2.1; omega
    have h3 := congrFun (congrFun (cutBlock_pow_three_eq_scalar (hScut k hk) htI ht)
      ⟨0, by omega⟩) ⟨0, by omega⟩
    rw [pow_three_apply_of_eq_one (by omega), cutBlock_apply, scalar_apply,
      diagonal_apply_eq] at h3
    rw [hμ]
    simpa only [dite_eq_left hkn, Nat.add_zero] using h3
  have hne1 : ∀ k : ℕ, (fun _ => (1 : K) : Fin (k + 1 - k) → K) ≠ 0 := fun k h0 => by
    have := congrFun h0 ⟨0, by omega⟩
    exact one_ne_zero this
  have hinj : Set.InjOn μ S := by
    intro k hk k' hk' hkk'
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · exact false_of_eigen_cutBlocks ht (hcube k hk) hC (hScut k hk) (hScut k' hk') hlt
        (hblock k hk) (hne1 k) (by rw [hblock k' hk', ← hkk']) (hne1 k')
    · exact false_of_eigen_cutBlocks ht (hcube k' hk') hC (hScut k' hk') (hScut k hk) hlt
        (hblock k' hk') (hne1 k') (by rw [hblock k hk, hkk']) (hne1 k)
  have hmaps : Set.MapsTo μ S (Polynomial.nthRoots 3 ζ).toFinset := fun k hk => by
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
    exact hcube k hk
  have hle := Finset.card_le_card_of_injOn μ hmaps hinj
  have h3 : (Polynomial.nthRoots 3 ζ).toFinset.card ≤ 3 :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 ζ)
  omega

end CFSG.AGLEmbedding.ToralCensus
