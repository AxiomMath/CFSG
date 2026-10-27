module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

noncomputable section

variable {G : Type*} [Group G]

theorem exists_pair_of_sum_sq_eq_two {ι : Type*} [Fintype ι] {n : ι → ℤ}
    (h : ∑ i, n i ^ 2 = 2) :
    ∃ i j : ι, i ≠ j ∧ n i ^ 2 = 1 ∧ n j ^ 2 = 1 ∧ ∀ k, k ≠ i → k ≠ j → n k = 0 := by
  classical
  set S : Finset ι := {i | n i ≠ 0} with hSdef
  have hmem : ∀ i, i ∈ S ↔ n i ≠ 0 := by intro i; simp [hSdef]
  have hsum : ∑ i ∈ S, n i ^ 2 = 2 := by
    rw [← h]
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have hi0 : n i = 0 := by
      by_contra h0
      exact hi ((hmem i).2 h0)
    simp [hi0]
  have hone : ∀ i ∈ S, n i ^ 2 = 1 := by
    intro i hi
    have h0 : n i ≠ 0 := (hmem i).1 hi
    have hle : n i ^ 2 ≤ 2 :=
      hsum ▸ Finset.single_le_sum (fun j _ => sq_nonneg (n j)) hi
    have h1 : 1 ≤ |n i| := Int.one_le_abs (by omega)
    have h2 : |n i| < 2 := by nlinarith [sq_abs (n i), abs_nonneg (n i)]
    have h3 : |n i| = 1 := by omega
    rw [← sq_abs, h3, one_pow]
  have hcard : S.card = 2 := by
    have hc : ∑ i ∈ S, n i ^ 2 = ∑ _i ∈ S, (1 : ℤ) := Finset.sum_congr rfl hone
    rw [hc, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    exact_mod_cast hsum
  obtain ⟨i, j, hij, hSij⟩ := Finset.card_eq_two.1 hcard
  refine ⟨i, j, hij, hone i (by simp [hSij]), hone j (by simp [hSij]), fun k hki hkj => ?_⟩
  by_contra hk
  have hkS : k ∈ S := (hmem k).2 hk
  rw [hSij] at hkS
  simp [hki, hkj] at hkS

variable [Fintype G]

theorem exists_sub_Irr_of_cfInner_self_eq_two {z : G → ℂ}
    (hz : z ∈ Submodule.span ℤ (Irr G)) (hnorm : cfInner z z = 2) (hz1 : z 1 = 0) :
    ∃ η ∈ Irr G, ∃ θ ∈ Irr G, η ≠ θ ∧ η 1 = θ 1 ∧ z = η - θ := by
  classical
  have : Fintype (Irr G) := Fintype.ofFinite _
  obtain ⟨n, rfl⟩ := mem_span_Irr_iff_exists_intCast_sum.1 hz
  have hsum : ∑ χ : Irr G, n χ ^ 2 = 2 := by
    have h := cfInner_self_intCast_sum_Irr n
    rw [hnorm] at h
    exact_mod_cast h.symm
  obtain ⟨i, j, hij, hi, hj, hzero⟩ := exists_pair_of_sum_sq_eq_two hsum
  have hzeq : (∑ χ : Irr G, (n χ : ℂ) • ((χ : Irr G) : G → ℂ))
      = (n i : ℂ) • ((i : Irr G) : G → ℂ) + (n j : ℂ) • ((j : Irr G) : G → ℂ) := by
    rw [← Finset.sum_subset (s₁ := ({i, j} : Finset (Irr G))) (Finset.subset_univ _)
      (fun k _ hk => ?_), Finset.sum_pair hij]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      rw [hzero k hk.1 hk.2]
      simp
  rw [hzeq] at hz1 ⊢
  have heval : (n i : ℂ) * ((i : Irr G) : G → ℂ) 1 + (n j : ℂ) * ((j : Irr G) : G → ℂ) 1 = 0 := by
    simpa using hz1
  obtain ⟨di, hdi, hdi1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr i.2
  obtain ⟨dj, hdj, hdj1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr j.2
  have hne : ((i : Irr G) : G → ℂ) ≠ ((j : Irr G) : G → ℂ) := fun h => hij (Subtype.ext h)
  have hni : n i = 1 ∨ n i = -1 := by
    have h : (n i - 1) * (n i + 1) = 0 := by linear_combination hi
    rcases mul_eq_zero.1 h with h | h <;> omega
  have hnj : n j = 1 ∨ n j = -1 := by
    have h : (n j - 1) * (n j + 1) = 0 := by linear_combination hj
    rcases mul_eq_zero.1 h with h | h <;> omega
  have hpos : ((i : Irr G) : G → ℂ) 1 + ((j : Irr G) : G → ℂ) 1 ≠ 0 := by
    rw [hdi1, hdj1, ← Nat.cast_add, Nat.cast_ne_zero]
    omega
  rcases hni with hni | hni <;> rcases hnj with hnj | hnj
  · rw [hni, hnj] at heval
    exact absurd (by linear_combination heval) hpos
  · exact ⟨_, i.2, _, j.2, hne, by rw [hni, hnj] at heval; linear_combination heval, by
      rw [hni, hnj]; push_cast; module⟩
  · exact ⟨_, j.2, _, i.2, hne.symm, by rw [hni, hnj] at heval; linear_combination heval, by
      rw [hni, hnj]; push_cast; module⟩
  · rw [hni, hnj] at heval
    exact absurd (by linear_combination -heval) hpos

theorem sub_mem_span_Irr_of_mem_Irr {η θ : G → ℂ} (hη : η ∈ Irr G) (hθ : θ ∈ Irr G) :
    η - θ ∈ Submodule.span ℤ (Irr G) :=
  sub_mem (Submodule.subset_span hη) (Submodule.subset_span hθ)

theorem cfInner_self_sub_of_mem_Irr {η θ : G → ℂ} (hη : η ∈ Irr G) (hθ : θ ∈ Irr G)
    (hne : η ≠ θ) : cfInner (η - θ) (η - θ) = 2 := by
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_self_of_mem_Irr hη, cfInner_self_of_mem_Irr hθ,
    cfInner_eq_zero_of_mem_Irr hη hθ hne, cfInner_eq_zero_of_mem_Irr hθ hη hne.symm]
  ring

theorem cfInner_self_eq_two_and_apply_one_eq_zero_iff {z : G → ℂ}
    (hz : z ∈ Submodule.span ℤ (Irr G)) :
    (cfInner z z = 2 ∧ z 1 = 0) ↔
      ∃ η ∈ Irr G, ∃ θ ∈ Irr G, η ≠ θ ∧ η 1 = θ 1 ∧ z = η - θ := by
  refine ⟨fun ⟨h1, h2⟩ => exists_sub_Irr_of_cfInner_self_eq_two hz h1 h2, ?_⟩
  rintro ⟨η, hη, θ, hθ, hne, hdeg, rfl⟩
  exact ⟨cfInner_self_sub_of_mem_Irr hη hθ hne, by simp [hdeg]⟩

end

end CFSG.FeitThompson
