module

public import CFSG.ClassicalInvolution.Phan.PhanS6T2Co
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Roots

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.T

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] (M : Model K)

omit [DecidableEq K] in
theorem card_K_eq : Fintype.card K = M.q ^ 2 := by
  rw [← Nat.card_eq_fintype_card]
  exact M.card_K

theorem card_nrm_fibre (c : K) :
    (Finset.univ.filter fun x : K => nrm M x = c).card ≤ M.q + 1 := by
  calc (Finset.univ.filter fun x : K => nrm M x = c).card
      ≤ ((Polynomial.nthRoots (M.q + 1) c).toFinset).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.succ_pos _)]
        rw [← hx, nrm, M.tau_pow, ← pow_succ']
    _ ≤ (Polynomial.nthRoots (M.q + 1) c).card := Multiset.toFinset_card_le _
    _ ≤ M.q + 1 := Polynomial.card_nthRoots _ _

theorem card_fix (hq : 1 < M.q) :
    (Finset.univ.filter fun x : K => M.τ x = x).card ≤ M.q := by
  set P : Polynomial K := Polynomial.X ^ M.q - Polynomial.X with hP
  have hdeg : P.natDegree = M.q := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  calc (Finset.univ.filter fun x : K => M.τ x = x).card ≤ P.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
        rw [← M.tau_pow, hx, sub_self]
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = M.q := hdeg

theorem card_sub_tau_fibre (hq : 1 < M.q) (t : K) :
    (Finset.univ.filter fun ω : K => ω - M.τ ω = t).card ≤ M.q := by
  rcases (Finset.univ.filter fun ω : K => ω - M.τ ω = t).eq_empty_or_nonempty with h | ⟨ω₀, h₀⟩
  · rw [h]
    exact Nat.zero_le _
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₀
    refine le_trans (Finset.card_le_card_of_injOn (fun ω => ω - ω₀) ?_ ?_) (card_fix M hq)
    · intro ω hω
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rw [map_sub]
      linear_combination h₀ - hω
    · intro x _ y _ hxy
      simpa using hxy

theorem card_sqfibre (hq : 1 < M.q) (c : K) :
    (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c).card ≤ 2 * M.q := by
  have h1 := Finset.card_le_mul_card_image (f := fun ω : K => ω - M.τ ω)
    (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c) M.q (by
      intro t _
      refine le_trans (Finset.card_le_card ?_) (card_sub_tau_fibre M hq t)
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω.2)
  have h2 : ((Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c).image
      fun ω : K => ω - M.τ ω).card ≤ 2 := by
    calc _ ≤ ((Polynomial.nthRoots 2 c).toFinset).card := by
          apply Finset.card_le_card
          intro t ht
          obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.1 ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
          exact hω
      _ ≤ (Polynomial.nthRoots 2 c).card := Multiset.toFinset_card_le _
      _ ≤ 2 := Polynomial.card_nthRoots _ _
  calc _ ≤ M.q * _ := h1
    _ ≤ M.q * 2 := Nat.mul_le_mul_left _ h2
    _ = 2 * M.q := mul_comm _ _

theorem exists_not_fixed (hq : 1 < M.q) : ∃ δ : K, M.τ δ ≠ δ := by
  by_contra h
  push Not at h
  have h1 := card_fix M hq
  have huniv : (Finset.univ.filter fun x : K => M.τ x = x) = Finset.univ := by
    ext x
    simp [h x]
  rw [huniv, Finset.card_univ, card_K_eq] at h1
  nlinarith

theorem exists_w (hq : 6 ≤ M.q) (c₁ c₂ : K) :
    ∃ w : K, M.τ w ≠ w ∧ (w - M.τ w) ^ 2 ≠ c₁ ∧ (w - M.τ w) ^ 2 ≠ c₂ := by
  by_contra hcon
  push Not at hcon
  have hq1 : 1 < M.q := by omega
  have hsub : (Finset.univ : Finset K) ⊆
      (Finset.univ.filter fun x : K => M.τ x = x) ∪
        (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c₁) ∪
          (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c₂) := by
    intro w _
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : M.τ w = w
    · exact Or.inl (Or.inl h1)
    · by_cases h2 : (w - M.τ w) ^ 2 = c₁
      · exact Or.inl (Or.inr h2)
      · exact Or.inr (hcon w h1 h2)
  have hc := Finset.card_le_card hsub
  have h3 := Finset.card_union_le
    ((Finset.univ.filter fun x : K => M.τ x = x) ∪
      (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c₁))
    (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c₂)
  have h4 := Finset.card_union_le (Finset.univ.filter fun x : K => M.τ x = x)
    (Finset.univ.filter fun ω : K => (ω - M.τ ω) ^ 2 = c₁)
  have h5 := card_fix M hq1
  have h6 := card_sqfibre M hq1 c₁
  have h7 := card_sqfibre M hq1 c₂
  rw [Finset.card_univ, card_K_eq] at hc
  nlinarith

theorem exists_u (hq : 7 ≤ M.q) (x y z : Fin 6 → K) (hx : ∀ i, x i ≠ 0) :
    ∃ u : K, ∀ i, nrm M (x i * u + y i) ≠ z i := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ Finset.univ.biUnion fun i : Fin 6 =>
      Finset.univ.filter fun u : K => nrm M (x i * u + y i) = z i := by
    intro u _
    obtain ⟨i, hi⟩ := hcon u
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨i, hi⟩
  have hc := Finset.card_le_card hsub
  have hb : ∀ i : Fin 6, (Finset.univ.filter fun u : K => nrm M (x i * u + y i) = z i).card ≤
      M.q + 1 := by
    intro i
    refine le_trans (Finset.card_le_card_of_injOn (fun u => x i * u + y i) ?_ ?_)
      (card_nrm_fibre M (z i))
    · intro u hu
      simpa using hu
    · intro a _ b _ hab
      have := add_right_cancel hab
      exact mul_left_cancel₀ (hx i) this
  have hu := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin 6)))
    (t := fun i : Fin 6 => Finset.univ.filter fun u : K => nrm M (x i * u + y i) = z i)
  have hs : ∑ i : Fin 6, (Finset.univ.filter fun u : K =>
      nrm M (x i * u + y i) = z i).card ≤ ∑ _i : Fin 6, (M.q + 1) :=
    Finset.sum_le_sum fun i _ => hb i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  rw [Finset.card_univ, card_K_eq] at hc
  nlinarith

end CFSG.ClassicalInvolution.PhanB3.S.Std.T
