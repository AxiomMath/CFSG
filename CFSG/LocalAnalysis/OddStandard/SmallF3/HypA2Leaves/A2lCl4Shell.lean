module

public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap

theorem cl24_scalar_of_card_three {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 3)
    (c : K) : c = 0 ∨ c = 1 ∨ c = -1 := by
  have hcard_units : Nat.card Kˣ = 2 := by
    rw [Nat.card_units, hK]
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have hc2 : c ^ 2 = 1 := by
      have hpow : (Units.mk0 c hc : Kˣ) ^ Nat.card Kˣ = 1 := pow_card_eq_one'
      rw [hcard_units] at hpow
      simpa [Units.val_mk0] using congrArg (fun u : Kˣ => (u : K)) hpow
    have hfac : (c - 1) * (c + 1) = 0 := by
      have h2 : (c - 1) * (c + 1) = c ^ 2 - 1 := by ring
      rw [h2, hc2, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)

private noncomputable def cl24PlusVec {K : Type} [Field K] (a : K) :
    Kˣ × K × K × K × K → (Fin 4 ⊕ Fin 4 → K) :=
  fun p => Sum.elim
    ![0, p.2.1, (p.1 : K), p.2.2.2.1]
    ![0, p.2.2.1,
      (a - p.2.1 * p.2.2.1 - p.2.2.2.1 * p.2.2.2.2) / (p.1 : K), p.2.2.2.2]

private lemma cl24PlusVec_mem {K : Type} [Field K] (a : K) (p : Kˣ × K × K × K × K) :
    cl24PlusVec a p ∈ (plusPair K (0 : Fin 4)).perp := by
  rw [HypPair.mem_perp, plusPair_e, plusPair_f, polar_single_inl_quadPlus,
    polar_single_inr_quadPlus]
  exact ⟨by simp [cl24PlusVec], by simp [cl24PlusVec]⟩

private lemma cl24PlusVec_ne_zero {K : Type} [Field K] (a : K) (p : Kˣ × K × K × K × K) :
    cl24PlusVec a p ≠ 0 := by
  intro h
  have h2 : (p.1 : K) = 0 := by
    have := congrFun h (Sum.inl 2)
    simpa [cl24PlusVec] using this
  exact p.1.ne_zero h2

private lemma cl24PlusVec_quad {K : Type} [Field K] (a : K) (p : Kˣ × K × K × K × K) :
    quadPlus 4 K (cl24PlusVec a p) = a := by
  obtain ⟨s, x1, y1, x3, y3⟩ := p
  have hs : (s : K) ≠ 0 := s.ne_zero
  rw [quadPlus_apply, Fin.sum_univ_four]
  simp [cl24PlusVec]
  rw [mul_div_cancel₀ _ hs]
  ring

private lemma cl24PlusVec_injective {K : Type} [Field K] (a : K) :
    Function.Injective (cl24PlusVec a) := by
  rintro ⟨s, x1, y1, x3, y3⟩ ⟨s', x1', y1', x3', y3'⟩ h
  have h2 : (s : K) = (s' : K) := by
    have := congrFun h (Sum.inl 2); simpa [cl24PlusVec] using this
  have h1 : x1 = x1' := by
    have := congrFun h (Sum.inl 1); simpa [cl24PlusVec] using this
  have hy1 : y1 = y1' := by
    have := congrFun h (Sum.inr 1); simpa [cl24PlusVec] using this
  have h3 : x3 = x3' := by
    have := congrFun h (Sum.inl 3); simpa [cl24PlusVec] using this
  have hy3 : y3 = y3' := by
    have := congrFun h (Sum.inr 3); simpa [cl24PlusVec] using this
  obtain rfl : s = s' := Units.ext h2
  rw [h1, hy1, h3, hy3]

theorem cl24_shell_plus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (a : K) :
    162 ≤ ({v : Fin 4 ⊕ Fin 4 → K | v ∈ (plusPair K (0 : Fin 4)).perp ∧ v ≠ 0 ∧
      quadPlus 4 K v = a} : Set (Fin 4 ⊕ Fin 4 → K)).ncard := by
  let F : Kˣ × K × K × K × K → (Fin 4 ⊕ Fin 4 → K) := cl24PlusVec a
  have hF : Function.Injective F := cl24PlusVec_injective a
  have hsub : Set.range F ⊆ {v : Fin 4 ⊕ Fin 4 → K |
      v ∈ (plusPair K (0 : Fin 4)).perp ∧ v ≠ 0 ∧ quadPlus 4 K v = a} := by
    rintro v ⟨p, rfl⟩
    exact ⟨cl24PlusVec_mem a p, cl24PlusVec_ne_zero a p, cl24PlusVec_quad a p⟩
  have hcard : Nat.card (Kˣ × K × K × K × K) = 162 := by
    simp only [Nat.card_prod, Nat.card_units, hK]
  calc
    162 = Nat.card (Kˣ × K × K × K × K) := hcard.symm
    _ = (Set.range F).ncard := (Set.ncard_range_of_injective hF).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

private noncomputable def cl24MinusVec {K : Type} [Field K] (b c a : K) :
    Kˣ × K × K × K × K → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :=
  fun p => Sum.elim
    (![0, p.2.1, (p.1 : K)] : Fin (4 - 1) → K)
    (Sum.elim
      (![0, p.2.2.1, (a - p.2.1 * p.2.2.1 -
        ((p.2.2.2.1) ^ 2 + b * p.2.2.2.1 * p.2.2.2.2 + c * (p.2.2.2.2) ^ 2)) /
          (p.1 : K)] : Fin (4 - 1) → K)
      (![p.2.2.2.1, p.2.2.2.2] : Fin 2 → K))

private lemma cl24MinusVec_mem {K : Type} [Field K] (b c a : K) (p : Kˣ × K × K × K × K) :
    cl24MinusVec b c a p ∈
      (minusPair K b c (⟨0, by norm_num⟩ : Fin (4 - 1))).perp := by
  rw [HypPair.mem_perp, minusPair_e, minusPair_f, polar_single_inl_quadMinus,
    polar_single_inr_quadMinus]
  exact ⟨by simp [cl24MinusVec], by simp [cl24MinusVec]⟩

private lemma cl24MinusVec_ne_zero {K : Type} [Field K] (b c a : K) (p : Kˣ × K × K × K × K) :
    cl24MinusVec b c a p ≠ 0 := by
  intro h
  have h2 : (p.1 : K) = 0 := by
    have := congrFun h (Sum.inl 2)
    simpa [cl24MinusVec] using this
  exact p.1.ne_zero h2

private lemma cl24MinusVec_quad {K : Type} [Field K] (b c a : K) (p : Kˣ × K × K × K × K) :
    quadMinus 4 K b c (cl24MinusVec b c a p) = a := by
  obtain ⟨s, x1, y1, u, v⟩ := p
  have hs : (s : K) ≠ 0 := s.ne_zero
  rw [quadMinus_apply, Fin.sum_univ_three]
  simp [cl24MinusVec]
  rw [mul_div_cancel₀ _ hs]
  ring

private lemma cl24MinusVec_injective {K : Type} [Field K] (b c a : K) :
    Function.Injective (cl24MinusVec b c a) := by
  rintro ⟨s, x1, y1, u, v⟩ ⟨s', x1', y1', u', v'⟩ h
  have h2 : (s : K) = (s' : K) := by
    have := congrFun h (Sum.inl 2); simpa [cl24MinusVec] using this
  have h1 : x1 = x1' := by
    have := congrFun h (Sum.inl 1); simpa [cl24MinusVec] using this
  have hy1 : y1 = y1' := by
    have := congrFun h (Sum.inr (Sum.inl 1)); simpa [cl24MinusVec] using this
  have hu : u = u' := by
    have := congrFun h (Sum.inr (Sum.inr 0)); simpa [cl24MinusVec] using this
  have hv : v = v' := by
    have := congrFun h (Sum.inr (Sum.inr 1)); simpa [cl24MinusVec] using this
  obtain rfl : s = s' := Units.ext h2
  rw [h1, hy1, hu, hv]

theorem cl24_shell_minus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (b c a : K) :
    162 ≤ ({v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K |
      v ∈ (minusPair K b c (⟨0, by norm_num⟩ : Fin (4 - 1))).perp ∧ v ≠ 0 ∧
      quadMinus 4 K b c v = a} : Set (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)).ncard := by
  let F : Kˣ × K × K × K × K → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) :=
    cl24MinusVec b c a
  have hF : Function.Injective F := cl24MinusVec_injective b c a
  have hsub : Set.range F ⊆ {v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K |
      v ∈ (minusPair K b c (⟨0, by norm_num⟩ : Fin (4 - 1))).perp ∧ v ≠ 0 ∧
      quadMinus 4 K b c v = a} := by
    rintro v ⟨p, rfl⟩
    exact ⟨cl24MinusVec_mem b c a p, cl24MinusVec_ne_zero b c a p, cl24MinusVec_quad b c a p⟩
  have hcard : Nat.card (Kˣ × K × K × K × K) = 162 := by
    simp only [Nat.card_prod, Nat.card_units, hK]
  calc
    162 = Nat.card (Kˣ × K × K × K × K) := hcard.symm
    _ = (Set.range F).ncard := (Set.ncard_range_of_injective hF).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

end CFSG.OddStandard.SmallF3.HypA2Leaves
