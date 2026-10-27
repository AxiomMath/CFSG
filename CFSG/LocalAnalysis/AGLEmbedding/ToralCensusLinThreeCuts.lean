module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCyc

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)

section Cuts

variable {n : ℕ} {I : Set ℕ}

theorem exists_isConsecutiveCut_le_lt (I : Set ℕ) {k : ℕ} (hk : k < n) :
    ∃ a b, IsConsecutiveCut n I a b ∧ a ≤ k ∧ k < b := by
  classical
  have hex : ∃ b, k < b ∧ (b = n ∨ b ∈ I) := ⟨n, hk, Or.inl rfl⟩
  have hb := Nat.find_spec hex
  have ha : Nat.findGreatest (fun c => c = 0 ∨ c ∈ I) k = 0 ∨
      Nat.findGreatest (fun c => c = 0 ∨ c ∈ I) k ∈ I :=
    Nat.findGreatest_spec (P := fun c => c = 0 ∨ c ∈ I) (Nat.zero_le k) (Or.inl rfl)
  have hak := Nat.findGreatest_le (P := fun c => c = 0 ∨ c ∈ I) k
  refine ⟨_, _, ⟨by omega, Nat.find_min' hex ⟨hk, Or.inl rfl⟩, ha, hb.2, fun c hc hac => ?_⟩,
    hak, hb.1⟩
  by_cases hck : c ≤ k
  · have := Nat.le_findGreatest (P := fun c => c = 0 ∨ c ∈ I) hck (Or.inr hc)
    omega
  · have := Nat.find_min' hex ⟨by omega, Or.inr hc⟩
    omega

theorem le_of_isConsecutiveCut_of_lt {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b)
    (h' : IsConsecutiveCut n I a' b') (haa : a < a') : b ≤ a' := by
  have ha' : a' ∈ I := h'.2.2.1.resolve_left (by omega)
  by_contra hb
  exact h.2.2.2.2 a' ha' ⟨haa, by omega⟩

theorem eq_of_isConsecutiveCut_of_mem {a b a' b' k : ℕ} (h : IsConsecutiveCut n I a b)
    (h' : IsConsecutiveCut n I a' b') (hk : a ≤ k ∧ k < b) (hk' : a' ≤ k ∧ k < b') :
    a = a' ∧ b = b' := by
  have haa : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · have := le_of_isConsecutiveCut_of_lt h h' hlt
      omega
    · exact heq
    · have := le_of_isConsecutiveCut_of_lt h' h hgt
      omega
  refine ⟨haa, ?_⟩
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · have hb : b ∈ I := h.2.2.2.1.resolve_left (by have := h'.2.1; omega)
    exact absurd ⟨by omega, hlt⟩ (h'.2.2.2.2 b hb)
  · exact heq
  · have hb' : b' ∈ I := h'.2.2.2.1.resolve_left (by have := h.2.1; omega)
    exact absurd ⟨by omega, hgt⟩ (h.2.2.2.2 b' hb')

theorem exists_isConsecutiveCut_of_right {a b : ℕ} (h : IsConsecutiveCut n I a b)
    (hbn : b < n) : ∃ b', IsConsecutiveCut n I b b' := by
  obtain ⟨a', b', h', ha', hb'⟩ := exists_isConsecutiveCut_le_lt I hbn
  rcases eq_or_lt_of_le ha' with rfl | hlt
  · exact ⟨b', h'⟩
  · have := (eq_of_isConsecutiveCut_of_mem (k := b - 1) h h'
      ⟨by have := h.1; omega, by have := h.1; omega⟩ ⟨by omega, by omega⟩).2
    omega

theorem isConsecutiveCut_sub_lt (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) {a b : ℕ}
    (h : IsConsecutiveCut n I a b) : b - a < n := by
  obtain ⟨i, hi⟩ := hne
  have := hI i hi
  by_contra hlt
  have := h.2.1
  exact h.2.2.2.2 i hi ⟨by omega, by omega⟩

theorem exists_first_last_cuts (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n) (hne : I.Nonempty) :
    ∃ b₀ a₁, IsConsecutiveCut n I 0 b₀ ∧ IsConsecutiveCut n I a₁ n ∧ b₀ ≤ a₁ := by
  obtain ⟨i, hi⟩ := hne
  have hin := hI i hi
  obtain ⟨a, b₀, h₀, ha, -⟩ := exists_isConsecutiveCut_le_lt (n := n) I (k := 0) (by omega)
  obtain ⟨a₁, b, h₁, -, hb⟩ := exists_isConsecutiveCut_le_lt (n := n) I (k := n - 1) (by omega)
  obtain rfl : a = 0 := by omega
  obtain rfl : b = n := by have := h₁.2.1; omega
  refine ⟨b₀, a₁, h₀, h₁, ?_⟩
  rcases Nat.eq_zero_or_pos a₁ with h0 | hpos
  · have := isConsecutiveCut_sub_lt hI ⟨i, hi⟩ h₁
    omega
  · exact le_of_isConsecutiveCut_of_lt h₀ h₁ hpos

end Cuts

section Three

variable {K : Type} [Field K] [CharP K 2]

theorem three_dvd_card_sl_two_of_charTwo :
    3 ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of, zero_mul, one_mul, zero_sub, CharTwo.neg_eq]
  set A : SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 1], hdet⟩ with hA
  have hA3 : A ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_three', hA]
    change (!![0, 1; 1, 1] * !![0, 1; 1, 1] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j = _
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
    have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
    fin_cases i <;> fin_cases j <;> simp [h11]
  have hA1 : A ≠ 1 := fun h => by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp [hA] at this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← orderOf_eq_prime hA3 hA1]
  exact orderOf_dvd_natCard A

theorem three_dvd_card_sl_of_charTwo {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (SpecialLinearGroup (Fin m) K) := by
  have hdvd := Subgroup.card_dvd_of_injective _
    (CFSG.RankThree.CALinearPlane.blockSLOn_injective (k := K) (intervalCoords m 0 2 hm))
  rw [card_intervalCoords] at hdvd
  exact three_dvd_card_sl_two_of_charTwo.trans hdvd

theorem exists_card_eq_two_pow_of_charTwo [Finite K] : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  exact ⟨f, f.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem three_dvd_card_sq_sub_one [Finite K] : 3 ∣ Nat.card K ^ 2 - 1 := by
  obtain ⟨f, -, hf⟩ := exists_card_eq_two_pow_of_charTwo (K := K)
  have h4 : Nat.card K ^ 2 = 4 ^ f := by rw [hf, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4]
  have hmod : 4 ^ f ≡ 1 [MOD 3] := by
    simpa using (show 4 ≡ 1 [MOD 3] from rfl).pow f
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp hmod.symm

theorem card_eq_two_of_lt_four [Finite K] (h : Nat.card K < 4) : Nat.card K = 2 := by
  obtain ⟨f, hf1, hf⟩ := exists_card_eq_two_pow_of_charTwo (K := K)
  have hf2 : f < 2 := by
    by_contra hf2
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain rfl : f = 1 := by omega
  simpa using hf

omit [CharP K 2] in
theorem four_le_card_of_three_dvd [Finite K] (hq : 3 ∣ Nat.card K - 1) : 4 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have := Nat.le_of_dvd (by omega) hq
  omega

variable [Finite K] {n : ℕ} {I : Set ℕ}

theorem false_of_two_perfect_cuts
    (hcyc : ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K),
      Q ≤ perfectJoin (flagStabilizer n K I) → IsPGroup 3 Q →
      Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q)
    {a b a' b' : ℕ} (h : IsConsecutiveCut n I a b) (h' : IsConsecutiveCut n I a' b')
    (hbb : b ≤ a') (hs : 3 ≤ b - a ∨ (b - a = 2 ∧ 4 ≤ Nat.card K))
    (hs' : 3 ≤ b' - a' ∨ (b' - a' = 2 ∧ 4 ≤ Nat.card K)) : False := by
  obtain ⟨Q, hQ, hQp, hQZ, hnc⟩ := cycBlocksSL_holds K n I 3 Nat.prime_three
    (Or.inl ⟨a, b, a', b', h, h', hbb, hs, hs',
      three_dvd_card_sl_of_charTwo (by omega), three_dvd_card_sl_of_charTwo (by omega)⟩)
  exact hnc (hcyc Q hQ hQp hQZ)

theorem false_of_three_le_cut
    (hcyc : ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K),
      Q ≤ perfectJoin (flagStabilizer n K I) → IsPGroup 3 Q →
      Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q)
    {a b : ℕ} (h : IsConsecutiveCut n I a b) (h3 : 3 ≤ b - a) (hlt : b - a < n)
    (hq : 3 ∣ Nat.card K - 1) : False := by
  obtain ⟨Q, hQ, hQp, hQZ, hnc⟩ := cycBlocksSL_holds K n I 3 Nat.prime_three
    (Or.inr (Or.inl ⟨a, b, h, h3, hlt, hq⟩))
  exact hnc (hcyc Q hQ hQp hQZ)

theorem false_of_four_le_cut
    (hcyc : ∀ Q : Subgroup (SpecialLinearGroup (Fin n) K),
      Q ≤ perfectJoin (flagStabilizer n K I) → IsPGroup 3 Q →
      Q ⊓ Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ → IsCyclic Q)
    {a b : ℕ} (h : IsConsecutiveCut n I a b) (h4 : 4 ≤ b - a) (hq : ¬ 3 ∣ Nat.card K - 1) :
    False := by
  obtain ⟨Q, hQ, hQp, hQZ, hnc⟩ := cycBlocksSL_holds K n I 3 Nat.prime_three
    (Or.inr (Or.inr ⟨a, b, 2, h, by norm_num, by omega, three_dvd_card_sq_sub_one, hq⟩))
  exact hnc (hcyc Q hQ hQp hQZ)

end Three

end CFSG.AGLEmbedding.ToralCensus
