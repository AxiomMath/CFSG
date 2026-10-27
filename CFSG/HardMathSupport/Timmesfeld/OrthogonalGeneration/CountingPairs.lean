module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.CountingZeros
public import CFSG.ClassicalGroups.Orthogonal.FixedHypPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Finset

section Pairs

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a; decide

lemma add_self_zmod2 (g : V) : g + g = 0 := by
  rw [← two_smul (ZMod 2) g]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

lemma map_add_eq (f e : V) : Q (f + e) = Q f + Q e + polar Q f e := by
  rw [polar]; ring

section Fiber

variable [Fintype V]

lemma four_mul_card_fiber (hQ : (polarBilin Q).Nondegenerate) {e : V} (he0 : e ≠ 0)
    (heQ : Q e = 0) :
    4 * (univ.filter fun f => Q f = 0 ∧ polar Q e f = 1).card = Fintype.card V := by
  classical
  obtain ⟨g, hg⟩ := exists_polar_ne_zero hQ he0
  have hg1 : polar Q e g = 1 := zmod2_eq_one_of_ne_zero hg
  set S0 := univ.filter fun f : V => polar Q e f = 0 with hS0
  set S1 := univ.filter fun f : V => polar Q e f = 1 with hS1
  have hcard : Fintype.card V = S0.card + S1.card := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun f => polar Q e f = 1)
    rw [Finset.card_univ] at h
    have hS : (univ.filter fun f : V => ¬ polar Q e f = 1) = S0 := by
      ext f
      simp only [hS0, mem_filter, mem_univ, true_and]
      constructor
      · intro h
        by_contra h'
        exact h (zmod2_eq_one_of_ne_zero h')
      · intro h h'
        rw [h] at h'
        exact absurd h' (by decide)
    rw [hS, ← hS1] at h
    omega
  have hS01 : S0.card = S1.card := by
    refine Finset.card_bij (fun f _ => f + g) ?_ ?_ ?_
    · intro f hf
      simp only [hS0, hS1, mem_filter, mem_univ, true_and] at hf ⊢
      rw [polar_add_right, hf, hg1, zero_add]
    · intro a _ b _ hab
      exact add_right_cancel hab
    · intro b hb
      refine ⟨b + g, ?_, ?_⟩
      · simp only [hS0, hS1, mem_filter, mem_univ, true_and] at hb ⊢
        rw [polar_add_right, hb, hg1]
        decide
      · rw [add_assoc, add_self_zmod2, add_zero]
  have hA : (univ.filter fun f => Q f = 0 ∧ polar Q e f = 1) = S1.filter fun f => Q f = 0 := by
    ext f
    simp only [hS1, mem_filter, mem_univ, true_and]
    tauto
  have hsplit := Finset.card_filter_add_card_filter_not (s := S1) (fun f => Q f = 0)
  have hB : (S1.filter fun f => Q f = 0).card = (S1.filter fun f => ¬ Q f = 0).card := by
    refine Finset.card_bij (fun f _ => f + e) ?_ ?_ ?_
    · intro f hf
      simp only [hS1, mem_filter, mem_univ, true_and] at hf ⊢
      obtain ⟨h1, h2⟩ := hf
      refine ⟨?_, ?_⟩
      · rw [polar_add_right, h1, polar_self_eq_zero heQ]
        simp
      · rw [map_add_eq, h2, heQ, polar_comm, h1]
        decide
    · intro a _ b _ hab
      exact add_right_cancel hab
    · intro b hb
      refine ⟨b + e, ?_, ?_⟩
      · simp only [hS1, mem_filter, mem_univ, true_and] at hb ⊢
        obtain ⟨h1, h2⟩ := hb
        refine ⟨?_, ?_⟩
        · rw [polar_add_right, h1, polar_self_eq_zero heQ]
          simp
        · rw [map_add_eq, heQ, polar_comm, h1]
          have h2' : Q b = 1 := zmod2_eq_one_of_ne_zero h2
          rw [h2']
          decide
      · rw [add_assoc, add_self_zmod2, add_zero]
  rw [hA]
  omega

end Fiber

variable [Module.Finite (ZMod 2) V]

theorem card_hypPairs (hQ : (polarBilin Q).Nondegenerate) {d : ℕ}
    (hd : Module.finrank (ZMod 2) V = d) :
    Nat.card {x : V × V // Q x.1 = 0 ∧ Q x.2 = 0 ∧ polar Q x.1 x.2 = 1} =
      (Nat.card {v : V // Q v = 0} - 1) * 2 ^ (d - 2) := by
  classical
  have hfin : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  have hV : Fintype.card V = 2 ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := V), hd, ZMod.card]
  have hfib : ∀ e : V, e ≠ 0 → Q e = 0 →
      (univ.filter fun f => Q f = 0 ∧ polar Q e f = 1).card = 2 ^ (d - 2) := by
    intro e he0 heQ
    have h4 := four_mul_card_fiber hQ he0 heQ
    rw [hV] at h4
    have hpos : 0 < (univ.filter fun f => Q f = 0 ∧ polar Q e f = 1).card := by
      by_contra hc
      have : (univ.filter fun f => Q f = 0 ∧ polar Q e f = 1).card = 0 := by omega
      rw [this] at h4
      exact absurd h4.symm (by positivity)
    have hd2 : 2 ≤ d := by
      by_contra hc
      have : 2 ^ d ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 2 ^ d = 2 ^ (d - 2) * 4 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
      simp [pow_add]
    omega
  have hinner : ∀ e : V, (∑ f : V, if (Q e = 0 ∧ Q f = 0 ∧ polar Q e f = 1) then 1 else 0) =
      if (Q e = 0 ∧ e ≠ 0) then 2 ^ (d - 2) else 0 := by
    intro e
    by_cases h : Q e = 0 ∧ e ≠ 0
    · simp only [h, and_self, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [← hfib e h.2 h.1, Finset.card_filter]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun f _ => ?_
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      rintro ⟨h1, h2, h3⟩
      apply h
      refine ⟨h1, ?_⟩
      rintro rfl
      simp at h3
  have hzero : Nat.card {v : V // Q v = 0} - 1 = (univ.filter fun e : V => Q e = 0 ∧ e ≠ 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have : (univ.filter fun e : V => Q e = 0 ∧ e ≠ 0) = (univ.filter fun e : V => Q e = 0).erase 0 := by
      ext e
      simp [and_comm]
    rw [this, Finset.card_erase_of_mem (by simp [map_zero])]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [hinner, hzero, Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

end Pairs

section Arithmetic

lemma not_dvd_pairs {ε : Bool} {n p Z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ typeSign ε n) (hZ1 : 1 ≤ Z)
    (hZ : (Z : ℤ) = 2 ^ (2 * (n + 1) - 1) + (if ε then 1 else -1) * 2 ^ (n + 1 - 1)) :
    ¬ p ∣ (Z - 1) * 2 ^ (2 * n + 2 - 2) := by
  have h2 : (2 * (n + 1) - 1) = 2 * n + 1 := by omega
  rw [h2] at hZ
  simp only [Nat.add_sub_cancel] at hZ
  have hZ3 : (p : ℤ) ∣ (Z : ℤ) - 3 := by
    have hx : (2 : ℤ) ^ (2 * n + 1) = 2 * (2 ^ n) ^ 2 := by ring
    cases ε
    · have hd : (p : ℤ) ∣ 2 ^ n + 1 := by
        have : ((typeSign false n : ℕ) : ℤ) = 2 ^ n + 1 := by simp [typeSign]
        rw [← this]; exact_mod_cast hdvd
      obtain ⟨t, ht⟩ := hd
      have : (Z : ℤ) - 3 = (p : ℤ) * (t * (2 * (2 ^ n) - 3 )) := by
        rw [hZ, hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have e : (2 : ℤ) ^ n = p * t - 1 := by linarith
        rw [e]; ring
      rw [this]; exact dvd_mul_right _ _
    · have hd : (p : ℤ) ∣ 2 ^ n - 1 := by
        have : ((typeSign true n : ℕ) : ℤ) = 2 ^ n - 1 := by
          simp [typeSign, Nat.cast_sub (Nat.one_le_two_pow)]
        rw [← this]; exact_mod_cast hdvd
      obtain ⟨t, ht⟩ := hd
      have : (Z : ℤ) - 3 = (p : ℤ) * (t * (2 * (2 ^ n) + 3)) := by
        rw [hZ, hx]
        simp only [↓reduceIte]
        have e : (2 : ℤ) ^ n = p * t + 1 := by linarith
        rw [e]; ring
      rw [this]; exact dvd_mul_right _ _
  intro hdiv
  have hnot2 : ¬ p ∣ 2 ^ (2 * n + 2 - 2) := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hZ1' : p ∣ Z - 1 := (hp.dvd_mul.1 hdiv).resolve_right hnot2
  have hZ1'' : (p : ℤ) ∣ (Z : ℤ) - 1 := by
    have := (Int.natCast_dvd_natCast (m := p) (n := Z - 1)).2 hZ1'
    rwa [Nat.cast_sub hZ1, Nat.cast_one] at this
  have h2' : (p : ℤ) ∣ 2 := by
    have := dvd_sub hZ1'' hZ3
    have e : (Z : ℤ) - 1 - ((Z : ℤ) - 3) = 2 := by ring
    rwa [e] at this
  have : p ∣ 2 := by exact_mod_cast h2'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

end Arithmetic

section Main

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) V] in
lemma finrank_of_isStdSpace {ε : Bool} {n : ℕ} (hstd : IsStdSpace ε Q (n + 1)) :
    Module.finrank (ZMod 2) V = 2 * n + 2 := by
  cases ε
  · obtain ⟨φ, -⟩ := hstd
    rw [φ.finrank_eq, Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega
  · obtain ⟨φ, -⟩ := hstd
    rw [φ.finrank_eq, Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
    omega

theorem exists_fixed_hypPair_of_isStdSpace (hQ : (polarBilin Q).Nondegenerate) {ε : Bool}
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ typeSign ε n)
    (hstd : IsStdSpace ε Q (n + 1)) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite V := Module.finite_of_finite (ZMod 2)
  refine exists_fixed_hypPair hE hexp ?_
  rw [card_hypPairs hQ (finrank_of_isStdSpace hstd)]
  have hZ := card_zeros_of_isStdSpace (Nat.succ_pos n) hstd
  have hZ1 : 1 ≤ Nat.card {v : V // Q v = 0} :=
    Nat.card_pos_iff.2 ⟨⟨0, map_zero Q⟩, inferInstance⟩
  exact not_dvd_pairs hp hp2 hdvd hZ1 hZ

end Main

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
