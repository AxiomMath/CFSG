module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteQuadraticBases
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

section Twisted

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

theorem pow_two_pow_mod (hcard : Fintype.card K = 2 ^ n) (x : K) (k : ℕ) :
    x ^ 2 ^ k = x ^ 2 ^ (k % n) := by
  conv_lhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, pow_mul, ← hcard,
    FiniteField.pow_card_pow]

theorem pow_two_pow_pow_two_pow (hcard : Fintype.card K = 2 ^ n) (x : K) (j t : Fin n) :
    (x ^ 2 ^ (j : ℕ)) ^ 2 ^ (t : ℕ) = x ^ 2 ^ ((j + t : Fin n) : ℕ) := by
  rw [← pow_mul, ← pow_add, Fin.val_add, ← pow_two_pow_mod hcard]

variable [CharP K 2] [NeZero n]

theorem twisted_expansion (hcard : Fintype.card K = 2 ^ n) (t : Fin n)
    {f g : K →+ K} {l m : Fin n → K} (hf : ∀ x, f x = ∑ i, l i * x ^ 2 ^ (i : ℕ))
    (hg : ∀ x, g x = ∑ i, m i * x ^ 2 ^ (i : ℕ)) (x : K) :
    g (x * x ^ 2 ^ (t : ℕ)) + f x * f x ^ 2 ^ (t : ℕ) =
      ∑ i, ∑ k, ((if k = i + t then m i else 0) + l i * l (k - t) ^ 2 ^ (t : ℕ)) *
        (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (k : ℕ)) := by
  have hshift := fun j => pow_two_pow_pow_two_pow hcard x j t
  have h1 : g (x * x ^ 2 ^ (t : ℕ)) = ∑ i, ∑ k, (if k = i + t then m i else 0) *
      (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (k : ℕ)) := by
    rw [hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [mul_pow, ← pow_mul, mul_comm (2 ^ (t : ℕ)), pow_mul, hshift]
  have h2 : f x ^ 2 ^ (t : ℕ) = ∑ j, l j ^ 2 ^ (t : ℕ) * x ^ 2 ^ ((j + t : Fin n) : ℕ) := by
    rw [hf, show (∑ i, l i * x ^ 2 ^ (i : ℕ)) ^ 2 ^ (t : ℕ) =
      frobPowHom K 2 t (∑ i, l i * x ^ 2 ^ (i : ℕ)) from (frobPowHom_apply _ _).symm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [frobPowHom_apply, mul_pow, hshift]
  have h3 : f x * f x ^ 2 ^ (t : ℕ) = ∑ i, ∑ k, l i * l (k - t) ^ 2 ^ (t : ℕ) *
      (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (k : ℕ)) := by
    rw [h2, hf, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun j => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  rw [h1, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Twisted

theorem twisted_product_quadratic_similarity_rigidity {K : Type*} [Field K] {n s : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hs : s < n) (h4s : ¬ n ∣ 4 * s) :
    (∀ f g : K →+ K, f ≠ 0 → (∀ x, g (x * x ^ 2 ^ s) = f x * f x ^ 2 ^ s) →
      ∃! p : Kˣ × Fin n, (∀ x, f x = p.1 * x ^ 2 ^ (p.2 : ℕ)) ∧
        ∀ x, g x = p.1 * (p.1 : K) ^ 2 ^ s * x ^ 2 ^ (p.2 : ℕ)) ∧
    ∀ (c : Kˣ) (i : Fin n), ∃ f g : K →+ K, (∀ x, f x = c * x ^ 2 ^ (i : ℕ)) ∧
      (∀ x, g x = c * (c : K) ^ 2 ^ s * x ^ 2 ^ (i : ℕ)) ∧
      (∀ x, g (x * x ^ 2 ^ s) = f x * f x ^ 2 ^ s) ∧
      Function.Bijective f ∧ Function.Bijective g := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have : NeZero n := ⟨by omega⟩
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hlt : 2 ^ (n - 1) < Fintype.card K := by
    rw [hcard]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨hlin, -⟩ := finite_field_linearized_map_bases Nat.prime_two hn hK
  obtain ⟨σ, hσ, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK
  have hσpow : ∀ (k : ℕ) (x : K), (σ ^ k) x = x ^ 2 ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', RingAut.mul_apply, ih, hσ, ← pow_mul, pow_succ]
  obtain ⟨S, rfl⟩ : ∃ S : Fin n, (S : ℕ) = s := ⟨⟨s, hs⟩, rfl⟩
  have hzero : ∀ {a : K}, a ^ 2 ^ (S : ℕ) = 0 → a = 0 := fun h =>
    (pow_eq_zero_iff (by positivity)).1 h
  refine ⟨fun f g hf0 hfg => ?_, fun c i => ?_⟩
  · obtain ⟨l, hl, -⟩ := hlin f
    obtain ⟨m, hm, -⟩ := hlin g
    have h4S : (S + S) + (S + S) ≠ 0 := by
      intro h
      apply h4s
      have hv := congrArg Fin.val h
      simp only [Fin.val_add, Fin.val_zero] at hv
      rw [← Nat.add_mod] at hv
      exact Nat.dvd_of_mod_eq_zero (by rw [show 4 * (S : ℕ) = S + S + (S + S) by ring]; exact hv)
    have hS0 : S ≠ 0 := fun h => h4S (by simp [h])
    have h2S : S + S ≠ 0 := fun h => h4S (by rw [h, add_zero])
    have hne1 : ∀ i : Fin n, i ≠ i + S := fun i h => hS0 (add_eq_left.1 h.symm)
    have hne2 : ∀ i : Fin n, i ≠ i + S + S := fun i h =>
      h2S (add_eq_left.1 (by rw [← add_assoc]; exact h.symm))
    have hC : ∀ x : K, ∑ i, ∑ k, ((if k = i + S then m i else 0) +
        l i * l (k - S) ^ 2 ^ (S : ℕ)) * (x ^ 2 ^ (i : ℕ) * x ^ 2 ^ (k : ℕ)) = 0 := fun x => by
      rw [← twisted_expansion hcard S hl hm x, hfg x, CharTwo.add_self_eq_zero]
    obtain ⟨hO, hD⟩ := coeff_eq_zero_of_forall_sum_sum_eq_zero hlt hC
    have F1 : ∀ i, l i * l (i - S) ^ 2 ^ (S : ℕ) = 0 := fun i => by
      have := hD i
      rwa [ite_eq_right (hne1 i), zero_add] at this
    have F2 : ∀ i k : Fin n, k ≠ i + S → i ≠ k + S →
        l i * l (k - S) ^ 2 ^ (S : ℕ) + l k * l (i - S) ^ 2 ^ (S : ℕ) = 0 :=
      fun i k h1 h2 => by
        have := hO i k
        rwa [ite_eq_right h1, ite_eq_right h2, zero_add, zero_add] at this
    have F3 : ∀ i : Fin n, m i + l i * l i ^ 2 ^ (S : ℕ) +
        l (i + S) * l (i - S) ^ 2 ^ (S : ℕ) = 0 := fun i => by
      have := hO i (i + S)
      rwa [ite_eq_left rfl, add_sub_cancel_right, ite_eq_right (hne2 i), zero_add] at this
    have hA : ∀ i j, l i ≠ 0 → l j ≠ 0 → j = i ∨ j = i - (S + S) := by
      intro i j hi hj
      by_contra hc
      push Not at hc
      have h1 : l (i - S) = 0 := hzero ((mul_eq_zero.1 (F1 i)).resolve_left hi)
      have h2 := F2 i (j + S) (fun h => hc.1 (add_right_cancel h))
        (fun h => hc.2 (eq_sub_of_add_eq (by rw [h, add_assoc])))
      rw [add_sub_cancel_right, h1, zero_pow (by positivity), mul_zero, add_zero] at h2
      exact hj (hzero ((mul_eq_zero.1 h2).resolve_left hi))
    obtain ⟨i₀, hi₀⟩ : ∃ i, l i ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (AddMonoidHom.ext fun x => by simp [hl x, h])
    have hB : ∀ j, l j ≠ 0 → j = i₀ := by
      intro j hj
      by_contra hji
      rcases hA i₀ j hi₀ hj with h | h
      · exact hji h
      rcases hA j i₀ hj hi₀ with h' | h'
      · exact hji h'.symm
      apply h4S
      rw [h, sub_sub] at h'
      exact sub_eq_self.1 h'.symm
    have hl' : ∀ j, l j = if j = i₀ then l i₀ else 0 := fun j => by
      by_cases hj : j = i₀
      · rw [ite_eq_left hj, hj]
      · rw [ite_eq_right hj]
        by_contra h
        exact hj (hB j h)
    have hm' : ∀ j, m j = if j = i₀ then l i₀ * l i₀ ^ 2 ^ (S : ℕ) else 0 := fun j => by
      have h3 := F3 j
      have h4 : l (j + S) * l (j - S) ^ 2 ^ (S : ℕ) = 0 := by
        by_cases ha : l (j + S) = 0
        · rw [ha, zero_mul]
        by_cases hb : l (j - S) = 0
        · rw [hb, zero_pow (by positivity), mul_zero]
        exfalso
        apply h2S
        have e : j + S + S = j := by rw [hB _ ha, ← hB _ hb, sub_add_cancel]
        rwa [add_assoc, add_eq_left] at e
      rw [h4, add_zero, hl' j] at h3
      by_cases hj : j = i₀
      · rw [ite_eq_left hj] at h3 ⊢
        exact (add_eq_zero_iff_eq_neg.1 h3).trans (CharTwo.neg_eq _)
      · rw [ite_eq_right hj, zero_mul, add_zero] at h3
        rw [ite_eq_right hj]
        exact h3
    have hfx : ∀ x, f x = l i₀ * x ^ 2 ^ (i₀ : ℕ) := fun x => by
      rw [hl x, Finset.sum_eq_single i₀ (fun j _ hj => by rw [hl' j, ite_eq_right hj, zero_mul])
        (by simp)]
    have hgx : ∀ x, g x = l i₀ * l i₀ ^ 2 ^ (S : ℕ) * x ^ 2 ^ (i₀ : ℕ) := fun x => by
      rw [hm x, Finset.sum_eq_single i₀ (fun j _ hj => by rw [hm' j, ite_eq_right hj, zero_mul])
        (by simp), hm' i₀, ite_eq_left rfl]
    refine ⟨(Units.mk0 (l i₀) hi₀, i₀), ⟨fun x => by rw [Units.val_mk0]; exact hfx x,
      fun x => by rw [Units.val_mk0]; exact hgx x⟩, ?_⟩
    rintro ⟨c, i⟩ ⟨hc1, -⟩
    have hrep : ∀ x, f x = ∑ j, (Pi.single i (c : K) : Fin n → K) j * x ^ 2 ^ (j : ℕ) :=
      fun x => by
        rw [hc1 x, Finset.sum_eq_single (f := fun j => (Pi.single i (c : K) : Fin n → K) j *
          x ^ 2 ^ (j : ℕ)) i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]) (by simp),
          Pi.single_eq_same]
    have hli : (Pi.single i (c : K) : Fin n → K) = l := (hlin f).unique hrep hl
    have hci : (c : K) = l i := by rw [← hli, Pi.single_eq_same]
    have hii : i = i₀ := hB i (by rw [← hci]; exact c.ne_zero)
    subst hii
    exact Prod.ext (Units.ext (by rw [hci, Units.val_mk0])) rfl
  · refine ⟨(c : K) • frobPowHom K 2 i, ((c : K) * (c : K) ^ 2 ^ (S : ℕ)) • frobPowHom K 2 i,
      fun x => by simp, fun x => by simp, fun x => ?_, ?_, ?_⟩
    · simp only [AddMonoidHom.smul_apply, frobPowHom_apply, smul_eq_mul]
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ (S : ℕ))]
      ring
    · have e : ⇑((c : K) • frobPowHom K 2 i) = ⇑(Units.mulLeft c) ∘ ⇑(σ ^ (i : ℕ)) :=
        funext fun x => by
          rw [Function.comp_apply, hσpow, Units.mulLeft_apply, AddMonoidHom.smul_apply,
            frobPowHom_apply, smul_eq_mul]
      rw [e]
      exact (Units.mulLeft c).bijective.comp (σ ^ (i : ℕ)).bijective
    · have e : ⇑(((c : K) * (c : K) ^ 2 ^ (S : ℕ)) • frobPowHom K 2 i) =
          ⇑(Units.mulLeft (c * c ^ 2 ^ (S : ℕ))) ∘ ⇑(σ ^ (i : ℕ)) :=
        funext fun x => by
          rw [Function.comp_apply, hσpow, Units.mulLeft_apply, AddMonoidHom.smul_apply,
            frobPowHom_apply, smul_eq_mul, Units.val_mul, Units.val_pow_eq_pow_val]
      rw [e]
      exact (Units.mulLeft _).bijective.comp (σ ^ (i : ℕ)).bijective

end CFSG.LocalAnalysis.ComponentInitial
