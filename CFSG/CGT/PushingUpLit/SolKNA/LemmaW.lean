module

public import CFSG.CGT.PushingUpLit.SolKNA.LemmaWArith
public import CFSG.CGT.PushingUpLit.SolKNA.LemmaWPoly

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open Polynomial

section

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem additive_eq_zero_of_inv_formula {a : ℕ} (ha : 1 ≤ a)
    (hcard : Fintype.card K = 2 ^ (2 * a + 1)) (h : K →+ K)
    (hfe : ∀ t : K, t ≠ 0 → h t = t ^ (2 ^ a) * h t⁻¹) (h1 : h 1 = 0) : ∀ t, h t = 0 := by
  classical
  obtain ⟨d, hd⟩ := exists_linearized hcard h
  set q1 := Fintype.card K - 1 with hq1
  have hP : 4 ≤ 2 ^ (2 * a) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1v : q1 = 2 * 2 ^ (2 * a) - 1 := by rw [hq1, hcard, pow_succ]; ring_nf
  have hlt : ∀ l : Fin (2 * a + 1), 2 ^ (l : ℕ) < q1 := fun l => by
    have : 2 ^ (l : ℕ) ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hae : 2 ^ a < q1 := by
    have : 2 ^ a ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hpowmod : ∀ t : K, t ≠ 0 → ∀ n : ℕ, t ^ (n % q1) = t ^ n := by
    intro t ht n
    conv_rhs => rw [← Nat.mod_add_div n q1]
    rw [pow_add, pow_mul, hq1, FiniteField.pow_card_sub_one_eq_one t ht, one_pow, mul_one]
  let f : Fin (2 * a + 1) → ℕ := fun l => (2 ^ a + q1 - 2 ^ (l : ℕ)) % q1
  have hf : ∀ t : K, t ≠ 0 → ∀ l : Fin (2 * a + 1),
      t ^ (2 ^ a) * (t⁻¹) ^ (2 ^ (l : ℕ)) = t ^ f l := by
    intro t ht l
    have hl := hlt l
    have h2a := Nat.two_pow_pos a
    have h2l := Nat.two_pow_pos (l : ℕ)
    have hn : t ^ (2 ^ a + q1 - 2 ^ (l : ℕ)) * t ^ (2 ^ (l : ℕ)) = t ^ (2 ^ a) := by
      rw [← pow_add, show 2 ^ a + q1 - 2 ^ (l : ℕ) + 2 ^ (l : ℕ) = 2 ^ a + q1 by omega, pow_add,
        hq1, FiniteField.pow_card_sub_one_eq_one t ht, mul_one]
    show _ = t ^ ((2 ^ a + q1 - 2 ^ (l : ℕ)) % q1)
    rw [hpowmod t ht]
    calc t ^ (2 ^ a) * (t⁻¹) ^ (2 ^ (l : ℕ))
        = t ^ (2 ^ a + q1 - 2 ^ (l : ℕ)) * t ^ (2 ^ (l : ℕ)) * (t⁻¹) ^ (2 ^ (l : ℕ)) := by rw [hn]
      _ = t ^ (2 ^ a + q1 - 2 ^ (l : ℕ)) := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ ht, one_pow, mul_one]
  have hs : (Finset.univ.erase (0 : K)).card = q1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hpoly : expPoly (2 * a + 1) d (fun l => 2 ^ (l : ℕ)) = expPoly (2 * a + 1) d f := by
    refine eq_of_eval_expPoly d _ f (Finset.univ.erase 0) (fun l => by rw [hs]; exact hlt l)
      (fun l => by rw [hs]; exact Nat.mod_lt _ (by omega)) fun t ht => ?_
    have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
    rw [← hd t, hfe t ht0, hd t⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_left_comm, hf t ht0 l]
  have hd0 : ∀ l₀ : Fin (2 * a + 1), (l₀ : ℕ) ≠ a - 1 → d l₀ = 0 := by
    intro l₀ hl₀
    have hc : (expPoly (2 * a + 1) d fun l => 2 ^ (l : ℕ)).coeff (2 ^ (l₀ : ℕ)) =
        (expPoly (2 * a + 1) d f).coeff (2 ^ (l₀ : ℕ)) := by rw [hpoly]
    rw [expPoly_coeff_two_pow, expPoly_coeff] at hc
    rw [hc]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases heq : 2 ^ (l₀ : ℕ) = f l
    · exfalso
      apply hl₀
      have hq1' : q1 = 2 ^ (2 * a + 1) - 1 := by rw [hq1, hcard]
      have hl' := hlt l
      have h2a := Nat.two_pow_pos a
      have h2l := Nat.two_pow_pos (l : ℕ)
      have heq' : 2 ^ (l₀ : ℕ) = (2 ^ a + q1 - 2 ^ (l : ℕ)) % q1 := heq
      have hmod : (2 ^ (l₀ : ℕ) + 2 ^ (l : ℕ)) % q1 = 2 ^ a % q1 := by
        rw [heq', Nat.mod_add_mod,
          show 2 ^ a + q1 - 2 ^ (l : ℕ) + 2 ^ (l : ℕ) = 2 ^ a + q1 by omega, Nat.add_mod_right]
      rw [hq1'] at hmod
      exact (two_pow_add_two_pow_modEq ha l₀.2 l.2 hmod).1
    · simp [heq]
  have hd1 : ∀ l : Fin (2 * a + 1), d l = 0 := by
    intro l
    by_cases hl : (l : ℕ) = a - 1
    · have h1' : h 1 = ∑ l' : Fin (2 * a + 1), d l' := by simp [hd 1]
      have hsum : ∑ l' : Fin (2 * a + 1), d l' = d l := by
        refine Finset.sum_eq_single l (fun l' _ hne => hd0 l' ?_) (by simp)
        intro h'
        exact hne (Fin.ext (h'.trans hl.symm))
      rw [h1, hsum] at h1'
      exact h1'.symm
    · exact hd0 l hl
  intro t
  rw [hd t]
  exact Finset.sum_eq_zero fun l _ => by rw [hd1 l, zero_mul]

theorem weight_lemma_field {a : ℕ} (ha : 1 ≤ a) (hcard : Fintype.card K = 2 ^ (2 * a + 1))
    (c : K → K → K) (h₁ : ∀ b b' b'', c (b + b') b'' = c b b'' + c b' b'')
    (h₂ : ∀ b b' b'', c b (b' + b'') = c b b' + c b b'') (halt : ∀ b, c b b = 0)
    (hequiv : ∀ x : K, x ≠ 0 → ∀ b b',
      c (x ^ (1 + 2 ^ (a + 1)) * b) (x ^ (1 + 2 ^ (a + 1)) * b') = x ^ (1 + 2 ^ a) * c b b') :
    ∀ b b', c b b' = 0 := by
  have hu : ∀ u : K, u ≠ 0 → ∀ b b', c (u * b) (u * b') = u ^ (2 ^ a) * c b b' := by
    intro u hu0 b b'
    obtain ⟨x, hx0, hx1, hx2⟩ := exists_unit_pow_eq hcard hu0
    have := hequiv x hx0 b b'
    rwa [hx1, hx2] at this
  have hsymm : ∀ b b', c b b' = c b' b := by
    intro b b'
    have h0 := halt (b + b')
    simp only [h₁, h₂, halt] at h0
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h0 - (c b' b) * h2
  let h : K →+ K := AddMonoidHom.mk' (fun t => c t 1) (fun x y => h₁ x y 1)
  have hform : ∀ b b' : K, b' ≠ 0 → c b b' = b' ^ (2 ^ a) * h (b / b') := by
    intro b b' hb'
    have e : b' * (b / b') = b := by field_simp
    have := hu b' hb' (b / b') 1
    rwa [e, mul_one] at this
  have hfe : ∀ t : K, t ≠ 0 → h t = t ^ (2 ^ a) * h t⁻¹ := by
    intro t ht
    have h1 := hform 1 t ht
    show c t 1 = t ^ (2 ^ a) * h t⁻¹
    rw [hsymm t 1, h1, one_div]
  have hz := additive_eq_zero_of_inv_formula ha hcard h hfe (halt 1)
  intro b b'
  by_cases hb' : b' = 0
  · subst hb'
    simpa using h₂ b 0 0
  · rw [hform b b' hb', hz, mul_zero]

end

end CFSG.CGT.PushingUpLit.SolKNA
