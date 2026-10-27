module

public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing
import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace AnchoredPrimeArray

open ComplexConjugate
open scoped ComplexOrder

theorem sum_ite_eq_add {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α) (c d : ℤ) :
    ∑ a : α, (if a = a₀ then c else d) = c + ((Fintype.card α : ℤ) - 1) * d := by
  have hc : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a₀⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a₀), if_pos rfl,
    Finset.sum_congr rfl (fun a ha => if_neg (Finset.ne_of_mem_erase ha)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ,
    nsmul_eq_mul, Nat.cast_sub hc]
  push_cast
  ring

theorem sum_pattern {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (i₀ : ι) (j₀ : κ) (u v w z : ℤ) :
    ∑ k : ι × κ, (if k.1 = i₀ then (if k.2 = j₀ then u else v) else
        (if k.2 = j₀ then w else z))
      = (u + ((Fintype.card κ : ℤ) - 1) * v) + ((Fintype.card ι : ℤ) - 1) *
        (w + ((Fintype.card κ : ℤ) - 1) * z) := by
  rw [Fintype.sum_prod_type]
  rw [show (∑ i : ι, ∑ j : κ, (if i = i₀ then (if j = j₀ then u else v) else
      (if j = j₀ then w else z)))
      = ∑ i : ι, (if i = i₀ then u + ((Fintype.card κ : ℤ) - 1) * v
        else w + ((Fintype.card κ : ℤ) - 1) * z) from
    Finset.sum_congr rfl fun i _ => by
      by_cases hi : i = i₀
      · simp only [hi, if_true]
        exact sum_ite_eq_add j₀ u v
      · simp only [hi, if_false]
        exact sum_ite_eq_add j₀ w z]
  rw [sum_ite_eq_add i₀]

theorem cases_of_le {q p S T : ℤ} (hq : 3 ≤ q) (hp : 3 ≤ p)
    (h : 1 + (p - 1) * T ^ 2 + (q - 1) * (S ^ 2 + (p - 1) * (S + T - 1) ^ 2) ≤ q) :
    (S = 1 ∧ T = 0) ∨ (S = 0 ∧ T = 1 ∧ p ≤ q) := by
  have hsq : ∀ x : ℤ, x ≠ 0 → 1 ≤ x ^ 2 := fun x hx => by
    nlinarith [Int.one_le_abs hx, sq_abs x, abs_nonneg x]
  have h' : 1 + (p - 1) * T ^ 2 + (q - 1) * S ^ 2
      + (q - 1) * ((p - 1) * (S + T - 1) ^ 2) ≤ q := by nlinarith
  have hT0 : 0 ≤ (p - 1) * T ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hS0 : 0 ≤ (q - 1) * S ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hr : S + T - 1 = 0 := by
    by_contra hne
    have h1 := hsq _ hne
    have hA : 2 ≤ (p - 1) * (S + T - 1) ^ 2 := by nlinarith
    have hB : 2 * (q - 1) ≤ (q - 1) * ((p - 1) * (S + T - 1) ^ 2) := by nlinarith
    linarith
  rw [hr] at h'
  norm_num at h'
  have hSor : S = 0 ∨ S = 1 := by
    by_contra hcon
    have hSne : S ≠ 0 := fun h0 => hcon (Or.inl h0)
    have hTne : T ≠ 0 := fun h0 => hcon (Or.inr (by omega))
    have h1 : 1 ≤ S ^ 2 := hsq S hSne
    have h2 : 1 ≤ T ^ 2 := hsq T hTne
    nlinarith
  rcases hSor with h0 | h1
  · subst h0
    have hT : T = 1 := by omega
    subst hT
    refine Or.inr ⟨rfl, rfl, by nlinarith⟩
  · exact Or.inl ⟨h1, by omega⟩

variable {G : Type*} [Group G] [Fintype G]

theorem sum_sq_lt_of_sub_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → G → ℂ}
    {ψ : G → ℂ} {n : ι → ℤ} {N : ℤ}
    (hηmem : ∀ k, η k ∈ Submodule.span ℤ (Irr G)) (hη : IsOrthonormalFamily η)
    (hψ : ψ ∈ Submodule.span ℤ (Irr G)) (hn : ∀ k, cfInner ψ (η k) = (n k : ℂ))
    (hN : cfInner ψ ψ = (N : ℂ))
    (hne : ψ - ∑ k, cfInner ψ (η k) • η k ≠ 0) :
    ∑ k, n k ^ 2 < N := by
  have hXmem : (∑ k, cfInner ψ (η k) • η k) ∈ Submodule.span ℤ (Irr G) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hn k, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hηmem k)
  have hsub : (ψ - ∑ k, cfInner ψ (η k) • η k) ∈ Submodule.span ℤ (Irr G) :=
    Submodule.sub_mem _ hψ hXmem
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hsub hsub
  have hpyth := CauchySchwarzProjection.classFunInner_self_eq_add_of_inner_eq
    (η := η) (fun k l => by rw [← cfInner_eq_classFunInner]; exact hη.cfInner_eq_ite k l)
    ψ (fun k => cfInner ψ (η k)) (fun k => (cfInner_eq_classFunInner _ _).symm)
  simp only [← cfInner_eq_classFunInner] at hpyth
  have hsum : ∑ k, cfInner ψ (η k) * conj (cfInner ψ (η k)) = ((∑ k, n k ^ 2 : ℤ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hn k, map_intCast]
    ring
  rw [hsum, hN, hm] at hpyth
  have hcast : N = (∑ k, n k ^ 2) + m := by exact_mod_cast hpyth
  have hm0 : (0 : ℂ) ≤ (m : ℂ) := hm ▸ cfInner_self_nonneg _
  have hm0' : 0 ≤ m := by exact_mod_cast hm0
  have hmne : m ≠ 0 := by
    intro h0
    have : Nonempty G := ⟨1⟩
    exact hne (cfInner_self_eq_zero.mp (by rw [hm, h0]; simp))
  omega

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Group G] [DecidableEq ι] in
theorem sum_smul_eq_sum_col {η : ι × κ → G → ℂ} {ψ : G → ℂ} {a : ι × κ → ℤ} {j₀ : κ}
    (ha : ∀ k, cfInner ψ (η k) = (a k : ℂ))
    (h : ∀ k : ι × κ, a k = if k.2 = j₀ then 1 else 0) :
    ∑ k : ι × κ, cfInner ψ (η k) • η k = ∑ i : ι, η (i, j₀) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem j₀ (Finset.mem_univ j₀)]
  · rw [ha (i, j₀), h (i, j₀)]
    simp
  · intro j _ hj
    rw [ha (i, j), h (i, j), if_neg hj]
    simp

omit [Group G] [DecidableEq κ] in
theorem sum_smul_eq_sum_row {η : ι × κ → G → ℂ} {ψ : G → ℂ} {a : ι × κ → ℤ} {i₀ : ι}
    (ha : ∀ k, cfInner ψ (η k) = (a k : ℂ))
    (h : ∀ k : ι × κ, a k = if k.1 = i₀ then 1 else 0) :
    ∑ k : ι × κ, cfInner ψ (η k) • η k = ∑ j : κ, η (i₀, j) := by
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
  · rw [ha (i₀, j), h (i₀, j)]
    simp
  · intro i _ hi
    rw [ha (i, j), h (i, j), if_neg hi]
    simp

theorem eq_col_sum_or_eq_row_sum {η : ι × κ → G → ℂ} {ψ : G → ℂ} {s t : ℂ} {i₀ : ι} {j₀ : κ}
    (hq : 3 ≤ Fintype.card ι) (hp : 3 ≤ Fintype.card κ)
    (hηmem : ∀ k, η k ∈ Submodule.span ℤ (Irr G)) (hη : IsOrthonormalFamily η)
    (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (hnorm : cfInner ψ ψ = (Fintype.card ι : ℂ) + 1)
    (h00 : cfInner ψ (η (i₀, j₀)) = 1)
    (hadd : ∀ i j, cfInner ψ (η (i, j))
      = cfInner ψ (η (i, j₀)) + cfInner ψ (η (i₀, j)) - 1)
    (hs : ∀ i, i ≠ i₀ → cfInner ψ (η (i, j₀)) = s)
    (ht : ∀ j, j ≠ j₀ → cfInner ψ (η (i₀, j)) = t)
    (hrem : ψ - ∑ k, cfInner ψ (η k) • η k ≠ 0) :
    (∑ k, cfInner ψ (η k) • η k = ∑ i, η (i, j₀)) ∨
      (∑ k, cfInner ψ (η k) • η k = ∑ j, η (i₀, j) ∧
        Fintype.card κ ≤ Fintype.card ι) := by
  classical
  choose a ha using fun k => exists_int_cfInner_of_mem_span_Irr hψ (hηmem k)
  obtain ⟨i₁, hi₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i₀
  obtain ⟨j₁, hj₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j₀
  set S := a (i₁, j₀) with hS
  set T := a (i₀, j₁) with hT
  have hsS : s = (S : ℂ) := (hs i₁ hi₁).symm.trans (ha _)
  have htT : t = (T : ℂ) := (ht j₁ hj₁).symm.trans (ha _)
  have hpat : ∀ k : ι × κ, a k = if k.1 = i₀ then (if k.2 = j₀ then 1 else T)
      else (if k.2 = j₀ then S else S + T - 1) := by
    rintro ⟨i, j⟩
    have key : ((a (i, j) : ℂ)) = ((if i = i₀ then (if j = j₀ then 1 else T)
        else (if j = j₀ then S else S + T - 1) : ℤ) : ℂ) := by
      rw [← ha (i, j)]
      by_cases hi : i = i₀ <;> by_cases hj : j = j₀
      · subst hi; subst hj; simpa using h00
      · subst hi; rw [ht j hj, htT]; simp [hj]
      · subst hj; rw [hs i hi, hsS]; simp [hi]
      · rw [hadd i j, hs i hi, ht j hj, hsS, htT]; push_cast [hi, hj]; ring
    exact_mod_cast key
  have hNc : cfInner ψ ψ = (((Fintype.card ι : ℤ) + 1 : ℤ) : ℂ) := by rw [hnorm]; push_cast; ring
  have hlt := sum_sq_lt_of_sub_ne_zero hηmem hη hψ ha hNc hrem
  have hsumsq : ∑ k : ι × κ, a k ^ 2
      = (1 + ((Fintype.card κ : ℤ) - 1) * T ^ 2) + ((Fintype.card ι : ℤ) - 1) *
        (S ^ 2 + ((Fintype.card κ : ℤ) - 1) * (S + T - 1) ^ 2) := by
    rw [← sum_pattern i₀ j₀ 1 (T ^ 2) (S ^ 2) ((S + T - 1) ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hpat k]
    by_cases hi : k.1 = i₀ <;> by_cases hj : k.2 = j₀ <;> simp [hi, hj]
  have hbound : 1 + ((Fintype.card κ : ℤ) - 1) * T ^ 2
      + ((Fintype.card ι : ℤ) - 1) * (S ^ 2 + ((Fintype.card κ : ℤ) - 1) * (S + T - 1) ^ 2)
      ≤ (Fintype.card ι : ℤ) := by rw [← hsumsq] at *; omega
  rcases cases_of_le (q := (Fintype.card ι : ℤ)) (p := (Fintype.card κ : ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hp) hbound with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl (sum_smul_eq_sum_col ha fun k => ?_)
    rw [hpat k, h1, h2]
    by_cases hi : k.1 = i₀ <;> by_cases hj : k.2 = j₀ <;> simp [hi, hj]
  · refine Or.inr ⟨sum_smul_eq_sum_row ha fun k => ?_, by exact_mod_cast h3⟩
    rw [hpat k, h1, h2]
    by_cases hi : k.1 = i₀ <;> by_cases hj : k.2 = j₀ <;> simp [hi, hj]

theorem card_lt_of_ne_col_sum {η : ι × κ → G → ℂ} {ψ : G → ℂ} {s t : ℂ} {i₀ : ι} {j₀ : κ}
    (hq : 3 ≤ Fintype.card ι) (hp : 3 ≤ Fintype.card κ)
    (hηmem : ∀ k, η k ∈ Submodule.span ℤ (Irr G)) (hη : IsOrthonormalFamily η)
    (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (hnorm : cfInner ψ ψ = (Fintype.card ι : ℂ) + 1)
    (h00 : cfInner ψ (η (i₀, j₀)) = 1)
    (hadd : ∀ i j, cfInner ψ (η (i, j))
      = cfInner ψ (η (i, j₀)) + cfInner ψ (η (i₀, j)) - 1)
    (hs : ∀ i, i ≠ i₀ → cfInner ψ (η (i, j₀)) = s)
    (ht : ∀ j, j ≠ j₀ → cfInner ψ (η (i₀, j)) = t)
    (hrem : ψ - ∑ k, cfInner ψ (η k) • η k ≠ 0)
    (hcol : ∑ k, cfInner ψ (η k) • η k ≠ ∑ i, η (i, j₀))
    (hne : Fintype.card κ ≠ Fintype.card ι) :
    Fintype.card κ < Fintype.card ι := by
  rcases eq_col_sum_or_eq_row_sum hq hp hηmem hη hψ hnorm h00 hadd hs ht hrem with h | ⟨-, h⟩
  · exact absurd h hcol
  · omega

theorem eq_col_sum_or_eq_row_sum_fin {q p : ℕ} (hq : 3 ≤ q) (hp : 3 ≤ p)
    {η : Fin q × Fin p → G → ℂ} {ψ : G → ℂ} {s t : ℂ}
    (hηmem : ∀ k, η k ∈ Submodule.span ℤ (Irr G)) (hη : IsOrthonormalFamily η)
    (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (hnorm : cfInner ψ ψ = (q : ℂ) + 1)
    (h00 : cfInner ψ (η (⟨0, by omega⟩, ⟨0, by omega⟩)) = 1)
    (hadd : ∀ i j, cfInner ψ (η (i, j)) = cfInner ψ (η (i, ⟨0, by omega⟩))
      + cfInner ψ (η (⟨0, by omega⟩, j)) - 1)
    (hs : ∀ i, i ≠ ⟨0, by omega⟩ → cfInner ψ (η (i, ⟨0, by omega⟩)) = s)
    (ht : ∀ j, j ≠ ⟨0, by omega⟩ → cfInner ψ (η (⟨0, by omega⟩, j)) = t)
    (hrem : ψ - ∑ k, cfInner ψ (η k) • η k ≠ 0) :
    (∑ k, cfInner ψ (η k) • η k = ∑ i, η (i, ⟨0, by omega⟩)) ∨
      (∑ k, cfInner ψ (η k) • η k = ∑ j, η (⟨0, by omega⟩, j) ∧ p ≤ q) := by
  have h := eq_col_sum_or_eq_row_sum (i₀ := (⟨0, by omega⟩ : Fin q))
    (j₀ := (⟨0, by omega⟩ : Fin p)) (s := s) (t := t)
    (by simpa using hq) (by simpa using hp) hηmem hη hψ (by simpa using hnorm) h00 hadd hs ht hrem
  simpa using h

end AnchoredPrimeArray

end CFSG.FeitThompson
