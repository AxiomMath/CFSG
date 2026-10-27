module

public import CFSG.LieType.SeitzGeneration.SingerUCayley
public import CFSG.LieType.SeitzGeneration.SingerUNorms

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Fin.NatCast Fin.CommRing

section Basic

variable {f : ℕ} {K : Type} [Field K]

theorem singerUF_two_eq_zero (h : UnitaryFieldData 2 f K) : (2 : K) = 0 := by
  haveI := h.charP
  exact_mod_cast CharP.cast_eq_zero K 2

theorem singerUF_neg_one_eq (h : UnitaryFieldData 2 f K) : (-1 : K) = 1 := by
  linear_combination -singerUF_two_eq_zero h

theorem singerUF_bar_eq_inv (h : UnitaryFieldData 2 f K) {c : K} (hcu : h.bar c * c = 1) :
    h.bar c = c⁻¹ :=
  eq_inv_of_mul_eq_one_left hcu

theorem singerUF_norm_one_of_pow (h : UnitaryFieldData 2 f K) {p : ℕ} (hpq : 2 ^ f + 1 = p)
    {x : K} (hx : x ^ p = 1) : h.bar x * x = 1 := by
  rw [h.bar_apply, ← pow_succ, hpq, hx]

theorem singerUF_pow_p (h : UnitaryFieldData 2 f K) {p : ℕ} (hpq : 2 ^ f + 1 = p) {ε : K}
    (hεb : h.bar ε = ε) : ε ^ p = ε ^ 2 := by
  rw [← hpq, pow_succ, ← h.bar_apply, hεb, sq]

theorem singerUF_exists_eps (h : UnitaryFieldData 2 f K) {c : K} (hcu : h.bar c * c = 1) :
    ∃ ε : K, ε ^ 2 = (c + c⁻¹)⁻¹ ∧ h.bar ε = ε := by
  have h2 := singerUF_two_eq_zero h
  have hbc := singerUF_bar_eq_inv h hcu
  have hbρ : h.bar (c + c⁻¹) = c + c⁻¹ := by
    rw [map_add, map_inv₀, hbc, inv_inv, add_comm]
  have hbr : h.bar (c + c⁻¹)⁻¹ = (c + c⁻¹)⁻¹ := by
    rw [map_inv₀, hbρ]
  have hf : 2 ^ (f - 1) * 2 = 2 ^ f := by
    have := h.one_le
    rw [← pow_succ]
    congr 1
    omega
  have hsq : (((c + c⁻¹)⁻¹) ^ 2 ^ (f - 1)) ^ 2 = (c + c⁻¹)⁻¹ := by
    rw [← pow_mul, hf, ← h.bar_apply, hbr]
  refine ⟨((c + c⁻¹)⁻¹) ^ 2 ^ (f - 1), hsq, ?_⟩
  set ε := ((c + c⁻¹)⁻¹) ^ 2 ^ (f - 1) with hε
  have hsqb : (h.bar ε) ^ 2 = ε ^ 2 := by
    rw [← map_pow, hsq, hbr]
  have hsum : (h.bar ε + ε) ^ 2 = 0 := by
    linear_combination hsqb + (ε ^ 2 + h.bar ε * ε) * h2
  have h0 : h.bar ε + ε = 0 := (pow_eq_zero_iff two_ne_zero).mp hsum
  linear_combination h0 - ε * h2

theorem singerUF_rho_ne_zero (h : UnitaryFieldData 2 f K) {c : K} (hc : c ≠ 0) (hc1 : c ≠ 1) :
    c + c⁻¹ ≠ 0 := by
  intro hs
  have h2 := singerUF_two_eq_zero h
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hsq : (c + 1) ^ 2 = 0 := by linear_combination c * hs - hcc + c * h2
  have h1 : c + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  exact hc1 (by linear_combination h1 - h2)

theorem singerUF_rho_ne_one (h : UnitaryFieldData 2 f K) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {c : K} (hc : c ≠ 0) (hpc : c ^ p = 1) (hc1 : c ≠ 1) : c + c⁻¹ ≠ 1 := by
  intro hs
  have h2 := singerUF_two_eq_zero h
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hq : c ^ 2 + c + 1 = 0 := by linear_combination c * hs - hcc + c * h2
  have h3 : c ^ 3 = 1 := by linear_combination (c - 1) * hq
  have hd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [orderOf_eq_prime hpc hc1] at hd
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp hd)

theorem singerUF_rel {c ε : K} (hc : c ≠ 0) (hρ : c + c⁻¹ ≠ 0) (hε : ε ^ 2 = (c + c⁻¹)⁻¹) :
    ε ^ 2 * (c ^ 2 + 1) = c := by
  have h1 : (c + c⁻¹) * ε ^ 2 = 1 := by rw [hε, mul_inv_cancel₀ hρ]
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  linear_combination c * h1 - ε ^ 2 * hcc

theorem singerUF_E0_ne (h : UnitaryFieldData 2 f K) {c ε : K} (hc : c ≠ 0) (hρ : c + c⁻¹ ≠ 0)
    (hε : ε ^ 2 = (c + c⁻¹)⁻¹) : ε ^ 2 + c ≠ 0 := by
  intro h0
  have h2 := singerUF_two_eq_zero h
  have h1 : (c + c⁻¹) * ε ^ 2 = 1 := by rw [hε, mul_inv_cancel₀ hρ]
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hεc : ε ^ 2 = c := by linear_combination h0 - c * h2
  have hc2 : c ^ 2 = 0 := by
    rw [hεc] at h1
    linear_combination h1 - hcc
  exact hc (pow_eq_zero_iff two_ne_zero |>.mp hc2)


theorem singerUF_odd (h : UnitaryFieldData 2 f K) {p : ℕ} (hpq : 2 ^ f + 1 = p) : Odd p := by
  have hf := h.one_le
  have h2f : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  exact ⟨2 ^ (f - 1), by omega⟩

theorem singerUF_three_le (h : UnitaryFieldData 2 f K) {p : ℕ} (hpq : 2 ^ f + 1 = p) :
    3 ≤ p := by
  have hf := h.one_le
  have : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem singerUF_norm_bar (h : UnitaryFieldData 2 f K) (x : K) : h.norm (h.bar x) = h.norm x := by
  simp only [UnitaryFieldData.norm, h.bar_bar, mul_comm]

section Cayley

theorem singerUF_cayley_zero_zero (h : UnitaryFieldData 2 f K) {p : ℕ} [hp : Fact p.Prime]
    (hpq : 2 ^ f + 1 = p) {c ε : K} (hc : c ≠ 0) (hεb : h.bar ε = ε) (hE : ε ^ 2 + c ≠ 0) :
    thmU_cayleyMat h p c ε 0 0 = c * ((1 + ε ^ 2) / (ε ^ 2 + c)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h2 := singerUF_two_eq_zero h
  have hodd := singerUF_odd h hpq
  have hp3 := singerUF_three_le h hpq
  have hE' : h.bar ε ^ p + c ≠ 0 := by
    rw [hεb, singerUF_pow_p h hpq hεb]
    exact hE
  rw [thmU_cayleyMat_apply_zero h hodd hp3 hc hE' 0, if_pos (Fin.val_zero (n := p))]
  rw [hεb, singerUF_pow_p h hpq hεb]
  have hnum : 1 - ε * ε = 1 + ε ^ 2 := by linear_combination (-(ε ^ 2)) * h2
  rw [hnum, mul_div_assoc]

theorem singerUF_cayley_hi (h : UnitaryFieldData 2 f K) {p : ℕ} [hp : Fact p.Prime]
    (hpq : 2 ^ f + 1 = p) {c ε : K} (hc : c ≠ 0) (hεb : h.bar ε = ε) (hE : ε ^ 2 + c ≠ 0)
    (k : Fin p) (hk : 2 ≤ (k : ℕ)) :
    thmU_cayleyMat h p c ε k 0 = ε ^ (p - (k : ℕ)) * ((1 + ε ^ 2) / (ε ^ 2 + c)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h2 := singerUF_two_eq_zero h
  have hodd := singerUF_odd h hpq
  have hp3 := singerUF_three_le h hpq
  have hE' : h.bar ε ^ p + c ≠ 0 := by
    rw [hεb, singerUF_pow_p h hpq hεb]
    exact hE
  rw [thmU_cayleyMat_apply_zero h hodd hp3 hc hE' k,
    if_neg (show ¬ ((k : ℕ) = 0) by omega), if_neg (show ¬ ((k : ℕ) = 1) by omega),
    hεb, singerUF_pow_p h hpq hεb, singerUF_neg_one_eq h, one_pow, one_mul]
  have hnum : 1 - ε * ε = 1 + ε ^ 2 := by linear_combination (-(ε ^ 2)) * h2
  rw [hnum, mul_div_assoc]

end Cayley

theorem singerUF_entry {p : ℕ} [NeZero p] {c : K} {g : Matrix (Fin p) (Fin p) K}
    (hg : g * companionMat p c = companionMat p c * g) (i k : ℕ) (hi : i < p) (hk : k < p) :
    g (i : Fin p) (k : Fin p) =
      if k ≤ i then g ((i - k : ℕ) : Fin p) 0 else c * g ((i + p - k : ℕ) : Fin p) 0 := by
  have key := thmU_commute_companion_entry c hg (i : Fin p) (k : Fin p)
  have hiv : ((i : Fin p) : ℕ) = i := Fin.val_cast_of_lt hi
  have hkv : ((k : Fin p) : ℕ) = k := Fin.val_cast_of_lt hk
  have hcol : ∀ x : Fin p, (g *ᵥ Pi.single 0 1) x = g x 0 := fun x => by
    rw [mulVec_single_one, col_apply]
  rw [key]
  have hval := thmU_val_sub_natCast ((i : ℕ) : Fin p) hk
  rw [hiv] at hval
  by_cases hki : k ≤ i
  · have e1 : (i : Fin p) - (k : Fin p) = ((i - k : ℕ) : Fin p) := by
      apply Fin.ext
      rw [hval, if_pos hki, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [hiv, hkv, if_pos hki, hcol, e1]
  · have e2 : (i : Fin p) - (k : Fin p) = ((i + p - k : ℕ) : Fin p) := by
      apply Fin.ext
      rw [hval, if_neg hki, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [hiv, hkv, if_neg hki, hcol, e2]

theorem singerUF_norm_entry (h : UnitaryFieldData 2 f K) {p : ℕ} [NeZero p] {c : K}
    (hcu : h.bar c * c = 1) {g : Matrix (Fin p) (Fin p) K}
    (hg : g * companionMat p c = companionMat p c * g) (i j : Fin p) :
    h.norm (g i j) = h.norm (g (i - j) 0) := by
  have hnc : h.norm c = 1 := by rw [UnitaryFieldData.norm, mul_comm]; exact hcu
  have key := thmU_commute_companion_entry c hg i j
  have hcol : ∀ x : Fin p, (g *ᵥ Pi.single 0 1) x = g x 0 := fun x => by
    rw [mulVec_single_one, col_apply]
  rw [key, hcol]
  split_ifs
  · rfl
  · rw [singerU_norm_mul, hnc, one_mul]

end Basic

section Reflection

variable {f : ℕ} {K : Type} [Field K]

theorem singerUF_reflection_of_monomial (h : UnitaryFieldData 2 f K) {p : ℕ} [hp : Fact p.Prime]
    {c : K} (hcu : h.bar c * c = 1) (hodd : Odd (orderOf c)) (hgt : 3 < orderOf c)
    (b : Matrix (Fin p) (Fin p) K) (hbu : (b.map h.bar)ᵀ * b = 1)
    (hbC : b * companionMat p c = companionMat p c * b)
    (s t : Fin p → K) (hs : ∀ j, h.bar (s j) * s j = 1)
    (hta : t 0 = c) (htne : ∀ i, i ≠ 0 → t i ≠ c)
    (htc : ∀ i, (t i - c) * (t i - c⁻¹) * (t i - 1) = 0)
    (hmono : IsMonomialMat ((b * diagonal s * b)⁻¹ * diagonal t * (b * diagonal s * b))) :
    ∃ r : Fin p, ∀ j : Fin p, h.norm (b j 0) = h.norm (b (r - j) 0) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hbdet : IsUnit b.det := Matrix.isUnit_det_of_left_inverse hbu
  have hsne : ∀ j, s j ≠ 0 := fun j h0 => by
    have := hs j
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hsdet : IsUnit (diagonal s).det := by
    rw [det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => hsne j)
  have hyu : IsUnit (b * diagonal s * b).det := by
    rw [det_mul, det_mul]
    exact (hbdet.mul hsdet).mul hbdet
  have hyi : (b * diagonal s * b)⁻¹ * (b * diagonal s * b) = 1 := nonsing_inv_mul _ hyu
  have hy : (b * diagonal s * b) * (b * diagonal s * b)⁻¹ = 1 := mul_nonsing_inv _ hyu
  obtain ⟨a, ha⟩ := singerU_monomial_conj_column hodd hgt _ _ hyi hy t 0 hta
    (fun i hi => htne i hi) htc hmono
  set y : Matrix (Fin p) (Fin p) K := b * diagonal s * b with hy_def
  have hcolY : ∀ i, y i a * y⁻¹ a 0 = if i = 0 then 1 else 0 := by
    intro i
    have e := congrFun (congrFun hy i) 0
    rw [mul_apply, Finset.sum_eq_single a] at e
    · rw [one_apply] at e
      exact e
    · intro k _ hk
      rw [ha k hk, mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ a) h'
  have hμ0 : y⁻¹ a 0 ≠ 0 := by
    intro h0
    have := hcolY 0
    rw [h0, mul_zero, if_pos rfl] at this
    exact zero_ne_one this
  have hya : ∀ k, y k a = if k = 0 then (y⁻¹ a 0)⁻¹ else 0 := by
    intro k
    have := hcolY k
    by_cases hk : k = 0
    · rw [if_pos hk] at this ⊢
      exact eq_inv_of_mul_eq_one_left this
    · rw [if_neg hk] at this ⊢
      exact (mul_eq_zero.mp this).resolve_right hμ0
  have hM : (b.map h.bar)ᵀ * y = diagonal s * b := by
    calc (b.map h.bar)ᵀ * y = ((b.map h.bar)ᵀ * b) * diagonal s * b := by
          rw [hy_def]
          simp only [Matrix.mul_assoc]
      _ = diagonal s * b := by rw [hbu, Matrix.one_mul]
  have hsa : ∀ i, s i * b i a = (y⁻¹ a 0)⁻¹ * (b.map h.bar)ᵀ i 0 := by
    intro i
    have e := congrFun (congrFun hM i) a
    rw [mul_apply, diagonal_mul] at e
    simp only [hya, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
    rw [← e, mul_comm]
  have hNs : ∀ j, h.norm (s j) = 1 := fun j => by
    rw [UnitaryFieldData.norm, mul_comm]
    exact hs j
  have hbt : ∀ i, (b.map h.bar)ᵀ i 0 = h.bar (b 0 i) := fun i => rfl
  have hrel : ∀ i, h.norm (b i a) = h.norm ((y⁻¹ a 0)⁻¹) * h.norm (b 0 i) := by
    intro i
    have e := congrArg h.norm (hsa i)
    rw [singerU_norm_mul, singerU_norm_mul, hNs i, one_mul, hbt, singerUF_norm_bar] at e
    exact e
  have hsum1 : ∑ i, h.norm (b i a) = 1 := by
    have e1 := congrFun (congrFun hbu a) a
    rw [mul_apply, one_apply_eq] at e1
    rw [← e1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [UnitaryFieldData.norm, transpose_apply, map_apply, mul_comm]
  have hbb : b * (b.map h.bar)ᵀ = 1 := by
    rw [← Matrix.inv_eq_left_inv hbu]
    exact Matrix.mul_nonsing_inv b hbdet
  have hsum2 : ∑ i, h.norm (b 0 i) = 1 := by
    have e2 := congrFun (congrFun hbb 0) 0
    rw [mul_apply, one_apply_eq] at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [UnitaryFieldData.norm, transpose_apply, map_apply]
  have hNμ : h.norm ((y⁻¹ a 0)⁻¹) = 1 := by
    have e3 : ∑ i, h.norm (b i a) = h.norm ((y⁻¹ a 0)⁻¹) * ∑ i, h.norm (b 0 i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hrel i
    rw [hsum1, hsum2, mul_one] at e3
    exact e3.symm
  refine ⟨-a, fun j => ?_⟩
  have e1 := hrel (-j)
  rw [hNμ, one_mul, singerUF_norm_entry h hcu hbC (-j) a, singerUF_norm_entry h hcu hbC 0 (-j),
    zero_sub, neg_neg] at e1
  rw [← e1, show (-j - a : Fin p) = -a - j by ring]

theorem singerUF_no_reflection (h : UnitaryFieldData 2 f K) {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {ε D : K} (hεb : h.bar ε = ε) (hn : ε ^ 2 ≠ 0) (hn2 : (ε ^ 2) ^ 2 ≠ 1)
    (hD : D ≠ 0) {c : K} (hcu : h.bar c * c = 1) (b : Matrix (Fin p) (Fin p) K)
    (hk : ∀ k : ℕ, 2 ≤ k → k < p → b (k : Fin p) 0 = ε ^ (p - k) * D)
    (h0 : b 0 0 = c * D)
    (hrefl : ∃ r : Fin p, ∀ j : Fin p, h.norm (b j 0) = h.norm (b (r - j) 0)) : False := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hnε : h.norm ε = ε ^ 2 := by rw [UnitaryFieldData.norm, hεb, sq]
  have hnc : h.norm c = 1 := by
    rw [UnitaryFieldData.norm, mul_comm]
    exact hcu
  have hnD : h.norm D ≠ 0 := singerU_norm_ne_zero h hD
  have hn₀ : h.norm (b 0 0) = h.norm D := by rw [h0, singerU_norm_mul, hnc, one_mul]
  have hn₀ne : h.norm (b 0 0) ≠ 0 := by
    rw [hn₀]
    exact hnD
  obtain ⟨r, hr⟩ := hrefl
  let e : Fin p ≃+* ZMod p := ZMod.finEquiv p
  have h0N : h.norm (b (e.symm 0) 0) = h.norm (b 0 0) := by
    rw [map_zero]
  have hkN : ∀ k : ℕ, 2 ≤ k → k < p →
      h.norm (b (e.symm (k : ZMod p)) 0) = (ε ^ 2) ^ (p - k) * h.norm (b 0 0) := by
    intro k hk2 hkp
    rw [map_natCast, hk k hk2 hkp, singerU_norm_mul, singerU_norm_pow, hnε, hn₀]
  refine singer_seq_no_reflection (N := fun x : ZMod p => h.norm (b (e.symm x) 0)) hp5 hn hn2
    hn₀ne h0N hkN ⟨e r, fun x => ?_⟩
  show h.norm (b (e.symm x) 0) = h.norm (b (e.symm (e r - x)) 0)
  rw [map_sub, RingEquiv.symm_apply_apply]
  exact hr (e.symm x)

end Reflection

section Helpers

variable {f : ℕ} {K : Type} [Field K]

theorem singerUF_mulVec_e0 {p : ℕ} [NeZero p] (M : Matrix (Fin p) (Fin p) K) (j : Fin p) :
    (M *ᵥ Pi.single 0 1) j = M j 0 := by
  rw [mulVec_single_one, col_apply]

theorem singerUF_bar_rho (h : UnitaryFieldData 2 f K) {c : K} (hcu : h.bar c * c = 1) :
    h.bar (c + c⁻¹) = c + c⁻¹ := by
  rw [map_add, map_inv₀, singerUF_bar_eq_inv h hcu, inv_inv, add_comm]

theorem singerUF_diag_unitary (h : UnitaryFieldData 2 f K) {p : ℕ} (s : Fin p → K)
    (hs : ∀ i, h.bar (s i) * s i = 1) : ((diagonal s).map h.bar)ᵀ * diagonal s = 1 := by
  rw [diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  simpa using hs i

theorem singerUF_eq_one_of_sq (h : UnitaryFieldData 2 f K) {x : K} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 := singerUF_two_eq_zero h
  have h1 : (x + 1) ^ 2 = 0 := by linear_combination hx + (x + 1) * h2
  have h3 : x + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
  linear_combination h3 - h2

theorem singerUF_inv_ne_self (h : UnitaryFieldData 2 f K) {c : K} (hc : c ≠ 0) (hc1 : c ≠ 1) :
    c⁻¹ ≠ c := by
  intro e
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  rw [e] at hcc
  exact hc1 (singerUF_eq_one_of_sq h (by linear_combination hcc))

theorem singerUF_cayley_one (h : UnitaryFieldData 2 f K) {p : ℕ} [hp : Fact p.Prime]
    (hpq : 2 ^ f + 1 = p) {c ε : K} (hc : c ≠ 0) (hεb : h.bar ε = ε) (hE : ε ^ 2 + c ≠ 0) :
    thmU_cayleyMat h p c ε 1 0 = (ε ^ (p - 1) + c * ε) / (ε ^ 2 + c) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hodd := singerUF_odd h hpq
  have hp3 := singerUF_three_le h hpq
  have hE' : h.bar ε ^ p + c ≠ 0 := by
    rw [hεb, singerUF_pow_p h hpq hεb]
    exact hE
  have h1 : ((1 : Fin p) : ℕ) = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [thmU_cayleyMat_apply_zero h hodd hp3 hc hE' 1, if_neg (show ¬ ((1 : Fin p) : ℕ) = 0 by omega),
    if_pos h1, hεb, singerUF_pow_p h hpq hεb]

theorem singerUF_cayley_nat (h : UnitaryFieldData 2 f K) {p : ℕ} [hp : Fact p.Prime]
    (hpq : 2 ^ f + 1 = p) {c ε : K} (hc : c ≠ 0) (hεb : h.bar ε = ε) (hE : ε ^ 2 + c ≠ 0)
    {k : ℕ} (hk2 : 2 ≤ k) (hkp : k < p) :
    thmU_cayleyMat h p c ε (k : Fin p) 0 = ε ^ (p - k) * ((1 + ε ^ 2) / (ε ^ 2 + c)) := by
  have hk : ((k : Fin p) : ℕ) = k := Fin.val_cast_of_lt hkp
  rw [singerUF_cayley_hi h hpq hc hεb hE (k : Fin p) (by rw [hk]; exact hk2), hk]

end Helpers

section FiveFour

theorem exists_outer_fixer_five_four {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {p : ℕ} [Fact p.Prime] (hℓ : ℓ = 2) (hf : f = 2) (hp : p = 5) {c : K}
    (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c) (H : Subgroup (GL (Fin p) K))
    (hT : ∀ g ∈ unitarySU ℓ f K p, (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hL : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin p) (Fin p) K) := by
  subst hℓ hf hp
  have hpq : 2 ^ 2 + 1 = 5 := by norm_num
  have h2 := singerUF_two_eq_zero h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcu
    exact zero_ne_one hcu
  have hpc : c ^ 5 = 1 := by
    rw [h.bar_apply] at hcu
    norm_num at hcu
    linear_combination hcu
  have hc1 : c ≠ 1 := fun e => hc ⟨1, by rw [one_pow, e]⟩
  have hord : orderOf c = 5 := orderOf_eq_prime hpc hc1
  have hodd : Odd (orderOf c) := by rw [hord]; decide
  have hgt : 3 < orderOf c := by rw [hord]; norm_num
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hρ0 : c + c⁻¹ ≠ 0 := singerUF_rho_ne_zero h hc0 hc1
  have hρ1 : c + c⁻¹ ≠ 1 := singerUF_rho_ne_one h (by norm_num) hc0 hpc hc1
  have hΦ : c ^ 4 + c ^ 3 + c ^ 2 + c + 1 = 0 := by
    have : (c - 1) * (c ^ 4 + c ^ 3 + c ^ 2 + c + 1) = 0 := by linear_combination hpc
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
  obtain ⟨ε, hεdef⟩ : ∃ ε : K, ε = (c + c⁻¹)⁻¹ := ⟨_, rfl⟩
  have hε1 : ε * (c + c⁻¹) = 1 := by
    rw [hεdef]
    exact inv_mul_cancel₀ hρ0
  have hεb : h.bar ε = ε := by
    rw [hεdef, map_inv₀, singerUF_bar_rho h hcu]
  have hkey : c ^ 2 * ((c + c⁻¹) ^ 2 + (c + c⁻¹) + 1) = 0 := by
    linear_combination hΦ + (2 * c ^ 2 + c * c⁻¹ + 1 + c) * hcc + c ^ 2 * h2
  have hρq : (c + c⁻¹) ^ 2 + (c + c⁻¹) + 1 = 0 :=
    (mul_eq_zero.mp hkey).resolve_left (pow_ne_zero 2 hc0)
  have hq : ε ^ 2 + ε + 1 = 0 := by
    linear_combination ε ^ 2 * hρq - (1 + ε * (c + c⁻¹) + ε) * hε1
  have hε3 : ε ^ 3 = 1 := by linear_combination (ε - 1) * hq
  have hεc : ε * (c ^ 2 + 1) = c := by linear_combination c * hε1 - ε * hcc
  have hc21 : c ^ 2 + 1 ≠ 0 := by
    intro e
    have h1 : (c + 1) ^ 2 = 0 := by linear_combination e + c * h2
    have h3 : c + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
    exact hc1 (by linear_combination h3 - h2)
  have hcε : c ^ 3 = ε ^ 2 * (1 + c) := by
    have key : (c ^ 2 + 1) ^ 2 * (c ^ 3 - ε ^ 2 * (1 + c)) = 0 := by
      linear_combination c ^ 2 * hpc + c ^ 5 * h2 - (1 + c) * (ε * (c ^ 2 + 1) + c) * hεc
    have := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hc21)
    linear_combination this
  have hε_ne1 : ε ≠ 1 := by
    intro e
    apply hρ1
    rw [e, one_mul] at hε1
    exact hε1
  have hsq_ne1 : ε ^ 2 ≠ 1 := fun e => hε_ne1 (singerUF_eq_one_of_sq h e)
  have hD1 : 1 + ε ^ 2 ≠ 0 := by
    intro e
    exact hsq_ne1 (by linear_combination e - h2)
  have hE : ε ^ 2 + c ≠ 0 := by
    intro h0
    have hεc2 : ε ^ 2 = c := by linear_combination h0 - c * h2
    have hc3 : c ^ 3 = 1 := by
      rw [← hεc2]
      linear_combination (ε ^ 3 + 1) * hε3
    have hord3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    rw [hord] at hord3
    omega
  obtain ⟨D, hD⟩ : ∃ D : K, D = (1 + ε ^ 2) / (ε ^ 2 + c) := ⟨_, rfl⟩
  have hDne : D ≠ 0 := by
    rw [hD]
    exact div_ne_zero hD1 hE
  have hodd5 : Odd 5 := by decide
  have hE5 : c + h.bar ε ^ 5 ≠ 0 := by
    rw [hεb, singerUF_pow_p h hpq hεb, add_comm]
    exact hE
  have hε0 : ε ≠ 0 := by
    intro e
    rw [e, zero_mul] at hε1
    exact zero_ne_one hε1
  have hn : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε0
  have hn2 : (ε ^ 2) ^ 2 ≠ 1 := by
    intro e
    apply hε_ne1
    linear_combination (-ε) * hε3 + e
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin 5) (Fin 5) K, b = thmU_cayleyMat h 5 c ε := ⟨_, rfl⟩
  have hbu : (b.map h.bar)ᵀ * b = 1 := by
    rw [hb]
    exact thmU_cayley_unitary h ε hodd5 hcu hc0 hE5
  have hbC : b * companionMat 5 c = companionMat 5 c * b := by
    rw [hb]
    exact (thmU_cayley_commute h ε hodd5 hc0 hE5).symm.eq
  have hb0 : b 0 0 = c * D := by
    rw [hb, singerUF_cayley_zero_zero h hpq hc0 hεb hE, hD]
  have hbk : ∀ k : ℕ, 2 ≤ k → k < 5 → b (k : Fin 5) 0 = ε ^ (5 - k) * D := by
    intro k hk2 hk5
    rw [hb, hD]
    exact singerUF_cayley_nat h hpq hc0 hεb hE hk2 hk5
  have hnum1 : ε ^ 4 + c * ε = (1 + c) * (1 + ε ^ 2) := by
    linear_combination (-(1 + c)) * hq + ε * hε3 + ε * (1 + c) * h2
  have hb1 : b 1 0 = (1 + c) * D := by
    rw [hb, singerUF_cayley_one h hpq hc0 hεb hE, hD, ← mul_div_assoc]
    show (ε ^ 4 + c * ε) / (ε ^ 2 + c) = _
    rw [hnum1]
  have hb2 : b 2 0 = ε ^ 3 * D := by
    have := hbk 2 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hb3 : b 3 0 = ε ^ 2 * D := by
    have := hbk 3 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have hb4 : b 4 0 = ε * D := by
    have := hbk 4 (by norm_num) (by norm_num)
    norm_num at this
    exact this
  have e01 : b 0 1 = c * b 4 0 := by
    have := singerUF_entry hbC 0 1 (by norm_num) (by norm_num)
    simpa using this
  have e02 : b 0 2 = c * b 3 0 := by
    have := singerUF_entry hbC 0 2 (by norm_num) (by norm_num)
    simpa using this
  have e03 : b 0 3 = c * b 2 0 := by
    have := singerUF_entry hbC 0 3 (by norm_num) (by norm_num)
    simpa using this
  have e04 : b 0 4 = c * b 1 0 := by
    have := singerUF_entry hbC 0 4 (by norm_num) (by norm_num)
    simpa using this
  have f21 : b 2 1 = b 1 0 := by
    have := singerUF_entry hbC 2 1 (by norm_num) (by norm_num)
    simpa using this
  have f22 : b 2 2 = b 0 0 := by
    have := singerUF_entry hbC 2 2 (by norm_num) (by norm_num)
    simpa using this
  have f23 : b 2 3 = c * b 4 0 := by
    have := singerUF_entry hbC 2 3 (by norm_num) (by norm_num)
    simpa using this
  have f24 : b 2 4 = c * b 3 0 := by
    have := singerUF_entry hbC 2 4 (by norm_num) (by norm_num)
    simpa using this
  set s : Fin 5 → K := ![c, 1, c⁻¹, 1, 1] with hs_def
  have hwpair : ∀ m : Fin 5,
      ((b * diagonal s * b) *ᵥ Pi.single 0 1) m = ∑ j, b m j * b j 0 * s j := by
    intro m
    rw [thmU_pairing_apply]
    simp only [singerUF_mulVec_e0]
  have hw0 : ((b * diagonal s * b) *ᵥ Pi.single 0 1) 0 = 0 := by
    rw [hwpair, Fin.sum_univ_five, e01, e02, e03, e04, hb0, hb1, hb2, hb3, hb4]
    simp only [hs_def]
    simp
    linear_combination D ^ 2 * hcε + (1 + c) * D ^ 2 * ε ^ 2 * hε3
      + (1 + c) * D ^ 2 * (ε ^ 2 + c * ε) * h2 + ε ^ 5 * D ^ 2 * hcc
  have hw2 : ((b * diagonal s * b) *ᵥ Pi.single 0 1) 2 = 0 := by
    rw [hwpair, Fin.sum_univ_five, f21, f22, f23, f24, hb0, hb1, hb2, hb3, hb4]
    simp only [hs_def]
    simp
    linear_combination (c ^ 2 + c * c⁻¹ + 2 * c) * D ^ 2 * hε3 + D ^ 2 * hcc
      + (1 + c) ^ 2 * D ^ 2 * h2
  have hsd : ∀ i, h.bar (s i) * s i = 1 := by
    intro i
    fin_cases i
    · show h.bar c * c = 1
      exact hcu
    · show h.bar 1 * 1 = 1
      simp
    · show h.bar c⁻¹ * c⁻¹ = 1
      rw [map_inv₀, singerUF_bar_eq_inv h hcu, inv_inv]
      exact hcc
    · show h.bar 1 * 1 = 1
      simp
    · show h.bar 1 * 1 = 1
      simp
  have hsdet : (diagonal s).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_five]
    simp [hs_def, hc0]
  have hsdetU : IsUnit (diagonal s).det := by
    rw [hsdet]
    exact isUnit_one
  have hbdetU : IsUnit b.det := Matrix.isUnit_det_of_left_inverse hbu
  have hcdetU : IsUnit (companionMat 5 c).det := thmU_companionMat_isUnit_det hodd5 hc0
  let sG : GL (Fin 5) K := Matrix.GeneralLinearGroup.mk'' (diagonal s) hsdetU
  let bG : GL (Fin 5) K := Matrix.GeneralLinearGroup.mk'' b hbdetU
  let cG : GL (Fin 5) K := Matrix.GeneralLinearGroup.mk'' (companionMat 5 c) hcdetU
  have hsG : sG ∈ unitarySU 2 2 K 5 :=
    (mem_unitarySU_iff h).mpr ⟨hsdet, singerUF_diag_unitary h s hsd⟩
  have hconj := (thmU_sq_conj_mem h hodd5 hcu hc H hT hL cG rfl bG hbu hbC sG hsG ⟨s, rfl⟩
    sG hsG ⟨s, rfl⟩).1
  have hcoe : (((bG * sG * bG)⁻¹ * sG * (bG * sG * bG) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = (b * diagonal s * b)⁻¹ * diagonal s * (b * diagonal s * b) := by
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
    rfl
  have hYU : IsUnit (b * diagonal s * b).det := by
    rw [det_mul, det_mul]
    exact (hbdetU.mul hsdetU).mul hbdetU
  have hYi : (b * diagonal s * b)⁻¹ * (b * diagonal s * b) = 1 := Matrix.nonsing_inv_mul _ hYU
  have hDw : diagonal s *ᵥ ((b * diagonal s * b) *ᵥ Pi.single 0 1) =
      (b * diagonal s * b) *ᵥ Pi.single 0 1 := by
    funext i
    rw [mulVec_diagonal]
    by_cases hi0 : i = 0
    · subst hi0
      rw [hw0, mul_zero]
    by_cases hi2 : i = 2
    · subst hi2
      rw [hw2, mul_zero]
    have hsi : s i = 1 := by
      rw [hs_def]
      fin_cases i <;> simp_all
    rw [hsi, one_mul]
  have hfixv : ((b * diagonal s * b)⁻¹ * diagonal s * (b * diagonal s * b)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 := by
    calc ((b * diagonal s * b)⁻¹ * diagonal s * (b * diagonal s * b)) *ᵥ Pi.single 0 1
        = (b * diagonal s * b)⁻¹ *ᵥ (diagonal s *ᵥ ((b * diagonal s * b) *ᵥ Pi.single 0 1)) := by
          rw [← mulVec_mulVec, ← mulVec_mulVec]
      _ = (b * diagonal s * b)⁻¹ *ᵥ ((b * diagonal s * b) *ᵥ Pi.single 0 1) := by rw [hDw]
      _ = Pi.single 0 1 := by rw [mulVec_mulVec, hYi, one_mulVec]
  have hfix : ∀ i : Fin 5, i ≠ 0 →
      ((b * diagonal s * b)⁻¹ * diagonal s * (b * diagonal s * b)) i 0 = 0 := by
    intro i hi
    have e := congrFun hfixv i
    rw [singerUF_mulVec_e0, Pi.single_apply, if_neg hi] at e
    exact e
  have hmono_neg : ¬ IsMonomialMat ((b * diagonal s * b)⁻¹ * diagonal s * (b * diagonal s * b)) := by
    intro hmono
    have hs0 : s 0 = c := rfl
    have hsne : ∀ i, i ≠ 0 → s i ≠ c := by
      intro i hi
      fin_cases i
      · exact absurd rfl hi
      · show (1 : K) ≠ c
        exact fun e => hc1 e.symm
      · show c⁻¹ ≠ c
        exact singerUF_inv_ne_self h hc0 hc1
      · show (1 : K) ≠ c
        exact fun e => hc1 e.symm
      · show (1 : K) ≠ c
        exact fun e => hc1 e.symm
    have hsc : ∀ i, (s i - c) * (s i - c⁻¹) * (s i - 1) = 0 := by
      intro i
      fin_cases i <;> simp [hs_def]
    obtain ⟨r, hr⟩ := singerUF_reflection_of_monomial h hcu hodd hgt b hbu hbC s s hsd hs0 hsne
      hsc hmono
    exact singerUF_no_reflection h (by norm_num) hεb hn hn2 hDne hcu b hbk hb0 ⟨r, hr⟩
  refine ⟨(bG * sG * bG)⁻¹ * sG * (bG * sG * bG), hconj, ?_, ?_⟩
  · intro i hi
    rw [hcoe]
    exact hfix i hi
  · rw [hcoe]
    exact hmono_neg
end FiveFour


section Sums

variable {K : Type} [Field K]

theorem singerUF_natCast_two_mul (h2 : (2 : K) = 0) (m : ℕ) : ((2 * m : ℕ) : K) = 0 := by
  rw [Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul]

theorem singerUF_natCast_two_mul_add_one (h2 : (2 : K) = 0) (m : ℕ) :
    ((2 * m + 1 : ℕ) : K) = 1 := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul, Nat.cast_one, zero_add]

theorem singerUF_sum_split_two {M : Type} [AddCommMonoid M] {p : ℕ} (hp : 7 ≤ p) (F : ℕ → M) :
    ∑ k ∈ Finset.range p, F k = F 0 + F 1 + ∑ k ∈ Finset.Ico 2 (p - 1), F k + F (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico F (show 2 ≤ q by omega)]
  have hq : q + 1 - 1 = q := by omega
  rw [hq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  abel

theorem singerUF_sN_add {c : K} (h2 : (2 : K) = 0) (sN : ℕ → K)
    (hsN : ∀ k, sN k = (if k = 2 then c ^ 2 else 1) * (if k = 5 then c⁻¹ else 1) *
      (if k = 6 then c⁻¹ else 1)) (k : ℕ) :
    sN k = 1 + (if k = 2 then c ^ 2 + 1 else 0) + (if k = 5 then c⁻¹ + 1 else 0) +
      (if k = 6 then c⁻¹ + 1 else 0) := by
  rw [hsN]
  by_cases hk2 : k = 2
  · subst hk2
    norm_num
    linear_combination -h2
  by_cases hk5 : k = 5
  · subst hk5
    norm_num
    linear_combination -h2
  by_cases hk6 : k = 6
  · subst hk6
    norm_num
    linear_combination -h2
  simp [hk2, hk5, hk6]

theorem singerUF_sum_sN_Ico2 {c : K} (h2 : (2 : K) = 0) (sN : ℕ → K)
    (hsN : ∀ k, sN k = (if k = 2 then c ^ 2 else 1) * (if k = 5 then c⁻¹ else 1) *
      (if k = 6 then c⁻¹ else 1)) {p : ℕ} (hp : 9 ≤ p) (hpo : Odd p) :
    ∑ k ∈ Finset.Ico 2 (p - 1), sN k = ((p - 3 : ℕ) : K) + (c ^ 2 + 1) := by
  obtain ⟨m, hm⟩ := hpo
  have hpar : ((p - 3 : ℕ) : K) = 0 := by
    rw [show p - 3 = 2 * (m - 1) by omega]
    exact singerUF_natCast_two_mul h2 _
  have h2mem : (2 : ℕ) ∈ Finset.Ico 2 (p - 1) := by
    rw [Finset.mem_Ico]; omega
  have h5mem : (5 : ℕ) ∈ Finset.Ico 2 (p - 1) := by
    rw [Finset.mem_Ico]; omega
  have h6mem : (6 : ℕ) ∈ Finset.Ico 2 (p - 1) := by
    rw [Finset.mem_Ico]; omega
  simp only [singerUF_sN_add h2 sN hsN]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Finset.sum_ite_eq', if_pos h2mem,
    Finset.sum_ite_eq', if_pos h5mem, Finset.sum_ite_eq', if_pos h6mem]
  rw [show p - 1 - 2 = p - 3 by omega]
  linear_combination (c⁻¹ + 1) * h2


theorem singerUF_sum_zero {p : ℕ} (hp : 17 ≤ p) (hpo : Odd p) {c ε D : K} (h2 : (2 : K) = 0)
    (hrel : ε ^ 2 * (c ^ 2 + 1) = c) (hcc : c * c⁻¹ = 1) (hpow : ε ^ p = ε ^ 2)
    (bcol : ℕ → K) (hb0 : bcol 0 = c * D)
    (hbk : ∀ k, 2 ≤ k → k < p → bcol k = ε ^ (p - k) * D)
    (e : ℕ → K) (he0 : ∀ k, k < p → e k = if k = 0 then bcol 0 else c * bcol (p - k))
    (sN : ℕ → K) (hsN : ∀ k, sN k = (if k = 2 then c ^ 2 else 1) * (if k = 5 then c⁻¹ else 1) *
      (if k = 6 then c⁻¹ else 1)) :
    ∑ k ∈ Finset.range p, e k * bcol k * sN k = 0 := by
  have hp7 : 7 ≤ p := by omega
  have hpar : ((p - 3 : ℕ) : K) = 0 := by
    obtain ⟨m, hm⟩ := hpo
    rw [show p - 3 = 2 * (m - 1) by omega]
    exact singerUF_natCast_two_mul h2 _
  have hs0 : sN 0 = 1 := by rw [hsN]; simp
  have hs1 : sN 1 = 1 := by rw [hsN]; simp
  have hsp1 : sN (p - 1) = 1 := by
    rw [hsN, if_neg (show ¬ (p - 1 = 2) by omega), if_neg (show ¬ (p - 1 = 5) by omega),
      if_neg (show ¬ (p - 1 = 6) by omega)]
    simp
  have he00 : e 0 = bcol 0 := by rw [he0 0 (by omega), if_pos rfl]
  have he1 : e 1 = c * bcol (p - 1) := by
    rw [he0 1 (by omega), if_neg (by norm_num)]
  have hep1 : e (p - 1) = c * bcol 1 := by
    rw [he0 (p - 1) (by omega), if_neg (by omega), show p - (p - 1) = 1 by omega]
  have hmid : ∀ k ∈ Finset.Ico 2 (p - 1), e k * bcol k * sN k = c * ε ^ 2 * D ^ 2 * sN k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpk : ε ^ k * ε ^ (p - k) = ε ^ p := by
      rw [← pow_add]
      congr 1
      omega
    rw [he0 k (by omega), if_neg (by omega), hbk k hk.1 (by omega),
      hbk (p - k) (by omega) (by omega), show p - (p - k) = k by omega]
    linear_combination (c * D ^ 2 * sN k) * hpk + (c * D ^ 2 * sN k) * hpow
  rw [singerUF_sum_split_two hp7, Finset.sum_congr rfl hmid, ← Finset.mul_sum,
    singerUF_sum_sN_Ico2 h2 sN hsN (by omega) hpo, hs0, hs1, hsp1, he00, he1, hep1, hb0]
  simp only [mul_one]
  linear_combination (c * ε ^ 2 * D ^ 2) * hpar + (c * D ^ 2) * hrel
    + (c ^ 2 * D ^ 2 + c * bcol 1 * bcol (p - 1)) * h2

theorem singerUF_sum_five {p : ℕ} (hp : 17 ≤ p) (hpo : Odd p) {c ε D : K} (h2 : (2 : K) = 0)
    (hrel : ε ^ 2 * (c ^ 2 + 1) = c) (hcc : c * c⁻¹ = 1) (hpow : ε ^ p = ε ^ 2)
    (bcol : ℕ → K) (hb0 : bcol 0 = c * D)
    (hbk : ∀ k, 2 ≤ k → k < p → bcol k = ε ^ (p - k) * D)
    (e : ℕ → K) (he5 : ∀ k, k < p → e k = if k ≤ 5 then bcol (5 - k) else c * bcol (5 + p - k))
    (sN : ℕ → K) (hsN : ∀ k, sN k = (if k = 2 then c ^ 2 else 1) * (if k = 5 then c⁻¹ else 1) *
      (if k = 6 then c⁻¹ else 1)) :
    ∑ k ∈ Finset.range p, e k * bcol k * sN k = 0 := by
  obtain ⟨m, hm⟩ := hpo
  have hp6 : ((p - 6 : ℕ) : K) = 1 := by
    rw [show p - 6 = 2 * (m - 3) + 1 by omega]
    exact singerUF_natCast_two_mul_add_one h2 _
  have hs0 : sN 0 = 1 := by rw [hsN]; simp
  have hs1 : sN 1 = 1 := by rw [hsN]; simp
  have hs2 : sN 2 = c ^ 2 := by rw [hsN]; simp
  have hs3 : sN 3 = 1 := by rw [hsN]; simp
  have hs4 : sN 4 = 1 := by rw [hsN]; simp
  have hs5 : sN 5 = c⁻¹ := by rw [hsN]; simp
  have hs_sum : ∑ k ∈ Finset.Ico 6 p, sN k = ((p - 6 : ℕ) : K) + (c⁻¹ + 1) := by
    rw [Finset.sum_congr rfl (fun k _ => singerUF_sN_add h2 sN hsN k)]
    have h6mem : (6 : ℕ) ∈ Finset.Ico 6 p := by
      rw [Finset.mem_Ico]; omega
    have h2not : (2 : ℕ) ∉ Finset.Ico 6 p := by
      rw [Finset.mem_Ico]; omega
    have h5not : (5 : ℕ) ∉ Finset.Ico 6 p := by
      rw [Finset.mem_Ico]; omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
      if_neg h2not, Finset.sum_ite_eq', if_neg h5not, Finset.sum_ite_eq', if_pos h6mem]
    rw [show p - 6 = p - 6 from rfl]
    ring
  have hmid : ∀ k ∈ Finset.Ico 6 p, e k * bcol k * sN k =
      c * ε ^ (p - 5) * D ^ 2 * sN k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpk : ε ^ (k - 5) * ε ^ (p - k) = ε ^ (p - 5) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he5 k (by omega), if_neg (by omega), hbk (5 + p - k) (by omega) (by omega),
      hbk k (by omega) (by omega), show p - (5 + p - k) = k - 5 by omega]
    linear_combination (c * D ^ 2 * sN k) * hpk
  have hsum_rest : ∑ k ∈ Finset.Ico 6 p, e k * bcol k * sN k =
      c * ε ^ (p - 5) * D ^ 2 * (((p - 6 : ℕ) : K) + (c⁻¹ + 1)) := by
    rw [Finset.sum_congr rfl hmid, ← Finset.mul_sum, hs_sum]
  have f0 : e 0 = bcol 5 := by rw [he5 0 (by omega)]; simp
  have f1 : e 1 = bcol 4 := by rw [he5 1 (by omega)]; simp
  have f2 : e 2 = bcol 3 := by rw [he5 2 (by omega)]; simp
  have f3 : e 3 = bcol 2 := by rw [he5 3 (by omega)]; simp
  have f4 : e 4 = bcol 1 := by rw [he5 4 (by omega)]; simp
  have f5 : e 5 = bcol 0 := by rw [he5 5 (by omega)]; simp
  have hA : ε ^ (p - 3) * ε ^ (p - 2) = ε ^ (p - 5) * ε ^ 2 := by
    rw [← hpow, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [← Finset.sum_range_add_sum_Ico _ (show 6 ≤ p by omega), hsum_rest]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [f0, f1, f2, f3, f4, f5, hs0, hs1, hs2, hs3, hs4, hs5,
    hbk 2 (by norm_num) (by omega), hbk 3 (by norm_num) (by omega),
    hbk 4 (by norm_num) (by omega), hbk 5 (by norm_num) (by omega), hb0]
  linear_combination (c ^ 2 + 1) * D ^ 2 * hA + ε ^ (p - 5) * D ^ 2 * hrel
    + c * ε ^ (p - 5) * D ^ 2 * hp6
    + (2 * c * ε ^ (p - 5) * D ^ 2 + c * c⁻¹ * ε ^ (p - 5) * D ^ 2 + ε ^ (p - 4) * D * bcol 1) * h2

end Sums

section FermatMain

variable {f : ℕ} {K : Type} [Field K]

theorem singerUF_prod_range_ite {p : ℕ} (a : ℕ) (ha : a < p) (v : K) :
    ∏ k ∈ Finset.range p, (if k = a then v else 1) = v := by
  rw [Finset.prod_ite_eq', if_pos (Finset.mem_range.mpr ha)]

theorem singerUF_pairing_sN {p : ℕ} [NeZero p] (b : Matrix (Fin p) (Fin p) K) (sN : ℕ → K)
    (m : Fin p) :
    ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1) m =
      ∑ k ∈ Finset.range p, b m (k : Fin p) * b (k : Fin p) 0 * sN k := by
  rw [thmU_pairing_apply, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [singerUF_mulVec_e0, Fin.cast_val_eq_self]

end FermatMain

theorem singerUF_tN_cases {K : Type} [Field K] {c : K} {tN : ℕ → K}
    (htN : ∀ k, tN k = (if k = 0 then c else 1) * (if k = 5 then c⁻¹ else 1)) (k : ℕ) :
    tN k = c ∨ tN k = c⁻¹ ∨ tN k = 1 := by
  rw [htN]
  split_ifs with h0 h5 <;> first | omega | simp

theorem singerUF_fermat_main_end {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {p : ℕ} [hp : Fact p.Prime] (hp17 : 17 ≤ p) (hodd : Odd p) {c ε D : K}
    (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c) (H : Subgroup (GL (Fin p) K))
    (hT : ∀ g ∈ unitarySU 2 f K p, (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hL : ∀ g ∈ unitarySU 2 f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hgt : 3 < orderOf c) (hodd_c : Odd (orderOf c))
    (hpq : 2 ^ f + 1 = p) (hεb : h.bar ε = ε) (hrel : ε ^ 2 * (c ^ 2 + 1) = c)
    (hE : ε ^ 2 + c ≠ 0) (hE' : c + h.bar ε ^ p ≠ 0) (hpow : ε ^ p = ε ^ 2)
    (hD : D = (1 + ε ^ 2) / (ε ^ 2 + c)) (hDne : D ≠ 0) (hn : ε ^ 2 ≠ 0)
    (hn2 : (ε ^ 2) ^ 2 ≠ 1) (hcc : c * c⁻¹ = 1) (h2 : (2 : K) = 0)
    (sN : ℕ → K) (hsN : ∀ k, sN k = (if k = 2 then c ^ 2 else 1) *
      (if k = 5 then c⁻¹ else 1) * (if k = 6 then c⁻¹ else 1))
    (hsnorm : ∀ k, h.bar (sN k) * sN k = 1)
    (hdet_s : (diagonal (fun j : Fin p => sN (j : ℕ))).det = 1)
    (tN : ℕ → K) (htN : ∀ k, tN k = (if k = 0 then c else 1) * (if k = 5 then c⁻¹ else 1))
    (htnorm : ∀ k, h.bar (tN k) * tN k = 1)
    (hdet_t : (diagonal (fun j : Fin p => tN (j : ℕ))).det = 1) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin p) (Fin p) K) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin p) (Fin p) K, b = thmU_cayleyMat h p c ε := ⟨_, rfl⟩
  have hbu : (b.map h.bar)ᵀ * b = 1 := by
    rw [hb]
    exact thmU_cayley_unitary h ε hodd hcu hc0 hE'
  have hbC : b * companionMat p c = companionMat p c * b := by
    rw [hb]
    exact (thmU_cayley_commute h ε hodd hc0 hE').symm.eq
  have hbk : ∀ k : ℕ, 2 ≤ k → k < p → b (k : Fin p) 0 = ε ^ (p - k) * D := by
    intro k hk2 hk
    rw [hb, hD]
    exact singerUF_cayley_nat h hpq hc0 hεb hE hk2 hk
  have hb0 : b ((0 : ℕ) : Fin p) 0 = c * D := by
    rw [hb, hD]
    exact singerUF_cayley_zero_zero h hpq hc0 hεb hE
  have he0 : ∀ k, k < p → b ((0 : ℕ) : Fin p) (k : Fin p) =
      if k = 0 then b ((0 : ℕ) : Fin p) 0 else c * b ((p - k : ℕ) : Fin p) 0 := by
    intro k hk
    have := singerUF_entry hbC 0 k (by omega) hk
    by_cases hk0 : k = 0
    · subst hk0
      simpa using this
    · rw [this, if_neg (show ¬ k ≤ 0 by omega), if_neg hk0, zero_add]
  have he5 : ∀ k, k < p → b ((5 : ℕ) : Fin p) (k : Fin p) =
      if k ≤ 5 then b ((5 - k : ℕ) : Fin p) 0 else c * b ((5 + p - k : ℕ) : Fin p) 0 :=
    fun k hk => singerUF_entry hbC 5 k (by omega) hk
  have hw0sum : ∑ k ∈ Finset.range p, b ((0 : ℕ) : Fin p) (k : Fin p) * b (k : Fin p) 0 * sN k
      = 0 :=
    singerUF_sum_zero hp17 hodd h2 hrel hcc hpow (fun k => b (k : Fin p) 0) hb0 hbk
      (fun k => b ((0 : ℕ) : Fin p) (k : Fin p)) he0 sN hsN
  have hw5sum : ∑ k ∈ Finset.range p, b ((5 : ℕ) : Fin p) (k : Fin p) * b (k : Fin p) 0 * sN k
      = 0 :=
    singerUF_sum_five hp17 hodd h2 hrel hcc hpow (fun k => b (k : Fin p) 0) hb0 hbk
      (fun k => b ((5 : ℕ) : Fin p) (k : Fin p)) he5 sN hsN
  have hw0 : ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1)
      ((0 : ℕ) : Fin p) = 0 := by
    rw [singerUF_pairing_sN b sN, hw0sum]
  have hw5 : ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1)
      ((5 : ℕ) : Fin p) = 0 := by
    rw [singerUF_pairing_sN b sN, hw5sum]
  have hwz : ∀ i : Fin p, ((i : ℕ) = 0 ∨ (i : ℕ) = 5) →
      ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1) i = 0 := by
    intro i hi
    rcases hi with hi | hi
    · have hiv : i = ((0 : ℕ) : Fin p) := Fin.ext (by rw [Fin.val_cast_of_lt (by omega)]; exact hi)
      rw [hiv]
      exact hw0
    · have hiv : i = ((5 : ℕ) : Fin p) := Fin.ext (by rw [Fin.val_cast_of_lt (by omega)]; exact hi)
      rw [hiv]
      exact hw5
  have hbdetU : IsUnit b.det := Matrix.isUnit_det_of_left_inverse hbu
  have hcdetU : IsUnit (companionMat p c).det := thmU_companionMat_isUnit_det hodd hc0
  have hsdetU : IsUnit (diagonal (fun j : Fin p => sN (j : ℕ))).det := by
    rw [hdet_s]
    exact isUnit_one
  have htdetU : IsUnit (diagonal (fun j : Fin p => tN (j : ℕ))).det := by
    rw [hdet_t]
    exact isUnit_one
  let sG : GL (Fin p) K := Matrix.GeneralLinearGroup.mk'' _ hsdetU
  let tG : GL (Fin p) K := Matrix.GeneralLinearGroup.mk'' _ htdetU
  let bG : GL (Fin p) K := Matrix.GeneralLinearGroup.mk'' b hbdetU
  let cG : GL (Fin p) K := Matrix.GeneralLinearGroup.mk'' (companionMat p c) hcdetU
  have hsG : sG ∈ unitarySU 2 f K p :=
    (mem_unitarySU_iff h).mpr ⟨hdet_s, singerUF_diag_unitary h _ (fun j => hsnorm j)⟩
  have htG : tG ∈ unitarySU 2 f K p :=
    (mem_unitarySU_iff h).mpr ⟨hdet_t, singerUF_diag_unitary h _ (fun j => htnorm j)⟩
  have hconj := (thmU_sq_conj_mem h hodd hcu hc H hT hL cG rfl bG hbu hbC sG hsG
    ⟨fun j : Fin p => sN (j : ℕ), rfl⟩ tG htG ⟨fun j : Fin p => tN (j : ℕ), rfl⟩).1
  have hcoe : (((bG * sG * bG)⁻¹ * tG * (bG * sG * bG) : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *
        diagonal (fun j : Fin p => tN (j : ℕ)) * (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) := by
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv]
    rfl
  have hYU : IsUnit (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b).det := by
    rw [det_mul, det_mul]
    exact (hbdetU.mul hsdetU).mul hbdetU
  have hYi : (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *
      (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) = 1 := Matrix.nonsing_inv_mul _ hYU
  have hDw : diagonal (fun j : Fin p => tN (j : ℕ)) *ᵥ
      ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1) =
      (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1 := by
    funext i
    rw [mulVec_diagonal]
    show tN (i : ℕ) * _ = _
    by_cases hi : (i : ℕ) = 0 ∨ (i : ℕ) = 5
    · rw [hwz i hi, mul_zero]
    · have ht1 : tN (i : ℕ) = 1 := by
        rw [htN, if_neg (show ¬ (i : ℕ) = 0 by omega), if_neg (show ¬ (i : ℕ) = 5 by omega),
          mul_one]
      rw [ht1, one_mul]
  have hfixv : ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *
      diagonal (fun j : Fin p => tN (j : ℕ)) * (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)) *ᵥ
      Pi.single 0 1 = Pi.single 0 1 := by
    calc _ = (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *ᵥ
          (diagonal (fun j : Fin p => tN (j : ℕ)) *ᵥ
            ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1)) := by
          rw [← mulVec_mulVec, ← mulVec_mulVec]
      _ = (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *ᵥ
          ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b) *ᵥ Pi.single 0 1) := by rw [hDw]
      _ = Pi.single 0 1 := by rw [mulVec_mulVec, hYi, one_mulVec]
  have hfix : ∀ i : Fin p, i ≠ 0 →
      ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *
        diagonal (fun j : Fin p => tN (j : ℕ)) * (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b))
        i 0 = 0 := by
    intro i hi
    have e := congrFun hfixv i
    rw [singerUF_mulVec_e0, Pi.single_apply, if_neg hi] at e
    exact e
  have hmono_neg : ¬ IsMonomialMat ((b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)⁻¹ *
      diagonal (fun j : Fin p => tN (j : ℕ)) * (b * diagonal (fun j : Fin p => sN (j : ℕ)) * b)) := by
    intro hmono
    have hs' : ∀ j : Fin p, h.bar ((fun j : Fin p => sN (j : ℕ)) j) *
        (fun j : Fin p => sN (j : ℕ)) j = 1 := fun j => hsnorm j
    have hta : (fun j : Fin p => tN (j : ℕ)) 0 = c := by
      show tN ((0 : Fin p) : ℕ) = c
      rw [Fin.val_zero, htN]
      simp
    have htne : ∀ i : Fin p, i ≠ 0 → (fun j : Fin p => tN (j : ℕ)) i ≠ c := by
      intro i hi
      have hi0 : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext h0)
      show tN (i : ℕ) ≠ c
      rw [htN, if_neg hi0, one_mul]
      split_ifs
      · exact singerUF_inv_ne_self h hc0 hc1
      · exact fun e => hc1 e.symm
    have htc : ∀ i : Fin p, ((fun j : Fin p => tN (j : ℕ)) i - c) *
        ((fun j : Fin p => tN (j : ℕ)) i - c⁻¹) * ((fun j : Fin p => tN (j : ℕ)) i - 1) = 0 := by
      intro i
      show (tN (i : ℕ) - c) * (tN (i : ℕ) - c⁻¹) * (tN (i : ℕ) - 1) = 0
      rcases singerUF_tN_cases htN (i : ℕ) with e | e | e <;> rw [e] <;> ring
    obtain ⟨r, hr⟩ := singerUF_reflection_of_monomial h hcu hodd_c hgt b hbu hbC
      (fun j : Fin p => sN (j : ℕ)) (fun j : Fin p => tN (j : ℕ)) hs' hta htne htc hmono
    exact singerUF_no_reflection h (by omega) hεb hn hn2 hDne hcu b hbk hb0 ⟨r, hr⟩
  refine ⟨(bG * sG * bG)⁻¹ * tG * (bG * sG * bG), hconj, ?_, ?_⟩
  · intro i hi
    rw [hcoe]
    exact hfix i hi
  · rw [hcoe]
    exact hmono_neg




theorem exists_outer_fixer_fermat {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {p : ℕ} [Fact p.Prime] (hp : 17 ≤ p) (hpq : ℓ ^ f + 1 = p) {c : K}
    (hcu : h.bar c * c = 1) (hc : ¬ ∃ μ : K, μ ^ p = c) (H : Subgroup (GL (Fin p) K))
    (hT : ∀ g ∈ unitarySU ℓ f K p, (∃ t, (g : Matrix (Fin p) (Fin p) K) = diagonal t) → g ∈ H)
    (hL : ∀ g ∈ unitarySU ℓ f K p,
      (g : Matrix (Fin p) (Fin p) K) * companionMat p c = companionMat p c * g → g ∈ H) :
    ∃ g ∈ H, (∀ i, i ≠ 0 → (g : Matrix (Fin p) (Fin p) K) i 0 = 0) ∧
      ¬ IsMonomialMat (g : Matrix (Fin p) (Fin p) K) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hℓ : ℓ = 2 := by
    have hev : Even (ℓ ^ f) := by
      obtain ⟨m, hm⟩ := hodd
      exact ⟨m, by omega⟩
    have h2d : 2 ∣ ℓ := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (even_iff_two_dvd.mp hev)
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).mp h2d).symm
  subst hℓ
  have h2 := singerUF_two_eq_zero h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcu
    exact zero_ne_one hcu
  have hpc : c ^ p = 1 := by
    rw [← hpq, pow_succ, ← h.bar_apply, hcu]
  have hc1 : c ≠ 1 := fun e => hc ⟨1, by rw [one_pow, e]⟩
  have hord : orderOf c = p := orderOf_eq_prime hpc hc1
  have hodd_c : Odd (orderOf c) := by rw [hord]; exact hodd
  have hgt : 3 < orderOf c := by rw [hord]; omega
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hρ0 : c + c⁻¹ ≠ 0 := singerUF_rho_ne_zero h hc0 hc1
  have hρ1 : c + c⁻¹ ≠ 1 := singerUF_rho_ne_one h (by omega) hc0 hpc hc1
  obtain ⟨ε, hε2, hεb⟩ := singerUF_exists_eps h hcu
  have hrel : ε ^ 2 * (c ^ 2 + 1) = c := singerUF_rel hc0 hρ0 hε2
  have hE : ε ^ 2 + c ≠ 0 := singerUF_E0_ne h hc0 hρ0 hε2
  have hE' : c + h.bar ε ^ p ≠ 0 := by
    rw [hεb, singerUF_pow_p h hpq hεb, add_comm]
    exact hE
  have hpow : ε ^ p = ε ^ 2 := singerUF_pow_p h hpq hεb
  have hD1 : 1 + ε ^ 2 ≠ 0 := by
    intro e
    have e1 : ε ^ 2 = 1 := by linear_combination e - h2
    rw [hε2] at e1
    exact hρ1 (inv_eq_one.mp e1)
  obtain ⟨D, hD⟩ : ∃ D : K, D = (1 + ε ^ 2) / (ε ^ 2 + c) := ⟨_, rfl⟩
  have hDne : D ≠ 0 := by
    rw [hD]
    exact div_ne_zero hD1 hE
  have hn : ε ^ 2 ≠ 0 := by
    rw [hε2]
    exact inv_ne_zero hρ0
  have hn2 : (ε ^ 2) ^ 2 ≠ 1 := by
    intro e
    have e1 := singerUF_eq_one_of_sq h e
    rw [hε2] at e1
    exact hρ1 (inv_eq_one.mp e1)
  obtain ⟨sN, hsN⟩ : ∃ sN : ℕ → K, ∀ k, sN k = (if k = 2 then c ^ 2 else 1) *
      (if k = 5 then c⁻¹ else 1) * (if k = 6 then c⁻¹ else 1) := ⟨_, fun k => rfl⟩
  have hcp : (c ^ 2) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hpc, one_pow]
  have hcinvp : (c⁻¹) ^ p = 1 := by rw [inv_pow, hpc, inv_one]
  have hsk : ∀ k, sN k ^ p = 1 := by
    intro k
    rw [hsN, mul_pow, mul_pow]
    split_ifs <;> simp [hcp, hcinvp]
  have hsnorm : ∀ k, h.bar (sN k) * sN k = 1 := fun k =>
    singerUF_norm_one_of_pow h hpq (hsk k)
  have hdet_s : (diagonal (fun j : Fin p => sN (j : ℕ))).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_eq_prod_range sN p]
    simp only [hsN]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, singerUF_prod_range_ite 2 (by omega),
      singerUF_prod_range_ite 5 (by omega), singerUF_prod_range_ite 6 (by omega)]
    linear_combination (c * c⁻¹ + 1) * hcc
  obtain ⟨tN, htN⟩ : ∃ tN : ℕ → K, ∀ k, tN k = (if k = 0 then c else 1) *
      (if k = 5 then c⁻¹ else 1) := ⟨_, fun k => rfl⟩
  have htp : ∀ k, tN k ^ p = 1 := by
    intro k
    rw [htN, mul_pow]
    split_ifs <;> simp [hpc, hcinvp]
  have hdet_t : (diagonal (fun j : Fin p => tN (j : ℕ))).det = 1 := by
    rw [det_diagonal, Fin.prod_univ_eq_prod_range tN p]
    simp only [htN]
    rw [Finset.prod_mul_distrib, singerUF_prod_range_ite 0 (by omega),
      singerUF_prod_range_ite 5 (by omega)]
    exact hcc
  have htnorm : ∀ k, h.bar (tN k) * tN k = 1 := fun k =>
    singerUF_norm_one_of_pow h hpq (htp k)
  exact singerUF_fermat_main_end h hp hodd hcu hc H hT hL hc0 hc1 hgt hodd_c hpq hεb hrel hE hE'
    hpow hD hDne hn hn2 hcc h2 sN hsN hsnorm hdet_s tN htN htnorm hdet_t

end CFSG.LieType.SeitzGeneration

end
