module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Finset

open scoped Classical

variable {P : Type} [Group P] [Fintype P] {L : Type} [Field L]

noncomputable def sg (ζ u : L) : ℤ := (if u = ζ then 1 else 0) - (if u = ζ ^ 2 then 1 else 0)

section Facts

variable {ζ : L}

theorem mu3_cases (hζ : IsPrimitiveRoot ζ 3) {u : L} (hu : u ^ 3 = 1) :
    u = 1 ∨ u = ζ ∨ u = ζ ^ 2 := by
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hu
  interval_cases i
  · exact Or.inl (pow_zero ζ)
  · exact Or.inr (Or.inl (pow_one ζ))
  · exact Or.inr (Or.inr rfl)

theorem ne_one_of_prim (hζ : IsPrimitiveRoot ζ 3) : ζ ≠ 1 :=
  hζ.ne_one (by norm_num)

theorem sq_ne_one_of_prim (hζ : IsPrimitiveRoot ζ 3) : ζ ^ 2 ≠ 1 :=
  hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)

theorem ne_sq_of_prim (hζ : IsPrimitiveRoot ζ 3) : ζ ≠ ζ ^ 2 := by
  intro h
  have hz0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  apply ne_one_of_prim hζ
  have : ζ * (ζ - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hz0
  · exact sub_eq_zero.mp h0

theorem one_ne_sq_of_prim (hζ : IsPrimitiveRoot ζ 3) : (1 : L) ≠ ζ ^ 2 :=
  fun h => sq_ne_one_of_prim hζ h.symm

theorem one_ne_of_prim (hζ : IsPrimitiveRoot ζ 3) : (1 : L) ≠ ζ :=
  fun h => ne_one_of_prim hζ h.symm

theorem sg_zeta (hζ : IsPrimitiveRoot ζ 3) : sg ζ ζ = 1 := by
  unfold sg
  rw [if_pos rfl, if_neg (ne_sq_of_prim hζ)]
  norm_num

theorem sg_zeta_sq (hζ : IsPrimitiveRoot ζ 3) : sg ζ (ζ ^ 2) = -1 := by
  unfold sg
  rw [if_neg (ne_sq_of_prim hζ).symm, if_pos rfl]
  norm_num

theorem sg_one (hζ : IsPrimitiveRoot ζ 3) : sg ζ 1 = 0 := by
  unfold sg
  rw [if_neg (one_ne_of_prim hζ), if_neg (one_ne_sq_of_prim hζ)]
  norm_num

theorem sg_triple (hζ : IsPrimitiveRoot ζ 3) {v : L} (hv : v ^ 3 = 1) :
    sg ζ (1 * v) + sg ζ (ζ * v) + sg ζ (ζ ^ 2 * v) = 0 := by
  have hz3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hz4 : ζ ^ 2 * ζ ^ 2 = ζ := by
    calc ζ ^ 2 * ζ ^ 2 = ζ * ζ ^ 3 := by ring
      _ = ζ := by rw [hz3, mul_one]
  have hz5 : ζ ^ 2 * ζ = 1 := by
    calc ζ ^ 2 * ζ = ζ ^ 3 := by ring
      _ = 1 := hz3
  have hz6 : ζ * ζ ^ 2 = 1 := by rw [mul_comm]; exact hz5
  rcases mu3_cases hζ hv with rfl | rfl | rfl
  · simp only [one_mul, mul_one]
    rw [sg_one hζ, sg_zeta hζ, sg_zeta_sq hζ]
    norm_num
  · rw [one_mul, ← pow_two, hz5, sg_zeta hζ, sg_zeta_sq hζ, sg_one hζ]
    norm_num
  · rw [one_mul, hz6, hz4, sg_zeta_sq hζ, sg_one hζ, sg_zeta hζ]
    norm_num

theorem char_one {c : P → L} (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hcpow : ∀ x, c x ^ 3 = 1) : c 1 = 1 := by
  have h1 : c 1 = c 1 * c 1 := by rw [← hcmul, mul_one]
  have hne : c 1 ^ 3 = 1 := hcpow 1
  have hne0 : c 1 ≠ 0 := by
    intro h0
    rw [h0] at hne
    norm_num at hne
  have : c 1 * (c 1 - 1) = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hne0
  · exact sub_eq_zero.mp h0

end Facts

section Triv

variable {ζ : L}

theorem triv_pow (hζ : IsPrimitiveRoot ζ 3) {c d : P → L}
    (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hdmul : ∀ x y, d (x * y) = d x * d y)
    {y : P} (hy : c y = ζ) (htriv : ∀ x, c x = 1 → d x = 1) (x : P) :
    ∃ j : ℕ, j < 3 ∧ c x = ζ ^ j ∧ d x = d y ^ j := by
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  have hcinv : c y⁻¹ * ζ = 1 := by
    rw [← hy, ← hcmul, inv_mul_cancel, hc1]
  have hz3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  rcases mu3_cases hζ (hcpow x) with h | h | h
  ·
    exact ⟨0, by norm_num, by rw [h]; simp, by rw [pow_zero, htriv x h]⟩
  ·
    refine ⟨1, by norm_num, by rw [h, pow_one], ?_⟩
    have hh : c (y⁻¹ * x) = 1 := by rw [hcmul, h]; exact hcinv
    have hdh : d (y⁻¹ * x) = 1 := htriv _ hh
    calc d x = d (y * (y⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = d y * d (y⁻¹ * x) := hdmul _ _
      _ = d y ^ 1 := by rw [hdh, mul_one, pow_one]
  ·
    refine ⟨2, by norm_num, by rw [h], ?_⟩
    have hcyy : c (y * y) = ζ ^ 2 := by rw [hcmul, hy]; ring
    have hcinv2 : c (y * y)⁻¹ * ζ ^ 2 = 1 := by
      rw [← hcyy, ← hcmul, inv_mul_cancel, hc1]
    have hh : c ((y * y)⁻¹ * x) = 1 := by
      rw [hcmul, h]; exact hcinv2
    have hdh : d ((y * y)⁻¹ * x) = 1 := htriv _ hh
    calc d x = d ((y * y) * ((y * y)⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = d (y * y) * d ((y * y)⁻¹ * x) := hdmul _ _
      _ = d y ^ 2 := by rw [hdh, mul_one, hdmul, sq]

end Triv

section Shift

variable {ζ : L}

noncomputable def Tcal (w : P → ℤ) (ζ : L) (v : P → L) (c' : L) : ℤ :=
  ∑ x, w x * sg ζ (c' * v x)

theorem Tcal_shift {w : P → ℤ} {v : P → L} (u c' : L) (t : P)
    (hw : ∀ x, w (x * t) = w x) (hv : ∀ x, v (x * t) = v x * u) :
    Tcal w ζ v c' = Tcal w ζ v (c' * u) := by
  unfold Tcal
  calc ∑ x, w x * sg ζ (c' * v x) = ∑ x, w (x * t) * sg ζ (c' * v (x * t)) :=
        (Equiv.sum_comp (Equiv.mulRight t) (fun x => w x * sg ζ (c' * v x))).symm
    _ = ∑ x, w x * sg ζ (c' * u * v x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hw, hv, show c' * (v x * u) = c' * u * v x by ring]

theorem Tcal_mu3_zero (hζ : IsPrimitiveRoot ζ 3) {w : P → ℤ} {v : P → L}
    (hv : ∀ x, v x ^ 3 = 1) (t : P) (hw : ∀ x, w (x * t) = w x)
    (hvt : ∀ x, v (x * t) = v x * ζ) {c'' : L} (hc'' : c'' ^ 3 = 1) :
    Tcal w ζ v c'' = 0 := by
  have hz3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hz5 : ζ ^ 2 * ζ = 1 := by
    calc ζ ^ 2 * ζ = ζ ^ 3 := by ring
      _ = 1 := hz3
  have hsum3 : Tcal w ζ v 1 + Tcal w ζ v ζ + Tcal w ζ v (ζ ^ 2) = 0 := by
    unfold Tcal
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    rw [← mul_add, ← mul_add, mul_eq_zero]
    right
    exact sg_triple hζ (hv x)
  have e1 : Tcal w ζ v 1 = Tcal w ζ v ζ := by
    have := Tcal_shift (w := w) (v := v) (ζ := ζ) ζ 1 t hw hvt
    rwa [one_mul] at this
  have e2 : Tcal w ζ v ζ = Tcal w ζ v (ζ ^ 2) := by
    have := Tcal_shift (w := w) (v := v) (ζ := ζ) ζ ζ t hw hvt
    rwa [← pow_two] at this
  have e3 : Tcal w ζ v (ζ ^ 2) = Tcal w ζ v 1 := by
    have := Tcal_shift (w := w) (v := v) (ζ := ζ) ζ (ζ ^ 2) t hw hvt
    rwa [hz5] at this
  have h1 : Tcal w ζ v 1 = 0 := by linarith
  rcases mu3_cases hζ hc'' with h | h | h
  · rw [h]; exact h1
  · rw [h, ← e1, h1]
  · rw [h, e3, h1]

end Shift

section Symm

variable {ζ : L}

theorem sum_sg_eq_zero {d : Fin 7 → P → L}
    (hsymm : ∀ z, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card) (z : P) :
    ∑ i, sg ζ (d i z) = 0 := by
  unfold sg
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hsymm z]
  simp

theorem mult_inv_eq (hζ : IsPrimitiveRoot ζ 3) {d : Fin 7 → P → L}
    (hdmul : ∀ i x y, d i (x * y) = d i x * d i y) (hdpow : ∀ i x, d i x ^ 3 = 1)
    (hsymm : ∀ z, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card)
    {c : P → L} (hcmul : ∀ x y, c (x * y) = c x * c y) (hcpow : ∀ x, c x ^ 3 = 1)
    (hcnt : ∃ x, c x ≠ 1) :
    (univ.filter fun i => d i = c).card =
      (univ.filter fun i => d i = fun x => c x ^ 2).card := by
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  obtain ⟨x0, hx0⟩ := hcnt
  obtain ⟨y, hy⟩ : ∃ y, c y = ζ := by
    rcases mu3_cases hζ (hcpow x0) with h | h | h
    · exact absurd h hx0
    · exact ⟨x0, h⟩
    · refine ⟨x0 * x0, ?_⟩
      rw [hcmul, h]
      calc ζ ^ 2 * ζ ^ 2 = ζ * ζ ^ 3 := by ring
        _ = ζ := by rw [hζ.pow_eq_one, mul_one]
  let h : P → ℤ := fun x => if c x = 1 then 1 else 0
  have hh1 : h 1 = 1 := by simp [h, hc1]
  have hhnn : ∀ x, 0 ≤ h x := fun x => by
    simp only [h]
    split_ifs <;> norm_num
  have hhsum : 0 < ∑ x, h x :=
    lt_of_lt_of_le (by rw [hh1]; norm_num) (Finset.single_le_sum (fun x _ => hhnn x)
      (Finset.mem_univ 1))
  have per_i : ∀ i, ∑ x, h x * sg ζ (d i (y * x)) =
      if (∀ x, c x = 1 → d i x = 1) then (∑ x, h x) * sg ζ (d i y) else 0 := by
    intro i
    simp only [hdmul]
    by_cases htriv : ∀ x, c x = 1 → d i x = 1
    · rw [if_pos htriv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hcx : c x = 1
      · simp [h, hcx, htriv x hcx]
      · simp [h, hcx]
    · rw [if_neg htriv]
      push_neg at htriv
      obtain ⟨x1, hx1c, hx1d⟩ := htriv
      obtain ⟨t, ht1, htζ⟩ : ∃ t, c t = 1 ∧ d i t = ζ := by
        rcases mu3_cases hζ (hdpow i x1) with h' | h' | h'
        · exact absurd h' hx1d
        · exact ⟨x1, hx1c, h'⟩
        · refine ⟨x1 * x1, by rw [hcmul, hx1c, mul_one], ?_⟩
          rw [hdmul, h']
          calc ζ ^ 2 * ζ ^ 2 = ζ * ζ ^ 3 := by ring
            _ = ζ := by rw [hζ.pow_eq_one, mul_one]
      have hw : ∀ x, h (x * t) = h x := fun x => by
        simp only [h, hcmul, ht1, mul_one]
      have hv : ∀ x, d i (x * t) = d i x * ζ := fun x => by rw [hdmul, htζ]
      have hT := Tcal_mu3_zero hζ (w := h) (v := d i) (fun x => hdpow i x) t hw hv
        (c'' := d i y) (hdpow i y)
      exact hT
  have hsum0 : ∑ i, ∑ x, h x * sg ζ (d i (y * x)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.mul_sum, sum_sg_eq_zero hsymm (y * x), mul_zero]
  have h2 : ∑ i, (if (∀ x, c x = 1 → d i x = 1) then (∑ x, h x) * sg ζ (d i y) else 0) = 0 :=
    Eq.trans (Finset.sum_congr rfl (fun i _ => (per_i i).symm)) hsum0
  have h3 : (∑ x, h x) * ∑ i, (if (∀ x, c x = 1 → d i x = 1) then sg ζ (d i y) else 0) = 0 := by
    rw [Finset.mul_sum]
    refine Eq.trans ?_ h2
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hfin : ∑ i, (if (∀ x, c x = 1 → d i x = 1) then sg ζ (d i y) else 0) = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hhsum.ne'
    · exact h4
  have hpt : ∀ i, (if (∀ x, c x = 1 → d i x = 1) then sg ζ (d i y) else 0) =
      (if d i = c then (1 : ℤ) else 0) - (if d i = fun x => c x ^ 2 then 1 else 0) := by
    intro i
    by_cases hA : d i = c
    · have htriv : ∀ x, c x = 1 → d i x = 1 := fun x hx => by rw [hA]; exact hx
      have hB : ¬ d i = fun x => c x ^ 2 := by
        intro hB
        have h1 : d i y = c y := congrFun hA y
        have h2' : d i y = c y ^ 2 := congrFun hB y
        rw [h1, hy] at h2'
        exact ne_sq_of_prim hζ h2'
      rw [if_pos htriv, if_pos hA, if_neg hB, hA, hy, sg_zeta hζ]
      norm_num
    · by_cases hB : d i = fun x => c x ^ 2
      · have htriv : ∀ x, c x = 1 → d i x = 1 := fun x hx => by
          have this : d i x = c x ^ 2 := congrFun hB x
          rw [this, hx, one_pow]
        have hdy : d i y = ζ ^ 2 := by
          have this : d i y = c y ^ 2 := congrFun hB y
          rw [this, hy]
        rw [if_pos htriv, if_neg hA, if_pos hB, hdy, sg_zeta_sq hζ]
        norm_num
      · rw [if_neg hA, if_neg hB, sub_zero]
        by_cases htriv : ∀ x, c x = 1 → d i x = 1
        · rw [if_pos htriv]
          rcases mu3_cases hζ (hdpow i y) with h4 | h4 | h4
          · rw [h4, sg_one hζ]
          · exfalso
            apply hA
            funext x
            obtain ⟨j, _, hcx, hdx⟩ := triv_pow hζ hcmul hcpow (fun x y => hdmul i x y) hy htriv x
            rw [hdx, h4, hcx]
          · exfalso
            apply hB
            funext x
            obtain ⟨j, _, hcx, hdx⟩ := triv_pow hζ hcmul hcpow (fun x y => hdmul i x y) hy htriv x
            rw [hdx, h4, hcx]
            ring
        · rw [if_neg htriv]
  have hsum_eq : ∑ i, ((if d i = c then (1 : ℤ) else 0) -
      (if d i = fun x => c x ^ 2 then 1 else 0)) = 0 :=
    Eq.trans (Finset.sum_congr rfl (fun i _ => (hpt i).symm)) hfin
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole] at hsum_eq
  have hcast : ((univ.filter fun i => d i = c).card : ℤ) =
      ((univ.filter fun i => d i = fun x => c x ^ 2).card : ℤ) := by linarith
  exact_mod_cast hcast

end Symm

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end
