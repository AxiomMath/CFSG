module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7CombCount

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Finset

open scoped Classical

variable {P : Type} [Group P] [Fintype P] {L : Type} [Field L]

@[expose] noncomputable def sg6 (ζ u : L) : ℤ := (if u = ζ then 1 else 0) - (if u = ζ ^ 2 then 1 else 0)

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

theorem sg_zeta (hζ : IsPrimitiveRoot ζ 3) : sg6 ζ ζ = 1 := by
  unfold sg6
  rw [if_pos rfl, if_neg (ne_sq_of_prim hζ)]
  norm_num

theorem sg_zeta_sq (hζ : IsPrimitiveRoot ζ 3) : sg6 ζ (ζ ^ 2) = -1 := by
  unfold sg6
  rw [if_neg (ne_sq_of_prim hζ).symm, if_pos rfl]
  norm_num

theorem sg_one (hζ : IsPrimitiveRoot ζ 3) : sg6 ζ 1 = 0 := by
  unfold sg6
  rw [if_neg (one_ne_of_prim hζ), if_neg (one_ne_sq_of_prim hζ)]
  norm_num

theorem sg_triple (hζ : IsPrimitiveRoot ζ 3) {v : L} (hv : v ^ 3 = 1) :
    sg6 ζ (1 * v) + sg6 ζ (ζ * v) + sg6 ζ (ζ ^ 2 * v) = 0 := by
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

@[expose] noncomputable def Tcal6 (w : P → ℤ) (ζ : L) (v : P → L) (c' : L) : ℤ :=
  ∑ x, w x * sg6 ζ (c' * v x)

theorem Tcal_shift {w : P → ℤ} {v : P → L} (u c' : L) (t : P)
    (hw : ∀ x, w (x * t) = w x) (hv : ∀ x, v (x * t) = v x * u) :
    Tcal6 w ζ v c' = Tcal6 w ζ v (c' * u) := by
  unfold Tcal6
  calc ∑ x, w x * sg6 ζ (c' * v x) = ∑ x, w (x * t) * sg6 ζ (c' * v (x * t)) :=
        (Equiv.sum_comp (Equiv.mulRight t) (fun x => w x * sg6 ζ (c' * v x))).symm
    _ = ∑ x, w x * sg6 ζ (c' * u * v x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hw, hv, show c' * (v x * u) = c' * u * v x by ring]

theorem Tcal_mu3_zero (hζ : IsPrimitiveRoot ζ 3) {w : P → ℤ} {v : P → L}
    (hv : ∀ x, v x ^ 3 = 1) (t : P) (hw : ∀ x, w (x * t) = w x)
    (hvt : ∀ x, v (x * t) = v x * ζ) {c'' : L} (hc'' : c'' ^ 3 = 1) :
    Tcal6 w ζ v c'' = 0 := by
  have hz3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hz5 : ζ ^ 2 * ζ = 1 := by
    calc ζ ^ 2 * ζ = ζ ^ 3 := by ring
      _ = 1 := hz3
  have hsum3 : Tcal6 w ζ v 1 + Tcal6 w ζ v ζ + Tcal6 w ζ v (ζ ^ 2) = 0 := by
    unfold Tcal6
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    rw [← mul_add, ← mul_add, mul_eq_zero]
    right
    exact sg_triple hζ (hv x)
  have e1 : Tcal6 w ζ v 1 = Tcal6 w ζ v ζ := by
    have := Tcal_shift (w := w) (v := v) (ζ := ζ) ζ 1 t hw hvt
    rwa [one_mul] at this
  have e2 : Tcal6 w ζ v ζ = Tcal6 w ζ v (ζ ^ 2) := by
    have := Tcal_shift (w := w) (v := v) (ζ := ζ) ζ ζ t hw hvt
    rwa [← pow_two] at this
  have e3 : Tcal6 w ζ v (ζ ^ 2) = Tcal6 w ζ v 1 := by
    have := Tcal_shift (w := w) (v := v) (ζ := ζ) ζ (ζ ^ 2) t hw hvt
    rwa [hz5] at this
  have h1 : Tcal6 w ζ v 1 = 0 := by linarith
  rcases mu3_cases hζ hc'' with h | h | h
  · rw [h]; exact h1
  · rw [h, ← e1, h1]
  · rw [h, e3, h1]

end Shift

section Symm

variable {ζ : L}

theorem sum_sg_eq_zero6 {d : Fin 6 → P → L}
    (hsymm : ∀ z, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card) (z : P) :
    ∑ i, sg6 ζ (d i z) = 0 := by
  unfold sg6
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, hsymm z]
  simp

theorem mult_inv_eq6 (hζ : IsPrimitiveRoot ζ 3) {d : Fin 6 → P → L}
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
  have per_i : ∀ i, ∑ x, h x * sg6 ζ (d i (y * x)) =
      if (∀ x, c x = 1 → d i x = 1) then (∑ x, h x) * sg6 ζ (d i y) else 0 := by
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
      push Not at htriv
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
  have hsum0 : ∑ i, ∑ x, h x * sg6 ζ (d i (y * x)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.mul_sum, sum_sg_eq_zero6 hsymm (y * x), mul_zero]
  have h2 : ∑ i, (if (∀ x, c x = 1 → d i x = 1) then (∑ x, h x) * sg6 ζ (d i y) else 0) = 0 :=
    Eq.trans (Finset.sum_congr rfl (fun i _ => (per_i i).symm)) hsum0
  have h3 : (∑ x, h x) * ∑ i, (if (∀ x, c x = 1 → d i x = 1) then sg6 ζ (d i y) else 0) = 0 := by
    rw [Finset.mul_sum]
    refine Eq.trans ?_ h2
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hfin : ∑ i, (if (∀ x, c x = 1 → d i x = 1) then sg6 ζ (d i y) else 0) = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hhsum.ne'
    · exact h4
  have hpt : ∀ i, (if (∀ x, c x = 1 → d i x = 1) then sg6 ζ (d i y) else 0) =
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

section Pairs

variable {ζ : L}

theorem exists_ne_one_of_ne_fun {u : P → L} (h : u ≠ fun _ => 1) : ∃ x, u x ≠ 1 := by
  by_contra h'
  push Not at h'
  exact h (funext h')

theorem sq_ne_one_of {u : L} (hu3 : u ^ 3 = 1) (hu : u ≠ 1) : u ^ 2 ≠ 1 := by
  intro h
  apply hu
  linear_combination (-u) * hu3 + (u ^ 2 + 1) * h

theorem sq_ne_left {u v : P → L} (hu : ∀ x, u x ^ 3 = 1) (h : u ≠ fun x => v x ^ 2) :
    (fun x => u x ^ 2) ≠ v := by
  intro e
  apply h
  funext x
  have h1 := congrFun e x
  rw [← h1]
  exact (KA7.sq_sq_eq (hu x)).symm

theorem ne_sq_of {b c : P → L} (hc : ∀ x, c x ^ 3 = 1) (h : c ≠ fun x => b x ^ 2) :
    b ≠ fun x => c x ^ 2 := by
  intro e
  apply h
  funext x
  have h1 := congrFun e x
  rw [h1, KA7.sq_sq_eq (hc x)]

theorem exists_three (hζ : IsPrimitiveRoot ζ 3) {d : Fin 6 → P → L}
    (hdmul : ∀ i x y, d i (x * y) = d i x * d i y) (hdpow : ∀ i x, d i x ^ 3 = 1)
    (hfaith : ∀ x : P, (∀ i, d i x = 1) → x = 1) (hcard : Fintype.card P = 27) :
    ∃ i1 i2 i3 : Fin 6,
      (∃ x, d i1 x ≠ 1) ∧ d i2 ≠ d i1 ∧ d i2 ≠ (fun x => d i1 x ^ 2) ∧ (∃ x, d i2 x ≠ 1) ∧
      d i3 ≠ d i1 ∧ d i3 ≠ (fun x => d i1 x ^ 2) ∧ d i3 ≠ d i2 ∧
      d i3 ≠ (fun x => d i2 x ^ 2) ∧ (∃ x, d i3 x ≠ 1) := by
  haveI : Nontrivial P := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨x0, hx0⟩ := exists_ne (1 : P)
  obtain ⟨i1, hi1⟩ : ∃ i, d i x0 ≠ 1 := by
    by_contra h
    push Not at h
    exact hx0 (hfaith x0 h)
  obtain ⟨i2, hi2a, hi2a2, hi21⟩ : ∃ i, d i ≠ d i1 ∧ d i ≠ (fun x => d i1 x ^ 2) ∧
      d i ≠ (fun _ => 1) := by
    by_contra h
    push Not at h
    obtain ⟨x1, hx1, hax1, -⟩ :=
      KA7.common_kernel hζ (hdmul i1) (hdpow i1) (hdmul i1) (hdpow i1) hcard
    apply hx1
    apply hfaith x1
    intro i
    by_cases h1 : d i = d i1
    · rw [h1]; exact hax1
    · by_cases h2 : d i = fun x => d i1 x ^ 2
      · rw [h2]; simp [hax1]
      · rw [h i h1 h2]
  obtain ⟨i3, hi3a, hi3a2, hi3b, hi3b2, hi31⟩ : ∃ i, d i ≠ d i1 ∧ d i ≠ (fun x => d i1 x ^ 2) ∧
      d i ≠ d i2 ∧ d i ≠ (fun x => d i2 x ^ 2) ∧ d i ≠ (fun _ => 1) := by
    by_contra h
    push Not at h
    obtain ⟨x1, hx1, hax1, hbx1⟩ :=
      KA7.common_kernel hζ (hdmul i1) (hdpow i1) (hdmul i2) (hdpow i2) hcard
    apply hx1
    apply hfaith x1
    intro i
    by_cases h1 : d i = d i1
    · rw [h1]; exact hax1
    · by_cases h2 : d i = fun x => d i1 x ^ 2
      · rw [h2]; simp [hax1]
      · by_cases h3 : d i = d i2
        · rw [h3]; exact hbx1
        · by_cases h4 : d i = fun x => d i2 x ^ 2
          · rw [h4]; simp [hbx1]
          · rw [h i h1 h2 h3 h4]
  exact ⟨i1, i2, i3, ⟨x0, hi1⟩, hi2a, hi2a2, exists_ne_one_of_ne_fun hi21, hi3a, hi3a2,
    hi3b, hi3b2, exists_ne_one_of_ne_fun hi31⟩

end Pairs

section Count

variable {ζ : L}

theorem card_eval {d u : Fin 6 → P → L} (hu : Function.Injective u)
    (hcover : ∀ i, ∃ k, d i = u k) (g : P) :
    (univ.filter fun i => d i g = 1).card =
      ∑ k : Fin 6, if u k g = 1 then (univ.filter fun i => d i = u k).card else 0 := by
  have hR : ∀ k, (if u k g = 1 then (univ.filter fun i => d i = u k).card else 0) =
      ∑ i : Fin 6, if u k g = 1 then (if d i = u k then 1 else 0) else 0 := by
    intro k
    split_ifs with h
    · rw [Finset.card_filter]
    · simp
  rw [Finset.card_filter]
  simp only [hR]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨k0, hk0⟩ := hcover i
  rw [Finset.sum_eq_single k0]
  · rw [hk0]; simp
  · intro k _ hk
    rw [hk0]
    split_ifs with h1 h2
    · exact absurd (hu h2).symm hk
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ k0) h

theorem pairs_count (hζ : IsPrimitiveRoot ζ 3) {d : Fin 6 → P → L}
    (hdmul : ∀ i x y, d i (x * y) = d i x * d i y) (hdpow : ∀ i x, d i x ^ 3 = 1)
    (hsymm : ∀ z : P, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card)
    {a b c : P → L} (ha_mul : ∀ x y, a (x * y) = a x * a y) (ha_pow : ∀ x, a x ^ 3 = 1)
    (ha_nt : ∃ x, a x ≠ 1)
    (hb_mul : ∀ x y, b (x * y) = b x * b y) (hb_pow : ∀ x, b x ^ 3 = 1)
    (hb_nt : ∃ x, b x ≠ 1)
    (hc_mul : ∀ x y, c (x * y) = c x * c y) (hc_pow : ∀ x, c x ^ 3 = 1)
    (hc_nt : ∃ x, c x ≠ 1)
    (hab : b ≠ a) (hab2 : b ≠ fun x => a x ^ 2)
    (hac : c ≠ a) (hac2 : c ≠ fun x => a x ^ 2)
    (hbc : c ≠ b) (hbc2 : c ≠ fun x => b x ^ 2)
    (ia ib ic : Fin 6) (hia : d ia = a) (hib : d ib = b) (hic : d ic = c) :
    Function.Injective (![a, fun x => a x ^ 2, b, fun x => b x ^ 2, c, fun x => c x ^ 2] :
      Fin 6 → P → L) ∧
    (∀ i, ∃ k : Fin 6, d i = ![a, fun x => a x ^ 2, b, fun x => b x ^ 2, c, fun x => c x ^ 2] k) ∧
    (univ.filter fun i => d i = a).card = 1 ∧
    (univ.filter fun i => d i = (fun x => a x ^ 2)).card = 1 ∧
    (univ.filter fun i => d i = b).card = 1 ∧
    (univ.filter fun i => d i = (fun x => b x ^ 2)).card = 1 ∧
    (univ.filter fun i => d i = c).card = 1 ∧
    (univ.filter fun i => d i = (fun x => c x ^ 2)).card = 1 := by
  have sa := mult_inv_eq6 hζ hdmul hdpow hsymm ha_mul ha_pow ha_nt
  have sb := mult_inv_eq6 hζ hdmul hdpow hsymm hb_mul hb_pow hb_nt
  have sc := mult_inv_eq6 hζ hdmul hdpow hsymm hc_mul hc_pow hc_nt
  have ha2 : (fun x => a x ^ 2) ≠ a := KA7.sq_fun_ne hζ ha_pow ha_nt
  have hb2 : (fun x => b x ^ 2) ≠ b := KA7.sq_fun_ne hζ hb_pow hb_nt
  have hc2 : (fun x => c x ^ 2) ≠ c := KA7.sq_fun_ne hζ hc_pow hc_nt
  have hb2a : (fun x => b x ^ 2) ≠ a := sq_ne_left hb_pow hab2
  have hc2a : (fun x => c x ^ 2) ≠ a := sq_ne_left hc_pow hac2
  have hc2b : (fun x => c x ^ 2) ≠ b := sq_ne_left hc_pow hbc2
  have hbc2' : b ≠ fun x => c x ^ 2 := ne_sq_of hc_pow hbc2
  have hb2c : (fun x => b x ^ 2) ≠ c := sq_ne_left hb_pow hbc2'
  have hab_2 : (fun x => a x ^ 2) ≠ fun x => b x ^ 2 :=
    fun e => hab (KA7.sq_fun_inj ha_pow hb_pow e).symm
  have hac_2 : (fun x => a x ^ 2) ≠ fun x => c x ^ 2 :=
    fun e => hac (KA7.sq_fun_inj ha_pow hc_pow e).symm
  have hbc_2 : (fun x => b x ^ 2) ≠ fun x => c x ^ 2 :=
    fun e => hbc (KA7.sq_fun_inj hb_pow hc_pow e).symm
  let u : Fin 6 → P → L := ![a, fun x => a x ^ 2, b, fun x => b x ^ 2, c, fun x => c x ^ 2]
  have hu_inj : Function.Injective u := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;>
      first
      | rfl
      | exact absurd h hab.symm
      | exact absurd h ha2.symm
      | exact absurd h hb2a.symm
      | exact absurd h hac.symm
      | exact absurd h hc2a.symm
      | exact absurd h hab2.symm
      | exact absurd h hab_2
      | exact absurd h hac2.symm
      | exact absurd h hac_2
      | exact absurd h hb2.symm
      | exact absurd h hbc.symm
      | exact absurd h hbc2'
      | exact absurd h hb2c
      | exact absurd h hbc_2
      | exact absurd h hc2.symm
      | exact absurd h hab
      | exact absurd h.symm hab.symm
      | exact absurd h.symm ha2.symm
      | exact absurd h.symm hb2a.symm
      | exact absurd h.symm hac.symm
      | exact absurd h.symm hc2a.symm
      | exact absurd h.symm hab2.symm
      | exact absurd h.symm hab_2
      | exact absurd h.symm hac2.symm
      | exact absurd h.symm hac_2
      | exact absurd h.symm hb2.symm
      | exact absurd h.symm hbc.symm
      | exact absurd h.symm hbc2'
      | exact absurd h.symm hb2c
      | exact absurd h.symm hbc_2
      | exact absurd h.symm hc2.symm
      | exact absurd h ha2
      | exact absurd h hb2
      | exact absurd h hc2
  have hpt : ∀ i, ∑ k : Fin 6, (if d i = u k then 1 else 0) ≤ 1 := by
    intro i
    rw [← Finset.card_filter]
    apply Finset.card_le_one.mpr
    intro k hk k' hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact hu_inj (hk.symm.trans hk')
  have hdouble : ∑ k : Fin 6, (univ.filter fun i => d i = u k).card =
      ∑ i : Fin 6, ∑ k : Fin 6, (if d i = u k then 1 else 0) := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have htot : ∑ k : Fin 6, (univ.filter fun i => d i = u k).card ≤ 6 := by
    rw [hdouble]
    calc ∑ i : Fin 6, ∑ k : Fin 6, (if d i = u k then 1 else 0)
        ≤ ∑ _i : Fin 6, (1 : ℕ) := Finset.sum_le_sum (fun i _ => hpt i)
      _ = 6 := by simp
  have hexp : ∑ k : Fin 6, (univ.filter fun i => d i = u k).card =
      (univ.filter fun i => d i = a).card + (univ.filter fun i => d i = (fun x => a x ^ 2)).card +
      (univ.filter fun i => d i = b).card + (univ.filter fun i => d i = (fun x => b x ^ 2)).card +
      (univ.filter fun i => d i = c).card + (univ.filter fun i => d i = (fun x => c x ^ 2)).card := by
    rw [Fin.sum_univ_six]
    rfl
  have pa : 0 < (univ.filter fun i => d i = a).card :=
    Finset.card_pos.mpr ⟨ia, by simp [hia]⟩
  have pb : 0 < (univ.filter fun i => d i = b).card :=
    Finset.card_pos.mpr ⟨ib, by simp [hib]⟩
  have pc : 0 < (univ.filter fun i => d i = c).card :=
    Finset.card_pos.mpr ⟨ic, by simp [hic]⟩
  have h6 : (univ.filter fun i => d i = a).card = 1 ∧
      (univ.filter fun i => d i = (fun x => a x ^ 2)).card = 1 ∧
      (univ.filter fun i => d i = b).card = 1 ∧
      (univ.filter fun i => d i = (fun x => b x ^ 2)).card = 1 ∧
      (univ.filter fun i => d i = c).card = 1 ∧
      (univ.filter fun i => d i = (fun x => c x ^ 2)).card = 1 := by
    omega
  have htot_eq : ∑ i : Fin 6, ∑ k : Fin 6, (if d i = u k then 1 else 0) = 6 := by
    rw [← hdouble, hexp]
    omega
  have hpt_eq : ∀ i, ∑ k : Fin 6, (if d i = u k then 1 else 0) = 1 := by
    have key := (Finset.sum_eq_sum_iff_of_le (s := univ)
      (f := fun i => ∑ k : Fin 6, (if d i = u k then 1 else 0)) (g := fun _ => 1)
      (fun i _ => hpt i)).mp (by rw [htot_eq]; simp)
    intro i
    exact key i (Finset.mem_univ i)
  have hcover : ∀ i, ∃ k, d i = u k := by
    intro i
    by_contra h
    push Not at h
    have h1 := hpt_eq i
    simp [h] at h1
  exact ⟨hu_inj, fun i => by
      obtain ⟨k, hk⟩ := hcover i
      exact ⟨k, hk⟩, h6.1, h6.2.1, h6.2.2.1, h6.2.2.2.1, h6.2.2.2.2.1, h6.2.2.2.2.2⟩

theorem exists_gt (hζ : IsPrimitiveRoot ζ 3) {d : Fin 6 → P → L}
    (hdmul : ∀ i x y, d i (x * y) = d i x * d i y) (hdpow : ∀ i x, d i x ^ 3 = 1)
    (hfaith : ∀ x : P, (∀ i, d i x = 1) → x = 1) (hcard : Fintype.card P = 27)
    (hsymm : ∀ z : P, (univ.filter fun i => d i z = ζ).card =
      (univ.filter fun i => d i z = ζ ^ 2).card) :
    ∃ g t : P, g ≠ 1 ∧ (univ.filter fun i => d i g = 1).card = 4 ∧
      ∀ i, d i g = 1 → d i t ≠ 1 := by
  obtain ⟨i1, i2, i3, ⟨x1, hx1⟩, hb1, hb2, ⟨y2, hy2⟩, hc1, hc2, hc3, hc4, ⟨y3, hy3⟩⟩ :=
    exists_three hζ hdmul hdpow hfaith hcard
  let u : Fin 6 → P → L := ![d i1, fun x => d i1 x ^ 2, d i2, fun x => d i2 x ^ 2,
    d i3, fun x => d i3 x ^ 2]
  obtain ⟨hu, hcov, ca, ca2, cb, cb2, cc, cc2⟩ :=
    pairs_count hζ hdmul hdpow hsymm (hdmul i1) (hdpow i1) ⟨x1, hx1⟩ (hdmul i2) (hdpow i2)
      ⟨y2, hy2⟩ (hdmul i3) (hdpow i3) ⟨y3, hy3⟩ hb1 hb2 hc1 hc2 hc3 hc4 i1 i2 i3 rfl rfl rfl
  obtain ⟨g, hg1, hga, hgb⟩ :=
    KA7.common_kernel hζ (hdmul i1) (hdpow i1) (hdmul i2) (hdpow i2) hcard
  have hcg : d i3 g ≠ 1 := by
    intro h
    apply hg1
    apply hfaith g
    intro i
    obtain ⟨k, hk⟩ := hcov i
    rw [hk]
    fin_cases k <;> simp [hga, hgb, h]
  have hcard4 : (univ.filter fun i => d i g = 1).card = 4 := by
    have v1 : (fun x => d i1 x ^ 2) g = 1 := by
      show d i1 g ^ 2 = 1
      rw [hga, one_pow]
    have v3 : (fun x => d i2 x ^ 2) g = 1 := by
      show d i2 g ^ 2 = 1
      rw [hgb, one_pow]
    have v5 : ¬ ((fun x => d i3 x ^ 2) g = 1) := fun h => sq_ne_one_of (hdpow i3 g) hcg h
    have c0 : (univ.filter fun i => d i = u 0).card = 1 := ca
    have c1 : (univ.filter fun i => d i = u 1).card = 1 := ca2
    have c2 : (univ.filter fun i => d i = u 2).card = 1 := cb
    have c3 : (univ.filter fun i => d i = u 3).card = 1 := cb2
    have e0 : u 0 g = 1 := hga
    have e1 : u 1 g = 1 := v1
    have e2 : u 2 g = 1 := hgb
    have e3 : u 3 g = 1 := v3
    have e4 : ¬ u 4 g = 1 := hcg
    have e5 : ¬ u 5 g = 1 := v5
    rw [card_eval hu hcov g, Fin.sum_univ_six, if_pos e0, if_pos e1, if_pos e2, if_pos e3,
      if_neg e4, if_neg e5, c0, c1, c2, c3]
  have ka := KA7.ker_card hζ (hdmul i1) (hdpow i1) ⟨x1, hx1⟩ hcard
  have kb := KA7.ker_card hζ (hdmul i2) (hdpow i2) ⟨y2, hy2⟩ hcard
  obtain ⟨t, ht1, ht2⟩ : ∃ t, d i1 t ≠ 1 ∧ d i2 t ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (univ : Finset P) ⊆
        (univ.filter fun x => d i1 x = 1) ∪ (univ.filter fun x => d i2 x = 1) := by
      intro x _
      by_cases hx : d i1 x = 1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x hx⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (univ.filter fun x => d i1 x = 1)
      (univ.filter fun x => d i2 x = 1)
    have h3 : (univ : Finset P).card = 27 := by rw [Finset.card_univ, hcard]
    omega
  refine ⟨g, t, hg1, hcard4, fun i hi => ?_⟩
  obtain ⟨k, hk⟩ := hcov i
  rw [hk] at hi ⊢
  fin_cases k
  · simpa using ht1
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
    exact sq_ne_one_of (hdpow i1 t) ht1
  · simpa using ht2
  · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
    exact sq_ne_one_of (hdpow i2 t) ht2
  · exact absurd (by simpa using hi) hcg
  · exfalso
    apply sq_ne_one_of (hdpow i3 g) hcg
    simpa using hi

end Count

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
