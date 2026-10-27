module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Blk
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix

abbrev N24Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def n24Cj (g : GL (Fin 3) (ZMod 2)) (m : N24Mat3) : N24Mat3 :=
  (g : N24Mat3) * m * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : N24Mat3)

theorem n24Cj_mul (g h : GL (Fin 3) (ZMod 2)) (m : N24Mat3) :
    n24Cj (g * h) m = n24Cj g (n24Cj h m) := by
  simp only [n24Cj, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem n24Cj_one (m : N24Mat3) : n24Cj 1 m = m := by
  simp [n24Cj]

theorem n24Cj_add (g : GL (Fin 3) (ZMod 2)) (m m' : N24Mat3) :
    n24Cj g (m + m') = n24Cj g m + n24Cj g m' := by
  simp only [n24Cj, Matrix.mul_add, Matrix.add_mul]

theorem n24Cj_zero (g : GL (Fin 3) (ZMod 2)) : n24Cj g 0 = 0 := by
  simp [n24Cj]

theorem n24Cj_inv_cancel (g : GL (Fin 3) (ZMod 2)) (m : N24Mat3) :
    n24Cj g⁻¹ (n24Cj g m) = m := by
  rw [← n24Cj_mul, inv_mul_cancel, n24Cj_one]

@[expose] def N24Coc (f : GL (Fin 3) (ZMod 2) → N24Mat3) : Prop :=
  ∀ A B : GL (Fin 3) (ZMod 2), f (A * B) = f A + n24Cj A (f B)

theorem N24Coc.map_one {f : GL (Fin 3) (ZMod 2) → N24Mat3} (hf : N24Coc f) : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one, n24Cj_one] at h
  exact (add_right_inj (f 1)).mp (by rw [add_zero]; exact h.symm)

theorem N24Coc.map_pow {f : GL (Fin 3) (ZMod 2) → N24Mat3} (hf : N24Coc f)
    (g : GL (Fin 3) (ZMod 2)) (n : ℕ) :
    f (g ^ n) = ∑ i ∈ Finset.range n, n24Cj (g ^ i) (f g) := by
  induction n with
  | zero => simp [hf.map_one]
  | succ n ih => rw [pow_succ, hf, ih, Finset.sum_range_succ]

theorem N24Coc.add_cob {f : GL (Fin 3) (ZMod 2) → N24Mat3} (hf : N24Coc f) (m : N24Mat3) :
    N24Coc (fun A => f A + (n24Cj A m + m)) := by
  intro A B
  show f (A * B) + (n24Cj (A * B) m + m) =
    f A + (n24Cj A m + m) + n24Cj A (f B + (n24Cj B m + m))
  have e : f A + (n24Cj A m + m) + n24Cj A (f B + (n24Cj B m + m)) =
      (f A + n24Cj A (f B) + (n24Cj A (n24Cj B m) + m)) + (n24Cj A m + n24Cj A m) := by
    rw [n24Cj_add, n24Cj_add]
    abel
  rw [e, n24_add_self, add_zero, hf A B, n24Cj_mul]

theorem N24Coc.vanish {f : GL (Fin 3) (ZMod 2) → N24Mat3} (hf : N24Coc f)
    {a b : GL (Fin 3) (ZMod 2)} (ha : f a = 0) (hb : f b = 0) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set (GL (Fin 3) (ZMod 2))), f g = 0 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ha
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hb
  | one => exact hf.map_one
  | mul x y _ _ hx hy => rw [hf, hx, hy, n24Cj_zero, add_zero]
  | inv x _ hx =>
    have h := hf x x⁻¹
    rw [mul_inv_cancel, hf.map_one, hx, zero_add] at h
    have h' := congrArg (n24Cj x⁻¹) h
    rw [n24Cj_inv_cancel, n24Cj_zero] at h'
    exact h'.symm

@[expose] def n24A : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide, by decide⟩

@[expose] def n24B : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 1, 0, 1; 1, 1, 0], !![1, 0, 1; 1, 0, 0; 1, 1, 1], by decide, by decide⟩

@[expose] def n24C : GL (Fin 3) (ZMod 2) := n24A * (n24B * (n24A * (n24B * n24B)))

theorem n24A_sq : n24A * n24A = 1 := Units.ext (by decide)

theorem n24B_cube : n24B ^ 3 = 1 := Units.ext (by decide)

theorem n24AB_pow7 : (n24A * n24B) ^ 7 = 1 := Units.ext (by decide)

theorem n24C_pow4 : n24C ^ 4 = 1 := Units.ext (by decide)

theorem n24_neg (X : N24Mat3) : -X = X := neg_eq_of_add_eq_zero_right (n24_add_self X)

theorem n24_eq_of_add_eq_zero {P Q : N24Mat3} (h : P + Q = 0) : P = Q :=
  (eq_neg_of_add_eq_zero_left h).trans (n24_neg Q)

theorem n24_eq_top_of_dvd_42 {R : Subgroup (GL (Fin 3) (ZMod 2))} (h : 42 ∣ Nat.card R) :
    R = ⊤ := by
  have hs := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  have hc := CFSG.ComponentClassification.GHarris.card_GL32_gh
  have hmul : Nat.card R * R.index = 168 := by rw [R.card_mul_index, hc]
  obtain ⟨k, hk⟩ := h
  have hpos : 0 < Nat.card R := Nat.card_pos
  have hk4 : k ≤ 4 := by
    by_contra hlt
    have : 42 * 5 ≤ Nat.card R := by rw [hk]; exact Nat.mul_le_mul_left 42 (by omega)
    have h1 : 1 ≤ R.index := Nat.one_le_iff_ne_zero.mpr (Subgroup.index_ne_zero_of_finite)
    nlinarith
  have hcore := R.index_normalCore_le_factorial_index
  interval_cases k
  · omega
  · have h3 : R.index = 4 := by rw [hk] at hmul; omega
    rcases hs.eq_bot_or_eq_top_of_normal R.normalCore with hb | ht
    · rw [hb, Subgroup.index_bot, hc, h3] at hcore
      exact absurd hcore (by decide)
    · have hR : R = ⊤ := top_le_iff.mp (ht ▸ R.normalCore_le)
      rw [hR, Subgroup.index_top] at h3
      exact absurd h3 (by decide)
  · have h3 : R.index = 2 := by rw [hk] at hmul; omega
    rcases hs.eq_bot_or_eq_top_of_normal R.normalCore with hb | ht
    · rw [hb, Subgroup.index_bot, hc, h3] at hcore
      exact absurd hcore (by decide)
    · have hR : R = ⊤ := top_le_iff.mp (ht ▸ R.normalCore_le)
      rw [hR, Subgroup.index_top] at h3
      exact absurd h3 (by decide)
  · rw [hk] at hmul
    omega
  · exact Subgroup.eq_top_of_card_eq R (by rw [hk, hc])

theorem n24_closure_AB :
    Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2))) = ⊤ := by
  apply n24_eq_top_of_dvd_42
  have ha : n24A ∈ Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2))) :=
    Subgroup.subset_closure (by simp)
  have hb : n24B ∈ Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2))) :=
    Subgroup.subset_closure (by simp)
  have hab := Subgroup.mul_mem _ ha hb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have o2 : orderOf n24A = 2 := orderOf_eq_prime (by rw [pow_two]; exact n24A_sq) (by decide)
  have o3 : orderOf n24B = 3 := orderOf_eq_prime n24B_cube (by decide)
  have o7 : orderOf (n24A * n24B) = 7 := orderOf_eq_prime n24AB_pow7 (by decide)
  have d2 : 2 ∣ Nat.card (Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2)))) :=
    by have := Subgroup.orderOf_dvd_natCard _ ha; rwa [o2] at this
  have d3 : 3 ∣ Nat.card (Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2)))) :=
    by have := Subgroup.orderOf_dvd_natCard _ hb; rwa [o3] at this
  have d7 : 7 ∣ Nat.card (Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2)))) :=
    by have := Subgroup.orderOf_dvd_natCard _ hab; rwa [o7] at this
  have d6 : 2 * 3 ∣ Nat.card (Subgroup.closure ({n24A, n24B} : Set (GL (Fin 3) (ZMod 2)))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d2 d3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime (2 * 3) 7) d6 d7

private instance n24MatDecEq : DecidableEq N24Mat3 := inferInstance

private instance n24MatFintype : Fintype N24Mat3 := inferInstance

theorem n24_h1_aux : ∀ x : N24Mat3, x + n24Cj n24A x = 0 →
    (∑ k ∈ Finset.range 7, n24Cj ((n24A * n24B) ^ k) x) = 0 →
    (∑ k ∈ Finset.range 4, n24Cj (n24C ^ k) (x + n24Cj (n24A * n24B) x)) = 0 →
    ∃ m : N24Mat3, n24Cj n24B m = m ∧ x = n24Cj n24A m + m := by
  decide +kernel

theorem y7c_n24_h1 (f : GL (Fin 3) (ZMod 2) → Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hf : ∀ A B : GL (Fin 3) (ZMod 2), f (A * B) = f A +
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * f B *
        ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ∃ m : Matrix (Fin 3) (Fin 3) (ZMod 2), ∀ A : GL (Fin 3) (ZMod 2),
      f A = (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m *
        ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) + m := by
  have hc : N24Coc f := hf
  obtain ⟨y, hy⟩ : ∃ y, f n24B = y := ⟨_, rfl⟩
  have hy3 : y + n24Cj n24B y + n24Cj (n24B * n24B) y = 0 := by
    have h := hc.map_pow n24B 3
    rw [n24B_cube, hc.map_one, hy] at h
    simpa [Finset.sum_range_succ, pow_two, n24Cj_one] using h.symm
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = n24Cj n24B y := ⟨_, rfl⟩
  have hym0 : n24Cj n24B m0 + m0 = y := by
    rw [hm0, ← n24Cj_mul]
    have h : y + (n24Cj n24B y + n24Cj (n24B * n24B) y) = 0 := by
      rw [← add_assoc]; exact hy3
    have h' := n24_eq_of_add_eq_zero h
    rw [add_comm, ← h']
  obtain ⟨g, hgdef⟩ : ∃ g : GL (Fin 3) (ZMod 2) → N24Mat3,
      g = fun A => f A + (n24Cj A m0 + m0) := ⟨_, rfl⟩
  have hg : N24Coc g := by rw [hgdef]; exact hc.add_cob m0
  have hgB : g n24B = 0 := by
    rw [hgdef]
    show f n24B + (n24Cj n24B m0 + m0) = 0
    rw [hy, hym0]
    exact n24_add_self y
  obtain ⟨x, hx⟩ : ∃ x, g n24A = x := ⟨_, rfl⟩
  have h1 : x + n24Cj n24A x = 0 := by
    have h := hg n24A n24A
    rw [n24A_sq, hg.map_one, hx] at h
    exact h.symm
  have hw : g (n24A * n24B) = x := by rw [hg, hgB, n24Cj_zero, add_zero, hx]
  have h3 : ∑ k ∈ Finset.range 7, n24Cj ((n24A * n24B) ^ k) x = 0 := by
    have h := hg.map_pow (n24A * n24B) 7
    rw [n24AB_pow7, hg.map_one, hw] at h
    exact h.symm
  have e1 : g (n24B * n24B) = 0 := by rw [hg, hgB, n24Cj_zero, add_zero]
  have e2 : g (n24A * (n24B * n24B)) = x := by rw [hg, e1, n24Cj_zero, add_zero, hx]
  have e3 : g (n24B * (n24A * (n24B * n24B))) = n24Cj n24B x := by
    rw [hg, hgB, e2, zero_add]
  have e4 : g n24C = x + n24Cj (n24A * n24B) x := by
    unfold n24C
    rw [hg, e3, ← n24Cj_mul, hx]
  have h4 : ∑ k ∈ Finset.range 4, n24Cj (n24C ^ k) (x + n24Cj (n24A * n24B) x) = 0 := by
    have h := hg.map_pow n24C 4
    rw [n24C_pow4, hg.map_one, e4] at h
    exact h.symm
  obtain ⟨m, hbm, hxm⟩ := n24_h1_aux x h1 h3 h4
  obtain ⟨g', hg'def⟩ : ∃ g' : GL (Fin 3) (ZMod 2) → N24Mat3,
      g' = fun A => g A + (n24Cj A m + m) := ⟨_, rfl⟩
  have hg' : N24Coc g' := by rw [hg'def]; exact hg.add_cob m
  have hg'A : g' n24A = 0 := by
    rw [hg'def]
    show g n24A + (n24Cj n24A m + m) = 0
    rw [hx, ← hxm]
    exact n24_add_self x
  have hg'B : g' n24B = 0 := by
    rw [hg'def]
    show g n24B + (n24Cj n24B m + m) = 0
    rw [hgB, hbm, n24_add_self, zero_add]
  refine ⟨m + m0, fun A => ?_⟩
  have hv := hg'.vanish hg'A hg'B A (by rw [n24_closure_AB]; exact Subgroup.mem_top A)
  have hv' : f A + (n24Cj A m0 + m0) + (n24Cj A m + m) = 0 := by
    rw [hg'def, hgdef] at hv
    exact hv
  show f A = n24Cj A (m + m0) + (m + m0)
  apply n24_eq_of_add_eq_zero
  rw [n24Cj_add]
  calc f A + (n24Cj A m + n24Cj A m0 + (m + m0))
      = f A + (n24Cj A m0 + m0) + (n24Cj A m + m) := by abel
    _ = 0 := hv'

theorem n24_commutant : ∀ m : N24Mat3, n24Cj n24A m = m → n24Cj n24B m = m → m = 0 ∨ m = 1 := by
  decide +kernel

end CFSG.OddStandard.HigherRank.YamadaG23
