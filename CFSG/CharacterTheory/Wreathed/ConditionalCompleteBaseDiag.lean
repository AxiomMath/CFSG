module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseSetting
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseColumns

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed
  CFSG.Wreathed.ConditionalUniformOddFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem one_le_sq_add_sq_of_sub_sign {a b : ℤ} (h : a - b = 1 ∨ a - b = -1) :
    1 ≤ a * a + b * b := by
  rcases h with h | h <;> nlinarith [mul_self_nonneg (a + b)]

theorem diag_difference {A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {γ : Fin 4 → ι}
    (hγinj : Function.Injective γ)
    (hγB : ∀ l, γ l ∈ B) {ε : Fin 4 → ℤ} (hε : ∀ l, ε l = 1 ∨ ε l = -1) {xk C : ι → ℤ}
    (hxk : ∀ φ ∈ B, xk φ = fixedPart p A Bq Dq σ τ₀ κ φ + ∑ l, ε l * unitVector (γ l) φ)
    (hC : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
      κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ)
    {c c' : ι → ℤ} (hcc : ∑ φ ∈ B, c φ * c φ = 8) (hc'c' : ∑ φ ∈ B, c' φ * c' φ = 8)
    (hcc' : ∑ φ ∈ B, c φ * c' φ = 6) (hpar : ∀ φ ∈ B, c φ + c' φ ≡ xk φ + C φ [ZMOD 2]) :
    (∀ l, c (γ l) - c' (γ l) = 1 ∨ c (γ l) - c' (γ l) = -1) ∧
      ∀ φ ∈ B, (∀ l, φ ≠ γ l) → c φ = c' φ := by
  set O := Finset.univ.image γ with hO
  have hOB : O ⊆ B := fun φ hφ => by
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
    exact hγB l
  have hcardO : O.card = 4 := by
    rw [hO, Finset.card_image_of_injective _ hγinj, Finset.card_univ, Fintype.card_fin]
  have hsq : ∑ φ ∈ B, (c φ - c' φ) * (c φ - c' φ) = 4 := by
    have h : ∀ φ, (c φ - c' φ) * (c φ - c' φ) = c φ * c φ + c' φ * c' φ - 2 * (c φ * c' φ) :=
      fun φ => by ring
    rw [Finset.sum_congr rfl fun φ _ => h φ, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hcc, hc'c', hcc']
    norm_num
  have hfix : ∀ φ, fixedPart p A Bq Dq σ τ₀ κ φ + (unitVector p φ - σ * unitVector A φ -
      τ₀ * unitVector Bq φ - κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ) =
      2 * (-σ * unitVector A φ - τ₀ * unitVector Bq φ + τ₀ * unitVector ω φ) := fun φ => by
    rw [fixedPart]
    ring
  have hlin : ∀ φ, (∀ l, φ ≠ γ l) → ∑ l, ε l * unitVector (γ l) φ = 0 := fun φ hφ =>
    Finset.sum_eq_zero fun l _ => by rw [unitVector_of_ne (hφ l), mul_zero]
  have hlinγ : ∀ l, ∑ l', ε l' * unitVector (γ l') (γ l) = ε l := fun l => by
    rw [Finset.sum_eq_single l (fun l' _ hl' => by
        rw [unitVector_of_ne fun h => hl' (hγinj h).symm, mul_zero])
      fun h => absurd (Finset.mem_univ l) h, unitVector_self, mul_one]
  have hodd : ∀ φ ∈ O, Odd (c φ - c' φ) := by
    intro φ hφ
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
    have h := hpar _ (hγB l)
    rw [hxk _ (hγB l), hC _ (hγB l), hlinγ l] at h
    have h2 : c (γ l) - c' (γ l) ≡ ε l + 2 * (-σ * unitVector A (γ l) -
        τ₀ * unitVector Bq (γ l) + τ₀ * unitVector ω (γ l)) - 2 * c' (γ l) [ZMOD 2] := by
      have h3 := hfix (γ l)
      unfold Int.ModEq at h ⊢
      omega
    rw [Int.odd_iff]
    unfold Int.ModEq at h2
    rcases hε l with he | he <;> rw [he] at h2 <;> omega
  have heven : ∀ φ ∈ B, φ ∉ O → c φ - c' φ = 0 :=
    fun φ hφ hφO => eq_zero_of_sq_sum_le_card_odd (g := fun φ => c φ - c' φ) hOB hφ hφO hodd
      (by rw [hsq, hcardO]; norm_num)
  have hsign := sign_of_sq_sum_le_card_odd (g := fun φ => c φ - c' φ) hOB hodd
    (by rw [hsq, hcardO]; norm_num)
  refine ⟨fun l => hsign _ (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩), fun φ hφ hφγ => ?_⟩
  have hφO : φ ∉ O := by
    rw [hO, Finset.mem_image]
    rintro ⟨l, -, hl⟩
    exact hφγ l hl.symm
  linarith [heven φ hφ hφO]


@[expose] def OnPair0 (γ : Fin 4 → ι) (ε : Fin 4 → ℤ) (b : ι → ℤ) (s : ℤ) : Prop :=
  b (γ 0) = s * ε 0 ∧ b (γ 1) = -(s * ε 1) ∧ b (γ 2) = 0 ∧ b (γ 3) = 0

@[expose] def OnPair1 (γ : Fin 4 → ι) (ε : Fin 4 → ℤ) (b : ι → ℤ) (s : ℤ) : Prop :=
  b (γ 0) = 0 ∧ b (γ 1) = 0 ∧ b (γ 2) = s * ε 2 ∧ b (γ 3) = -(s * ε 3)

theorem exists_unique_unit_of_sum_sq_eq_one {R : Finset ι} {b : ι → ℤ}
    (h : ∑ φ ∈ R, b φ * b φ = 1) :
    ∃ η ∈ R, (b η = 1 ∨ b η = -1) ∧ ∀ φ ∈ R, φ ≠ η → b φ = 0 := by
  obtain ⟨η, hηR, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [h]; norm_num :
    ∑ φ ∈ R, b φ * b φ ≠ 0)
  have hsplit := Finset.add_sum_erase R (fun φ => b φ * b φ) hηR
  have hrest : 0 ≤ ∑ φ ∈ R.erase η, b φ * b φ := Finset.sum_nonneg fun φ _ => mul_self_nonneg _
  have hη1 : 1 ≤ b η * b η := by
    have hb : b η ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rcases lt_or_gt_of_ne hb with h' | h' <;> nlinarith
  have hηeq : b η * b η = 1 := by linarith
  have hzero : ∑ φ ∈ R.erase η, b φ * b φ = 0 := by linarith
  refine ⟨η, hηR, ?_, fun φ hφ hφη => ?_⟩
  · have h1 : b η ≤ 1 := by nlinarith
    have h2 : -1 ≤ b η := by nlinarith
    have hb : b η ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    omega
  · exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun φ _ =>
      mul_self_nonneg (b φ)).mp hzero φ (Finset.mem_erase.mpr ⟨hφη, hφ⟩))


theorem unit_pair_of_sum_sq_eq_one {a b : ℤ} (h : a * a + b * b = 1) :
    (a = 0 ∧ (b = 1 ∨ b = -1)) ∨ ((a = 1 ∨ a = -1) ∧ b = 0) := by
  have ha := mul_self_nonneg a
  have hb := mul_self_nonneg b
  have ha2 : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hb2 : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  rcases (by omega : a = -1 ∨ a = 0 ∨ a = 1) with rfl | rfl | rfl <;>
    rcases (by omega : b = -1 ∨ b = 0 ∨ b = 1) with rfl | rfl | rfl <;> omega

theorem quad_norm_of_pair_sums {ε b : Fin 4 → ℤ} (hε : ∀ l, ε l = 1 ∨ ε l = -1)
    (h0 : ε 0 * b 0 + ε 1 * b 1 = 0) (h1 : ε 2 * b 2 + ε 3 * b 3 = 0) :
    b 1 = -(ε 1 * ε 0 * b 0) ∧ b 3 = -(ε 3 * ε 2 * b 2) ∧
      ∑ l, b l * b l = 2 * (b 0 * b 0 + b 2 * b 2) := by
  have hε2 : ∀ l, ε l * ε l = 1 := fun l => by rcases hε l with h | h <;> rw [h] <;> norm_num
  have hb1 : b 1 = -(ε 1 * ε 0 * b 0) := by linear_combination ε 1 * h0 - b 1 * hε2 1
  have hb3 : b 3 = -(ε 3 * ε 2 * b 2) := by linear_combination ε 3 * h1 - b 3 * hε2 3
  refine ⟨hb1, hb3, ?_⟩
  rw [Fin.sum_univ_four, hb1, hb3]
  linear_combination (b 0 * b 0 * (ε 1 * ε 1)) * hε2 0 + (b 0 * b 0) * hε2 1 +
    (b 2 * b 2 * (ε 3 * ε 3)) * hε2 2 + (b 2 * b 2) * hε2 3

theorem diag_norm_arith {F S R : ℤ} (h : 8 = F + 2 * S + R) (hF : F = 5 ∨ F = 6)
    (hS : 4 ≤ 2 * (2 * S)) (hR : 0 ≤ R) : S = 1 ∧ (F = 5 → R = 1) ∧ (F = 6 → R = 0) := by
  omega

variable {A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {κ' : Type*} {J : Finset κ'} {χ : κ' → ι}
  {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ}

theorem diag_pair {M : ℕ} (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) {γ : Fin 4 → ι} {ε : Fin 4 → ℤ}
    {xk yr : ι → ℤ} (hQ : Quadruple B p A Bq Dq ω σ τ₀ κ J χ γ ε xk yr) {c c' : ι → ℤ}
    (hc : IsBaseColumn B p y₀ C J xj c) (hc' : IsBaseColumn B p y₀ C J xj c')
    (hcx : ∑ φ ∈ B, c φ * xk φ = 0) (hcy : ∑ φ ∈ B, c φ * yr φ = 0)
    (hc'x : ∑ φ ∈ B, c' φ * xk φ = 0) (hc'y : ∑ φ ∈ B, c' φ * yr φ = 0)
    (hcc : ∑ φ ∈ B, c φ * c φ = 8) (hc'c' : ∑ φ ∈ B, c' φ * c' φ = 8)
    (hcc' : ∑ φ ∈ B, c φ * c' φ = 6) (hpar : ∀ φ ∈ B, c φ + c' φ ≡ xk φ + C φ [ZMOD 2]) :
    (∀ φ ∈ B, (∀ l, φ ≠ γ l) → c φ = c' φ) ∧ c A = -σ ∧ (∀ j ∈ J, c (χ j) = 0) ∧
      (∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
        ((OnPair0 γ ε c s ∧ OnPair1 γ ε c' s') ∨ (OnPair1 γ ε c s ∧ OnPair0 γ ε c' s'))) ∧
      ((c Bq = -τ₀ ∧ c Dq = -κ ∧ c ω = τ₀ ∧ ∃ η ∈ B, Outside p A Bq Dq ω J χ γ η ∧
          (c η = 1 ∨ c η = -1) ∧ ∀ φ ∈ B, Outside p A Bq Dq ω J χ γ φ → φ ≠ η → c φ = 0) ∨
        (c Bq = 0 ∧ c Dq = 0 ∧ c ω = 2 * τ₀ ∧
          ∀ φ ∈ B, Outside p A Bq Dq ω J χ γ φ → c φ = 0)) := by
  obtain ⟨hdiff, hagree⟩ := diag_difference hQ.inj hQ.mem hQ.sign hQ.hxk hS.hC hcc hc'c' hcc'
    hpar
  set R := B.filter (Outside p A Bq Dq ω J χ γ) with hR
  have hnc := hS.sum_split hQ (fun φ => c φ * c φ)
  have hnc' := hS.sum_split hQ (fun φ => c' φ * c' φ)
  rw [hcc, ← hR] at hnc
  rw [hc'c', ← hR] at hnc'
  have hnot : ∀ φ, (∀ l, γ l ≠ φ) → ∀ l, φ ≠ γ l := fun φ h l e => h l e.symm
  have hagp : c p = c' p := hagree p hS.hp (hnot p fun l => (hQ.core l).1)
  have hagA : c A = c' A := hagree A hS.hA (hnot A fun l => (hQ.core l).2.1)
  have hagB : c Bq = c' Bq := hagree Bq hS.hBq (hnot Bq fun l => (hQ.core l).2.2.1)
  have hagD : c Dq = c' Dq := hagree Dq hS.hDq (hnot Dq fun l => (hQ.core l).2.2.2.1)
  have hagω : c ω = c' ω := hagree ω hS.hω (hnot ω fun l => (hQ.core l).2.2.2.2)
  have hagχ : ∀ j ∈ J, c (χ j) = c' (χ j) := fun j hj =>
    hagree (χ j) (hS.hχB j hj) (hnot (χ j) fun l => hQ.odd l j hj)
  have hagR : ∀ φ ∈ R, c φ = c' φ := fun φ hφ =>
    hagree φ (Finset.mem_filter.mp hφ).1 (Finset.mem_filter.mp hφ).2.2.2.2.2.2.2
  have hRsum : ∑ φ ∈ R, c φ * c φ = ∑ φ ∈ R, c' φ * c' φ :=
    Finset.sum_congr rfl fun φ hφ => by rw [hagR φ hφ]
  have hJsum : ∑ j ∈ J, c (χ j) * c (χ j) = ∑ j ∈ J, c' (χ j) * c' (χ j) :=
    Finset.sum_congr rfl fun j hj => by rw [hagχ j hj]
  have hΓeq : ∑ l, c (γ l) * c (γ l) = ∑ l, c' (γ l) * c' (γ l) := by
    rw [hagp, hagA, hagB, hagD, hagω, hJsum, hRsum] at hnc
    linarith
  have hΓ4 : 4 ≤ ∑ l, (c (γ l) * c (γ l) + c' (γ l) * c' (γ l)) := by
    calc (4 : ℤ) = ∑ _l : Fin 4, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun l _ => one_le_sq_add_sq_of_sub_sign (hdiff l)
  rw [Finset.sum_add_distrib, ← hΓeq] at hΓ4
  have hRnn : 0 ≤ ∑ φ ∈ R, c φ * c φ := Finset.sum_nonneg fun φ _ => mul_self_nonneg _
  have hN : c p * c p + c A * c A + c Bq * c Bq + c Dq * c Dq + c ω * c ω +
      ∑ j ∈ J, c (χ j) * c (χ j) ≤ 7 := by linarith
  obtain ⟨hcA, hcχ, hform⟩ := hc.coords hM hJ hS.hσ hS.hτ₀ hS.hκ hS.hp hS.hA hS.hBq hS.hDq
    hS.hω hS.hχB hS.hy₀ hS.hxj hS.hC hN
  have hc'A : c' A = -σ := by rw [← hagA]; exact hcA
  have hfix : (c Bq = -τ₀ ∧ c Dq = -κ) ∨ (c Bq = 0 ∧ c Dq = 0) := by
    rcases hform with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hfix' : (c' Bq = -τ₀ ∧ c' Dq = -κ) ∨ (c' Bq = 0 ∧ c' Dq = 0) := by
    rw [← hagB, ← hagD]
    exact hfix
  obtain ⟨hp0, hp1⟩ := base_column_pair_sums hS.hσ hS.hτ₀ hS.hκ hS.hp hS.hA hS.hBq hS.hDq
    hQ.mem hQ.hxk hQ.hyr hc.one hcA hfix hcx hcy
  obtain ⟨hp0', hp1'⟩ := base_column_pair_sums hS.hσ hS.hτ₀ hS.hκ hS.hp hS.hA hS.hBq hS.hDq
    hQ.mem hQ.hxk hQ.hyr hc'.one hc'A hfix' hc'x hc'y
  obtain ⟨hc1, hc3, hΓc⟩ := quad_norm_of_pair_sums (b := fun l => c (γ l)) hQ.sign hp0 hp1
  obtain ⟨hc1', hc3', hΓc'⟩ := quad_norm_of_pair_sums (b := fun l => c' (γ l)) hQ.sign hp0' hp1'
  have hε2 : ∀ l, ε l * ε l = 1 := fun l => by rcases hQ.sign l with h | h <;> rw [h] <;> norm_num
  have hJ0 : ∑ j ∈ J, c (χ j) * c (χ j) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hcχ j hj, mul_zero]
  have hσ2 : σ * σ = 1 := by rcases hS.hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hS.hτ₀ with h | h <;> rw [h] <;> norm_num
  have hκ2 : κ * κ = 1 := by rcases hS.hκ with h | h <;> rw [h] <;> norm_num
  set Fn := c p * c p + c A * c A + c Bq * c Bq + c Dq * c Dq + c ω * c ω with hFn
  have hFn5 : (c Bq = -τ₀ ∧ c Dq = -κ ∧ c ω = τ₀) → Fn = 5 := by
    rintro ⟨h1, h2, h3⟩
    rw [hFn, hc.one, hcA, h1, h2, h3]
    linear_combination hσ2 + 2 * hτ2 + hκ2
  have hFn6 : (c Bq = 0 ∧ c Dq = 0 ∧ c ω = 2 * τ₀) → Fn = 6 := by
    rintro ⟨h1, h2, h3⟩
    rw [hFn, hc.one, hcA, h1, h2, h3]
    linear_combination hσ2 + 4 * hτ2
  have hFcase : Fn = 5 ∨ Fn = 6 := by
    rcases hform with h | h
    · exact Or.inl (hFn5 h)
    · exact Or.inr (hFn6 h)
  have hnc2 : 8 = Fn + 2 * (c (γ 0) * c (γ 0) + c (γ 2) * c (γ 2)) +
      ∑ φ ∈ R, c φ * c φ := by
    rw [hJ0, hΓc] at hnc
    linarith only [hnc]
  have hΓ4' : 4 ≤ 2 * (2 * (c (γ 0) * c (γ 0) + c (γ 2) * c (γ 2))) := by
    rw [hΓc] at hΓ4
    linarith only [hΓ4]
  obtain ⟨hsumc, hR5, hR6⟩ := diag_norm_arith hnc2 hFcase hΓ4' hRnn
  have hsum' : c' (γ 0) * c' (γ 0) + c' (γ 2) * c' (γ 2) = 1 := by
    have h := hΓeq
    rw [hΓc, hΓc'] at h
    linarith only [h, hsumc]
  have hpairs : ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      ((OnPair0 γ ε c s ∧ OnPair1 γ ε c' s') ∨ (OnPair1 γ ε c s ∧ OnPair0 γ ε c' s')) := by
    have hd0 := hdiff 0
    have hd2 := hdiff 2
    rcases unit_pair_of_sum_sq_eq_one hsumc with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;>
      rcases unit_pair_of_sum_sq_eq_one hsum' with ⟨h0', h2'⟩ | ⟨h0', h2'⟩
    · exfalso
      rw [h0, h0'] at hd0
      norm_num at hd0
    ·
      refine ⟨ε 2 * c (γ 2), ε 0 * c' (γ 0), sign_mul (hQ.sign 2) h2,
        sign_mul (hQ.sign 0) h0', Or.inr ⟨?_, ?_⟩⟩
      · refine ⟨h0, by rw [hc1, h0]; ring, ?_, ?_⟩
        · linear_combination -(c (γ 2)) * hε2 2
        · rw [hc3]
          ring
      · refine ⟨?_, ?_, h2', ?_⟩
        · linear_combination -(c' (γ 0)) * hε2 0
        · rw [hc1']
          ring
        · rw [hc3', h2']
          ring
    ·
      refine ⟨ε 0 * c (γ 0), ε 2 * c' (γ 2), sign_mul (hQ.sign 0) h0,
        sign_mul (hQ.sign 2) h2', Or.inl ⟨?_, ?_⟩⟩
      · refine ⟨?_, ?_, h2, ?_⟩
        · linear_combination -(c (γ 0)) * hε2 0
        · rw [hc1]
          ring
        · rw [hc3, h2]
          ring
      · refine ⟨h0', by rw [hc1', h0']; ring, ?_, ?_⟩
        · linear_combination -(c' (γ 2)) * hε2 2
        · rw [hc3']
          ring
    · exfalso
      rw [h2, h2'] at hd2
      norm_num at hd2
  refine ⟨hagree, hcA, hcχ, hpairs, ?_⟩
  rcases hform with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hR1 := hR5 (hFn5 ⟨h1, h2, h3⟩)
    obtain ⟨η, hηR, hη, hzero⟩ := exists_unique_unit_of_sum_sq_eq_one hR1
    refine Or.inl ⟨h1, h2, h3, η, (Finset.mem_filter.mp hηR).1, (Finset.mem_filter.mp hηR).2,
      hη, fun φ hφB hφ hφη => hzero φ (Finset.mem_filter.mpr ⟨hφB, hφ⟩) hφη⟩
  · have hR0 := hR6 (hFn6 ⟨h1, h2, h3⟩)
    refine Or.inr ⟨h1, h2, h3, fun φ hφB hφ => ?_⟩
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun φ _ =>
      mul_self_nonneg (c φ)).mp hR0 φ (Finset.mem_filter.mpr ⟨hφB, hφ⟩))

end CFSG.Wreathed.ConditionalCompleteBase
