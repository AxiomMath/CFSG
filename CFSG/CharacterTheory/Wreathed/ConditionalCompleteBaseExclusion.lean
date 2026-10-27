module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseFamily
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseDiag
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseGeneric

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ}
  {κ' : Type*} {J : Finset κ'} {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ} {M : ℕ}
  {γ : ℕ → Fin 4 → ι} {ε : ℕ → Fin 4 → ℤ} {xk yr : ℕ → ι → ℤ} {cd cd' : ℕ → ι → ℤ}
  {β : Type*} {V : Finset β} {dg : β → ι → ℤ}

theorem BaseFamily.diag_at
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) :
    (∀ φ ∈ B, (∀ l, φ ≠ γ r l) → cd r φ = cd' r φ) ∧ cd r A = -σ ∧
      (∀ j ∈ J, cd r (χ j) = 0) ∧
      (∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
        ((OnPair0 (γ r) (ε r) (cd r) s ∧ OnPair1 (γ r) (ε r) (cd' r) s') ∨
          (OnPair1 (γ r) (ε r) (cd r) s ∧ OnPair0 (γ r) (ε r) (cd' r) s'))) ∧
      ((cd r Bq = -τ₀ ∧ cd r Dq = -κ ∧ cd r ω = τ₀ ∧ ∃ η ∈ B, Outside p A Bq Dq ω J χ (γ r) η ∧
          (cd r η = 1 ∨ cd r η = -1) ∧
          ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → φ ≠ η → cd r φ = 0) ∨
        (cd r Bq = 0 ∧ cd r Dq = 0 ∧ cd r ω = 2 * τ₀ ∧
          ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → cd r φ = 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hF.orth_diag r hr r hr
  exact diag_pair hM hJ hS (hF.quad r hr) (hF.diag r hr).1 (hF.diag r hr).2 h1 h2 h3 h4
    (hF.norm_diag r hr).1 (hF.norm_diag r hr).2 (hF.prod_pair r hr) (hF.par r hr)

theorem quad_point_outside
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    {r t : ℕ} (hr : r ∈ Finset.Ico 1 M) (ht : t ∈ Finset.Ico 1 M) (hrt : r ≠ t) (l : Fin 4) :
    Outside p A Bq Dq ω J χ (γ t) (γ r l) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := (hF.quad r hr).core l
  exact ⟨c1, c2, c3, c4, c5, (hF.quad r hr).odd l, fun l' => hF.disj r hr t ht hrt l l'⟩


theorem quadSign_ne_zero (l : Fin 4) : quadSign l ≠ 0 := by
  have h := quadSign_sq l
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem sign_ne_zero {a : ℤ} (ha : a = 1 ∨ a = -1) : a ≠ 0 := by
  rcases ha with rfl | rfl <;> norm_num

theorem BaseFamily.eta_outside
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg) {r : ℕ}
    (hr : r ∈ Finset.Ico 1 M) {η : ι} {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1)
    (hηout : Outside p A Bq Dq ω J χ (γ r) η) (hcη : cd r η = ξ)
    (hzero : ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → φ ≠ η → cd r φ = 0) :
    ∀ t ∈ Finset.Ico 1 M, ∀ l, η ≠ γ t l := by
  intro t ht l hηl
  by_cases hrt : r = t
  · subst hrt
    exact hηout.2.2.2.2.2.2 l hηl
  · have h := (hF.orth_diag r hr t ht).2.1
    rw [Finset.sum_congr rfl fun φ hφ => by rw [(hF.quad t ht).hyr φ hφ],
      sum_mul_lincomb (hF.quad t ht).mem, Finset.sum_eq_single l (fun l' _ hl' => by
        rw [hzero _ ((hF.quad t ht).mem l') (quad_point_outside hF ht hr (Ne.symm hrt) l')
          (fun h => hl' ((hF.quad t ht).inj (h.trans hηl))), mul_zero])
        (fun h => absurd (Finset.mem_univ l) h), ← hηl, hcη] at h
    exact mul_ne_zero (mul_ne_zero (quadSign_ne_zero l) (sign_ne_zero ((hF.quad t ht).sign l)))
      (sign_ne_zero hξ) h

theorem mem_outside0_of_outside {φ : ι} {γ' : Fin 4 → ι} (hφ : φ ∈ B)
    (h : Outside p A Bq Dq ω J χ γ' φ) :
    φ ∈ B.filter (Outside0 p A Bq Dq ω J χ) :=
  Finset.mem_filter.mpr ⟨hφ, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

omit [DecidableEq ι] in
theorem outside_iff {φ : ι} {γ' : Fin 4 → ι} :
    Outside p A Bq Dq ω J χ γ' φ ↔ Outside0 p A Bq Dq ω J χ φ ∧ ∀ l, φ ≠ γ' l := by
  unfold Outside Outside0
  tauto

theorem BaseFamily.eta_common
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) {η : ι} {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (hηB : η ∈ B)
    (hηout : Outside p A Bq Dq ω J χ (γ r) η) (hcη : cd r η = ξ)
    (hzero : ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → φ ≠ η → cd r φ = 0)
    (hA : cd r Bq = -τ₀ ∧ cd r Dq = -κ ∧ cd r ω = τ₀) :
    ∀ t ∈ Finset.Ico 1 M, (cd t Bq = -τ₀ ∧ cd t Dq = -κ ∧ cd t ω = τ₀) ∧ cd t η = ξ ∧
      cd' t η = ξ := by
  have hηall := hF.eta_outside hr hξ hηout hcη hzero
  have hσ2 : σ * σ = 1 := by rcases hS.hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hS.hτ₀ with h | h <;> rw [h] <;> norm_num
  have hκ2 : κ * κ = 1 := by rcases hS.hκ with h | h <;> rw [h] <;> norm_num
  intro t ht
  obtain ⟨hagt, hcAt, hcχt, -, hformt⟩ := hF.diag_at hS hM hJ ht
  have hηt : Outside p A Bq Dq ω J χ (γ t) η :=
    outside_iff.mpr ⟨(outside_iff.mp hηout).1, hηall t ht⟩
  by_cases hrt : r = t
  · subst hrt
    exact ⟨hA, hcη, by rw [← hagt η hηB hηout.2.2.2.2.2.2, hcη]⟩
  obtain ⟨-, hcAr, hcχr, -, -⟩ := hF.diag_at hS hM hJ hr
  have hprod := (hF.prod_diag r hr t ht hrt).1
  rw [hS.inner_split0 hcχr] at hprod
  have hR := sum_supported_quad_add (R := B.filter (Outside0 p A Bq Dq ω J χ))
    (hF.quad r hr).inj
    (fun l => mem_outside0_of_outside ((hF.quad r hr).mem l) (quad_point_outside hF hr ht hrt l))
    (mem_outside0_of_outside hηB hηout) hηout.2.2.2.2.2.2 (g := cd t)
    (fun φ hφ hφγ hφη => hzero φ (Finset.mem_filter.mp hφ).1
      (outside_iff.mpr ⟨(Finset.mem_filter.mp hφ).2, hφγ⟩) hφη)
  rw [hR, (hF.diag r hr).1.one, (hF.diag t ht).1.one, hcAr, hcAt, hA.1, hA.2.1, hA.2.2, hcη]
    at hprod
  rcases hformt with ⟨hBt, hDt, hωt, ηt, hηtB, hηtout, hηts, hzt⟩ | ⟨hBt, hDt, hωt, hzt⟩
  · have hηtall := hF.eta_outside ht hηts hηtout rfl hzt
    have hγr0 : ∀ l, cd t (γ r l) = 0 := fun l => hzt _ ((hF.quad r hr).mem l)
      (quad_point_outside hF hr ht hrt l) fun h => hηtall r hr l h.symm
    rw [Finset.sum_congr rfl fun l _ => by rw [hγr0 l, mul_zero], Finset.sum_const_zero,
      zero_add, hBt, hDt, hωt] at hprod
    have hξη : ξ * cd t η = 1 := by linarith only [hprod, hσ2, hτ2, hκ2]
    have hcdt : cd t η = ξ := by rcases hξ with rfl | rfl <;> linarith
    exact ⟨⟨hBt, hDt, hωt⟩, hcdt, by rw [← hagt η hηB (hηall t ht), hcdt]⟩
  · exfalso
    have hγr0 : ∀ l, cd t (γ r l) = 0 := fun l => hzt _ ((hF.quad r hr).mem l)
      (quad_point_outside hF hr ht hrt l)
    rw [Finset.sum_congr rfl fun l _ => by rw [hγr0 l, mul_zero], Finset.sum_const_zero,
      zero_add, hzt η hηB hηt, hBt, hDt, hωt] at hprod
    linarith only [hprod, hσ2, hτ2]



theorem pair0_product {ε b g : Fin 4 → ℤ} {s : ℤ}
    (hb0 : b 0 = s * ε 0) (hb1 : b 1 = -(s * ε 1)) (hb2 : b 2 = 0) (hb3 : b 3 = 0)
    (hg : ε 0 * g 0 + ε 1 * g 1 = 0) : ∑ l, b l * g l = 2 * s * (ε 0 * g 0) := by
  rw [Fin.sum_univ_four, hb0, hb1, hb2, hb3]
  linear_combination (-s) * hg

theorem pair1_product {ε b g : Fin 4 → ℤ} {s : ℤ}
    (hb0 : b 0 = 0) (hb1 : b 1 = 0) (hb2 : b 2 = s * ε 2) (hb3 : b 3 = -(s * ε 3))
    (hg : ε 2 * g 2 + ε 3 * g 3 = 0) : ∑ l, b l * g l = 2 * s * (ε 2 * g 2) := by
  rw [Fin.sum_univ_four, hb0, hb1, hb2, hb3]
  linear_combination (-s) * hg

theorem generic_eta_arith {k a₀ a₂ e ξ s s' N : ℤ} (hξ : ξ = 1 ∨ ξ = -1)
    (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (hk : (k = 5 ∧ N = 2) ∨ (k = 4 ∧ N = 1))
    (h1 : k + 2 * s * a₀ + ξ * e = 6) (h2 : k + 2 * s' * a₂ + ξ * e = 6)
    (hN : 2 * (a₀ * a₀) + 2 * (a₂ * a₂) + e * e ≤ N) : k = 5 ∧ e = ξ := by
  have q0 := mul_self_nonneg a₀
  have q2 := mul_self_nonneg a₂
  have qe := mul_self_nonneg e
  have hN2 : N ≤ 2 := by omega
  have ha0 : -1 ≤ a₀ ∧ a₀ ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have ha2 : -1 ≤ a₂ ∧ a₂ ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have he : -1 ≤ e ∧ e ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨ha0l, ha0u⟩ := ha0
  obtain ⟨ha2l, ha2u⟩ := ha2
  obtain ⟨hel, heu⟩ := he
  rcases hξ with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;>
    interval_cases a₀ <;> interval_cases a₂ <;> interval_cases e <;> omega

theorem BaseFamily.eta_generic
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) {η : ι} {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (hηB : η ∈ B)
    (hηout : Outside p A Bq Dq ω J χ (γ r) η) (hcη : cd r η = ξ)
    (hzero : ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → φ ≠ η → cd r φ = 0)
    (hA : cd r Bq = -τ₀ ∧ cd r Dq = -κ ∧ cd r ω = τ₀) :
    ∀ I ∈ V, dg I η = ξ := by
  intro I hI
  have hηall := hF.eta_outside hr hξ hηout hcη hzero
  have hσ2 : σ * σ = 1 := by rcases hS.hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hS.hτ₀ with h | h <;> rw [h] <;> norm_num
  have hκ2 : κ * κ = 1 := by rcases hS.hκ with h | h <;> rw [h] <;> norm_num
  obtain ⟨hagr, hcAr, -, ⟨s, s', hs, hs', hpairs⟩, -⟩ := hF.diag_at hS hM hJ hr
  have hc'η : cd' r η = ξ := by rw [← hagr η hηB hηout.2.2.2.2.2.2, hcη]
  have hzero' : ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → φ ≠ η → cd' r φ = 0 :=
    fun φ hφ hout hne => by rw [← hagr φ hφ hout.2.2.2.2.2.2]; exact hzero φ hφ hout hne
  obtain ⟨hdA, hdχ, hform⟩ := generic_column hM hJ hS (hF.gen I hI) (hF.norm_gen I hI)
  have hfixd : (dg I Bq = -τ₀ ∧ dg I Dq = -κ) ∨ (dg I Bq = 0 ∧ dg I Dq = 0) := by
    rcases hform with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hQ := hF.quad r hr
  obtain ⟨hp0, hp1⟩ := base_column_pair_sums hS.hσ hS.hτ₀ hS.hκ hS.hp hS.hA hS.hBq hS.hDq
    hQ.mem hQ.hxk hQ.hyr (hF.gen I hI).one hdA hfixd (hF.orth_gen I hI r hr).1
    (hF.orth_gen I hI r hr).2
  obtain ⟨hd1, hd3, hdΓ⟩ := quad_norm_of_pair_sums (b := fun l => dg I (γ r l)) hQ.sign hp0 hp1
  set R := B.filter (Outside0 p A Bq Dq ω J χ) with hR
  have hγR : ∀ l, γ r l ∈ R := fun l => Finset.mem_filter.mpr ⟨hQ.mem l, (hQ.core l).1,
    (hQ.core l).2.1, (hQ.core l).2.2.1, (hQ.core l).2.2.2.1, (hQ.core l).2.2.2.2, hQ.odd l⟩
  have hηR : η ∈ R := mem_outside0_of_outside hηB hηout
  have hηγ : ∀ l, η ≠ γ r l := hηout.2.2.2.2.2.2
  have hbR : ∀ b : ι → ℤ, (∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → φ ≠ η → b φ = 0) →
      ∀ φ ∈ R, (∀ l, φ ≠ γ r l) → φ ≠ η → b φ = 0 := fun b hb φ hφ hφγ hφη =>
    hb φ (Finset.mem_filter.mp hφ).1 (outside_iff.mpr ⟨(Finset.mem_filter.mp hφ).2, hφγ⟩) hφη
  have hprod1 := (hF.prod_gen I hI r hr).1
  have hprod2 := (hF.prod_gen I hI r hr).2
  rw [hS.inner_split0 hdχ, Finset.sum_congr rfl fun φ _ => mul_comm (dg I φ) (cd r φ),
    sum_supported_quad_add hQ.inj hγR hηR hηγ (hbR (cd r) hzero), hcη] at hprod1
  rw [hS.inner_split0 hdχ, Finset.sum_congr rfl fun φ _ => mul_comm (dg I φ) (cd' r φ),
    sum_supported_quad_add hQ.inj hγR hηR hηγ (hbR (cd' r) hzero'), hc'η] at hprod2
  have hc'core : cd' r p = 1 ∧ cd' r A = -σ ∧ cd' r Bq = -τ₀ ∧ cd' r Dq = -κ ∧
      cd' r ω = τ₀ := by
    refine ⟨(hF.diag r hr).2.one, ?_, ?_, ?_, ?_⟩
    · rw [← hagr A hS.hA fun l h => (hQ.core l).2.1 h.symm, hcAr]
    · rw [← hagr Bq hS.hBq fun l h => (hQ.core l).2.2.1 h.symm, hA.1]
    · rw [← hagr Dq hS.hDq fun l h => (hQ.core l).2.2.2.1 h.symm, hA.2.1]
    · rw [← hagr ω hS.hω fun l h => (hQ.core l).2.2.2.2 h.symm, hA.2.2]
  rw [(hF.gen I hI).one, hdA, (hF.diag r hr).1.one, hcAr, hA.1, hA.2.1, hA.2.2] at hprod1
  rw [(hF.gen I hI).one, hdA, hc'core.1, hc'core.2.1, hc'core.2.2.1, hc'core.2.2.2.1,
    hc'core.2.2.2.2] at hprod2
  have hε2 : ∀ l, ε r l * ε r l = 1 := fun l => by
    rcases hQ.sign l with h | h <;> rw [h] <;> norm_num
  have hbud : 2 * ((ε r 0 * dg I (γ r 0)) * (ε r 0 * dg I (γ r 0))) +
      2 * ((ε r 2 * dg I (γ r 2)) * (ε r 2 * dg I (γ r 2))) + dg I η * dg I η ≤
      ∑ φ ∈ R, dg I φ * dg I φ := by
    have hsub : insert η (Finset.univ.image (γ r)) ⊆ R := by
      intro φ hφ
      rcases Finset.mem_insert.mp hφ with rfl | hφ
      · exact hηR
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
        exact hγR l
    have hηn : η ∉ Finset.univ.image (γ r) := by
      rw [Finset.mem_image]
      rintro ⟨l, -, hl⟩
      exact hηγ l hl.symm
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun φ => dg I φ * dg I φ) fun φ _ _ => mul_self_nonneg _
    rw [Finset.sum_insert hηn, Finset.sum_image fun i _ j _ h => hQ.inj h] at hle
    have hΓ : ∑ l, dg I (γ r l) * dg I (γ r l) =
        2 * (dg I (γ r 0) * dg I (γ r 0) + dg I (γ r 2) * dg I (γ r 2)) := hdΓ
    rw [hΓ] at hle
    linear_combination hle + (2 * (dg I (γ r 0) * dg I (γ r 0))) * hε2 0 +
      (2 * (dg I (γ r 2) * dg I (γ r 2))) * hε2 2
  have hk : ∀ k N : ℤ, (k = 1 * 1 + -σ * -σ + dg I Bq * -τ₀ + dg I Dq * -κ + dg I ω * τ₀) →
      N = ∑ φ ∈ R, dg I φ * dg I φ → (k = 5 ∧ N = 2) ∨ (k = 4 ∧ N = 1) := by
    intro k N hkd hNd
    rcases hform with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · left
      rw [h1, h2, h3] at hkd
      exact ⟨by linear_combination hkd + hσ2 + 2 * hτ2 + hκ2, by rw [hNd, h4]⟩
    · right
      rw [h1, h2, h3] at hkd
      exact ⟨by linear_combination hkd + hσ2 + 2 * hτ2, by rw [hNd, h4]⟩
  rcases hpairs with ⟨⟨c0, c1, c2, c3⟩, ⟨c0', c1', c2', c3'⟩⟩ |
      ⟨⟨c0, c1, c2, c3⟩, ⟨c0', c1', c2', c3'⟩⟩
  · have hΓ1 := pair0_product (b := fun l => cd r (γ r l)) (g := fun l => dg I (γ r l))
      c0 c1 c2 c3 hp0
    have hΓ2 := pair1_product (b := fun l => cd' r (γ r l)) (g := fun l => dg I (γ r l))
      c0' c1' c2' c3' hp1
    rw [hΓ1] at hprod1
    rw [hΓ2] at hprod2
    exact (generic_eta_arith hξ hs hs' (hk _ _ rfl rfl) (by linarith only [hprod1])
      (by linarith only [hprod2]) hbud).2
  · have hΓ1 := pair1_product (b := fun l => cd r (γ r l)) (g := fun l => dg I (γ r l))
      c0 c1 c2 c3 hp1
    have hΓ2 := pair0_product (b := fun l => cd' r (γ r l)) (g := fun l => dg I (γ r l))
      c0' c1' c2' c3' hp0
    rw [hΓ1] at hprod1
    rw [hΓ2] at hprod2
    exact (generic_eta_arith hξ hs' hs (hk _ _ rfl rfl) (by linarith only [hprod2])
      (by linarith only [hprod1]) hbud).2


theorem BaseFamily.no_case_A
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hnv : ∀ φ ∈ B, ∀ ξ : ℤ, Outside0 p A Bq Dq ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, cd t φ = ξ ∧ cd' t φ = ξ) → (∀ I ∈ V, dg I φ = ξ) → False)
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) :
    cd r Bq = 0 ∧ cd r Dq = 0 ∧ cd r ω = 2 * τ₀ ∧
      ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → cd r φ = 0 := by
  obtain ⟨-, -, -, -, hform⟩ := hF.diag_at hS hM hJ hr
  rcases hform with ⟨h1, h2, h3, η, hηB, hηout, hξ, hzero⟩ | hB
  · exfalso
    have hall := hF.eta_common hS hM hJ hr hξ hηB hηout rfl hzero ⟨h1, h2, h3⟩
    exact hnv η hηB (cd r η) (outside_iff.mp hηout).1 (hF.eta_outside hr hξ hηout rfl hzero)
      (fun t ht => (hall t ht).2) (hF.eta_generic hS hM hJ hr hξ hηB hηout rfl hzero
        ⟨h1, h2, h3⟩)
  · exact hB

end CFSG.Wreathed.ConditionalCompleteBase
