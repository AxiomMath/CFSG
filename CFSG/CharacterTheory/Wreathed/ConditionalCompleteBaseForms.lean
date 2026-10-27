module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseExclusion

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ}
  {κ' : Type*} {J : Finset κ'} {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ} {M : ℕ}
  {γ : ℕ → Fin 4 → ι} {ε : ℕ → Fin 4 → ℤ} {xk yr : ℕ → ι → ℤ} {cd cd' : ℕ → ι → ℤ}
  {β : Type*} {V : Finset β} {dg : β → ι → ℤ}

theorem generic_form_arith {a₀ a₂ s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1)
    (h1 : 4 + 2 * s * a₀ = 6) (h2 : 4 + 2 * s' * a₂ = 6)
    (hN : 2 * (a₀ * a₀) + 2 * (a₂ * a₂) ≤ 2) : False := by
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> nlinarith

theorem BaseFamily.diag_form
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hnv : ∀ φ ∈ B, ∀ ξ : ℤ, Outside0 p A Bq Dq ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, cd t φ = ξ ∧ cd' t φ = ξ) → (∀ I ∈ V, dg I φ = ξ) → False)
    {r : ℕ} (hr : r ∈ Finset.Ico 1 M) :
    (cd r p = 1 ∧ cd r A = -σ ∧ cd r Bq = 0 ∧ cd r Dq = 0 ∧ cd r ω = 2 * τ₀ ∧
      (∀ j ∈ J, cd r (χ j) = 0) ∧ ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → cd r φ = 0) ∧
    (cd' r p = 1 ∧ cd' r A = -σ ∧ cd' r Bq = 0 ∧ cd' r Dq = 0 ∧ cd' r ω = 2 * τ₀ ∧
      (∀ j ∈ J, cd' r (χ j) = 0) ∧ ∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ r) φ → cd' r φ = 0) ∧
    ∃ s s' : ℤ, (s = 1 ∨ s = -1) ∧ (s' = 1 ∨ s' = -1) ∧
      ((OnPair0 (γ r) (ε r) (cd r) s ∧ OnPair1 (γ r) (ε r) (cd' r) s') ∨
        (OnPair1 (γ r) (ε r) (cd r) s ∧ OnPair0 (γ r) (ε r) (cd' r) s')) := by
  obtain ⟨hag, hcA, hcχ, hpairs, -⟩ := hF.diag_at hS hM hJ hr
  obtain ⟨hB1, hB2, hB3, hB0⟩ := hF.no_case_A hS hM hJ hnv hr
  have hQ := hF.quad r hr
  have hcore : ∀ q ∈ B, (∀ l, γ r l ≠ q) → cd' r q = cd r q := fun q hq h =>
    (hag q hq fun l e => h l e.symm).symm
  refine ⟨⟨(hF.diag r hr).1.one, hcA, hB1, hB2, hB3, hcχ, hB0⟩,
    ⟨(hF.diag r hr).2.one, ?_, ?_, ?_, ?_, fun j hj => ?_, fun φ hφ hout => ?_⟩, hpairs⟩
  · rw [hcore A hS.hA fun l => (hQ.core l).2.1, hcA]
  · rw [hcore Bq hS.hBq fun l => (hQ.core l).2.2.1, hB1]
  · rw [hcore Dq hS.hDq fun l => (hQ.core l).2.2.2.1, hB2]
  · rw [hcore ω hS.hω fun l => (hQ.core l).2.2.2.2, hB3]
  · rw [hcore (χ j) (hS.hχB j hj) fun l => hQ.odd l j hj, hcχ j hj]
  · rw [← hag φ hφ hout.2.2.2.2.2.2, hB0 φ hφ hout]


theorem BaseFamily.generic_form
    (hF : BaseFamily B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj M γ ε xk yr cd cd' V dg)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hnv : ∀ φ ∈ B, ∀ ξ : ℤ, Outside0 p A Bq Dq ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, cd t φ = ξ ∧ cd' t φ = ξ) → (∀ I ∈ V, dg I φ = ξ) → False)
    {I : β} (hI : I ∈ V) :
    dg I p = 1 ∧ dg I A = -σ ∧ dg I Bq = 0 ∧ dg I Dq = 0 ∧ dg I ω = 2 * τ₀ ∧
      (∀ j ∈ J, dg I (χ j) = 0) ∧
      ∃ ψ ∈ B, Outside0 p A Bq Dq ω J χ ψ ∧ (∀ t ∈ Finset.Ico 1 M, ∀ l, ψ ≠ γ t l) ∧
        (dg I ψ = 1 ∨ dg I ψ = -1) ∧
        ∀ φ ∈ B, Outside0 p A Bq Dq ω J χ φ → φ ≠ ψ → dg I φ = 0 := by
  obtain ⟨hdA, hdχ, hform⟩ := generic_column hM hJ hS (hF.gen I hI) (hF.norm_gen I hI)
  set R := B.filter (Outside0 p A Bq Dq ω J χ) with hR
  have hσ2 : σ * σ = 1 := by rcases hS.hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hS.hτ₀ with h | h <;> rw [h] <;> norm_num
  have hκ2 : κ * κ = 1 := by rcases hS.hκ with h | h <;> rw [h] <;> norm_num
  have hfixd : (dg I Bq = -τ₀ ∧ dg I Dq = -κ) ∨ (dg I Bq = 0 ∧ dg I Dq = 0) := by
    rcases hform with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hps : ∀ t ∈ Finset.Ico 1 M, ε t 0 * dg I (γ t 0) + ε t 1 * dg I (γ t 1) = 0 ∧
      ε t 2 * dg I (γ t 2) + ε t 3 * dg I (γ t 3) = 0 := fun t ht =>
    base_column_pair_sums hS.hσ hS.hτ₀ hS.hκ hS.hp hS.hA hS.hBq hS.hDq (hF.quad t ht).mem
      (hF.quad t ht).hxk (hF.quad t ht).hyr (hF.gen I hI).one hdA hfixd
      (hF.orth_gen I hI t ht).1 (hF.orth_gen I hI t ht).2
  have hγR : ∀ t ∈ Finset.Ico 1 M, ∀ l, γ t l ∈ R := fun t ht l =>
    Finset.mem_filter.mpr ⟨(hF.quad t ht).mem l, ((hF.quad t ht).core l).1,
      ((hF.quad t ht).core l).2.1, ((hF.quad t ht).core l).2.2.1,
      ((hF.quad t ht).core l).2.2.2.1, ((hF.quad t ht).core l).2.2.2.2, (hF.quad t ht).odd l⟩
  have hquadle : ∀ t ∈ Finset.Ico 1 M, ∑ l, dg I (γ t l) * dg I (γ t l) ≤
      ∑ φ ∈ R, dg I φ * dg I φ := by
    intro t ht
    have hsub : Finset.univ.image (γ t) ⊆ R := fun φ hφ => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hγR t ht l
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun φ => dg I φ * dg I φ)
      fun φ _ _ => mul_self_nonneg _
    rwa [Finset.sum_image fun i _ j _ h => (hF.quad t ht).inj h] at h
  have h1M : 1 ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩
  rcases hform with ⟨h1, h2, h3, hRn⟩ | ⟨h1, h2, h3, hRn⟩
  ·
    exfalso
    obtain ⟨⟨hc1, hcA, hcB, hcD, hcω, -, hc0⟩, ⟨hc1', hcA', hcB', hcD', hcω', -, hc0'⟩,
      s, s', hs, hs', hpairs⟩ := hF.diag_form hS hM hJ hnv h1M
    have hbR : ∀ b : ι → ℤ, (∀ φ ∈ B, Outside p A Bq Dq ω J χ (γ 1) φ → b φ = 0) →
        ∀ φ ∈ R, (∀ l, φ ≠ γ 1 l) → b φ = 0 := fun b hb φ hφ hφγ =>
      hb φ (Finset.mem_filter.mp hφ).1 (outside_iff.mpr ⟨(Finset.mem_filter.mp hφ).2, hφγ⟩)
    have hprod1 := (hF.prod_gen I hI 1 h1M).1
    have hprod2 := (hF.prod_gen I hI 1 h1M).2
    rw [hS.inner_split0 hdχ, Finset.sum_congr rfl fun φ _ => mul_comm (dg I φ) (cd 1 φ),
      sum_supported_quad (hF.quad 1 h1M).inj (hγR 1 h1M) (hbR (cd 1) hc0), (hF.gen I hI).one,
      hdA, h1, h2, h3, hc1, hcA, hcB, hcD, hcω] at hprod1
    rw [hS.inner_split0 hdχ, Finset.sum_congr rfl fun φ _ => mul_comm (dg I φ) (cd' 1 φ),
      sum_supported_quad (hF.quad 1 h1M).inj (hγR 1 h1M) (hbR (cd' 1) hc0'),
      (hF.gen I hI).one, hdA, h1, h2, h3, hc1', hcA', hcB', hcD', hcω'] at hprod2
    obtain ⟨hp0, hp1⟩ := hps 1 h1M
    obtain ⟨hd1, hd3, hdΓ⟩ := quad_norm_of_pair_sums (b := fun l => dg I (γ 1 l))
      (hF.quad 1 h1M).sign hp0 hp1
    have hε2 : ∀ l, ε 1 l * ε 1 l = 1 := fun l => by
      rcases (hF.quad 1 h1M).sign l with h | h <;> rw [h] <;> norm_num
    have hbud : 2 * ((ε 1 0 * dg I (γ 1 0)) * (ε 1 0 * dg I (γ 1 0))) +
        2 * ((ε 1 2 * dg I (γ 1 2)) * (ε 1 2 * dg I (γ 1 2))) ≤ 2 := by
      have hle := hquadle 1 h1M
      have hΓ : ∑ l, dg I (γ 1 l) * dg I (γ 1 l) =
          2 * (dg I (γ 1 0) * dg I (γ 1 0) + dg I (γ 1 2) * dg I (γ 1 2)) := hdΓ
      rw [hΓ, hRn] at hle
      linear_combination hle + (2 * (dg I (γ 1 0) * dg I (γ 1 0))) * hε2 0 +
        (2 * (dg I (γ 1 2) * dg I (γ 1 2))) * hε2 2
    rcases hpairs with ⟨⟨c0, c1, c2, c3⟩, ⟨c0', c1', c2', c3'⟩⟩ |
        ⟨⟨c0, c1, c2, c3⟩, ⟨c0', c1', c2', c3'⟩⟩
    · rw [pair0_product (b := fun l => cd 1 (γ 1 l)) (g := fun l => dg I (γ 1 l)) c0 c1 c2 c3
        hp0] at hprod1
      rw [pair1_product (b := fun l => cd' 1 (γ 1 l)) (g := fun l => dg I (γ 1 l)) c0' c1' c2'
        c3' hp1] at hprod2
      exact generic_form_arith hs hs' (by linarith only [hprod1, hσ2, hτ2])
        (by linarith only [hprod2, hσ2, hτ2]) hbud
    · rw [pair1_product (b := fun l => cd 1 (γ 1 l)) (g := fun l => dg I (γ 1 l)) c0 c1 c2 c3
        hp1] at hprod1
      rw [pair0_product (b := fun l => cd' 1 (γ 1 l)) (g := fun l => dg I (γ 1 l)) c0' c1' c2'
        c3' hp0] at hprod2
      exact generic_form_arith hs' hs (by linarith only [hprod2, hσ2, hτ2])
        (by linarith only [hprod1, hσ2, hτ2]) hbud
  ·
    obtain ⟨ψ, hψR, hψ, hzero⟩ := exists_unique_unit_of_sum_sq_eq_one hRn
    have hψB := (Finset.mem_filter.mp hψR).1
    refine ⟨(hF.gen I hI).one, hdA, h1, h2, h3, hdχ, ψ, hψB, (Finset.mem_filter.mp hψR).2,
      fun t ht l hψl => ?_, hψ, fun φ hφ hout hne => hzero φ (Finset.mem_filter.mpr ⟨hφ, hout⟩)
        hne⟩
    obtain ⟨hp0, hp1⟩ := hps t ht
    have hzt : ∀ l', l' ≠ l → dg I (γ t l') = 0 := fun l' hl' =>
      hzero _ (hγR t ht l') fun h => hl' ((hF.quad t ht).inj (h.trans hψl))
    have hψv : dg I (γ t l) ≠ 0 := by
      rw [← hψl]
      rcases hψ with h | h <;> rw [h] <;> norm_num
    have hε0 : ∀ l', ε t l' ≠ 0 := fun l' => sign_ne_zero ((hF.quad t ht).sign l')
    fin_cases l
    · exact hψv (by
        have := hzt 1 (by decide)
        simp only [this, mul_zero, add_zero] at hp0
        exact (mul_eq_zero.mp hp0).resolve_left (hε0 0))
    · exact hψv (by
        have := hzt 0 (by decide)
        simp only [this, mul_zero, zero_add] at hp0
        exact (mul_eq_zero.mp hp0).resolve_left (hε0 1))
    · exact hψv (by
        have := hzt 3 (by decide)
        simp only [this, mul_zero, add_zero] at hp1
        exact (mul_eq_zero.mp hp1).resolve_left (hε0 2))
    · exact hψv (by
        have := hzt 2 (by decide)
        simp only [this, mul_zero, zero_add] at hp1
        exact (mul_eq_zero.mp hp1).resolve_left (hε0 3))

end CFSG.Wreathed.ConditionalCompleteBase
