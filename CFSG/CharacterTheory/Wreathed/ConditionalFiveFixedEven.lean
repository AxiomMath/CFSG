module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCore
public import CFSG.CharacterTheory.Wreathed.ConditionalUniformOddFourierTwo

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier
  CFSG.Wreathed.ConditionalUniformOddFourier

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

theorem sum_mul_five_unitVector {q₁ q₂ q₃ q₄ q₅ : ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B)
    (h₃ : q₃ ∈ B) (h₄ : q₄ ∈ B) (h₅ : q₅ ∈ B) (f : ι → ℤ) (a₁ a₂ a₃ a₄ a₅ : ℤ) :
    ∑ φ ∈ B, f φ * (a₁ * unitVector q₁ φ + a₂ * unitVector q₂ φ + a₃ * unitVector q₃ φ +
      a₄ * unitVector q₄ φ + a₅ * unitVector q₅ φ) =
      a₁ * f q₁ + a₂ * f q₂ + a₃ * f q₃ + a₄ * f q₄ + a₅ * f q₅ := by
  have h : ∀ φ, f φ * (a₁ * unitVector q₁ φ + a₂ * unitVector q₂ φ + a₃ * unitVector q₃ φ +
      a₄ * unitVector q₄ φ + a₅ * unitVector q₅ φ) = a₁ * (f φ * unitVector q₁ φ) +
      a₂ * (f φ * unitVector q₂ φ) + a₃ * (f φ * unitVector q₃ φ) +
      a₄ * (f φ * unitVector q₄ φ) + a₅ * (f φ * unitVector q₅ φ) := fun φ => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_mul_unitVector h₁,
    sum_mul_unitVector h₂, sum_mul_unitVector h₃, sum_mul_unitVector h₄, sum_mul_unitVector h₅]

theorem sum_five_add_rest {q₁ q₂ q₃ q₄ q₅ : ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B) (h₃ : q₃ ∈ B)
    (h₄ : q₄ ∈ B) (h₅ : q₅ ∈ B) (h21 : q₂ ≠ q₁) (h31 : q₃ ≠ q₁) (h32 : q₃ ≠ q₂)
    (h41 : q₄ ≠ q₁) (h42 : q₄ ≠ q₂) (h43 : q₄ ≠ q₃) (h51 : q₅ ≠ q₁) (h52 : q₅ ≠ q₂)
    (h53 : q₅ ≠ q₃) (h54 : q₅ ≠ q₄) (g : ι → ℤ) :
    ∑ φ ∈ B, g φ = g q₁ + g q₂ + g q₃ + g q₄ + g q₅ +
      ∑ φ ∈ ((((B.erase q₁).erase q₂).erase q₃).erase q₄).erase q₅, g φ := by
  have m₂ : q₂ ∈ B.erase q₁ := Finset.mem_erase.mpr ⟨h21, h₂⟩
  have m₃ : q₃ ∈ (B.erase q₁).erase q₂ :=
    Finset.mem_erase.mpr ⟨h32, Finset.mem_erase.mpr ⟨h31, h₃⟩⟩
  have m₄ : q₄ ∈ ((B.erase q₁).erase q₂).erase q₃ :=
    Finset.mem_erase.mpr ⟨h43, Finset.mem_erase.mpr ⟨h42, Finset.mem_erase.mpr ⟨h41, h₄⟩⟩⟩
  have m₅ : q₅ ∈ (((B.erase q₁).erase q₂).erase q₃).erase q₄ :=
    Finset.mem_erase.mpr ⟨h54, Finset.mem_erase.mpr ⟨h53,
      Finset.mem_erase.mpr ⟨h52, Finset.mem_erase.mpr ⟨h51, h₅⟩⟩⟩⟩
  rw [← Finset.add_sum_erase B g h₁, ← Finset.add_sum_erase _ g m₂,
    ← Finset.add_sum_erase _ g m₃, ← Finset.add_sum_erase _ g m₄,
    ← Finset.add_sum_erase _ g m₅]
  ring

theorem sign_of_sq_sum_le_card_odd {R O : Finset ι} {g : ι → ℤ} (hOR : O ⊆ R)
    (hodd : ∀ φ ∈ O, Odd (g φ)) (hsq : ∑ φ ∈ R, g φ * g φ ≤ O.card) :
    ∀ φ ∈ O, g φ = 1 ∨ g φ = -1 := by
  intro φ₀ hφ₀
  have hle : ∑ φ ∈ O, g φ * g φ ≤ O.card := le_trans (Finset.sum_le_sum_of_subset_of_nonneg hOR
    fun φ _ _ => mul_self_nonneg _) hsq
  have hrest : ((O.erase φ₀).card : ℤ) ≤ ∑ φ ∈ O.erase φ₀, g φ * g φ := by
    calc ((O.erase φ₀).card : ℤ) = ∑ _φ ∈ O.erase φ₀, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun φ hφ =>
          one_le_mul_self_of_odd (hodd φ (Finset.mem_of_mem_erase hφ))
  have hsplit := Finset.add_sum_erase O (fun φ => g φ * g φ) hφ₀
  have hcard : ((O.erase φ₀).card : ℤ) + 1 = O.card := by
    rw [Finset.card_erase_of_mem hφ₀]
    have : 1 ≤ O.card := Finset.card_pos.mpr ⟨φ₀, hφ₀⟩
    push_cast [Nat.cast_sub this]
    ring
  have h1 : g φ₀ * g φ₀ ≤ 1 := by linarith
  have h2 : g φ₀ ≤ 1 := by nlinarith
  have h3 : -1 ≤ g φ₀ := by nlinarith
  have hodd' := hodd φ₀ hφ₀
  rw [Int.odd_iff] at hodd'
  omega

theorem odd_of_modEq_two {a b : ℤ} (h : a ≡ b [ZMOD 2]) (hb : Odd b) : Odd a := by
  rw [Int.odd_iff] at hb ⊢
  unfold Int.ModEq at h
  omega

theorem eq_zero_of_modEq_zero_of_mul_self_le_one {a : ℤ} (ha : a ≡ 0 [ZMOD 2])
    (h : a * a ≤ 1) : a = 0 := by
  have h1 : -1 ≤ a := by nlinarith
  have h2 : a ≤ 1 := by nlinarith
  unfold Int.ModEq at ha
  omega

theorem sign_of_odd_of_mul_self_le_one {a : ℤ} (ha : Odd a) (h : a * a ≤ 1) :
    a = 1 ∨ a = -1 := by
  have h1 : -1 ≤ a := by nlinarith
  have h2 : a ≤ 1 := by nlinarith
  rw [Int.odd_iff] at ha
  omega

theorem mul_self_le_one_of_three_mul {a s : ℤ} (h : 3 * (a * a) + s = 4) (hs : 0 ≤ s) :
    a * a ≤ 1 := by
  omega

theorem even_column_relations {σ τ₀ κ yB yD yω xB xD xω s : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1) (h1 : -(τ₀ * yB) + κ * yD = 0)
    (h2 : -(τ₀ * yB) - κ * yD + 2 * τ₀ * yω = 0) (h3 : -1 - σ * σ - τ₀ * xB + κ * xD = 0)
    (h4 : -1 + σ * σ - τ₀ * xB - κ * xD + 2 * τ₀ * xω = 0)
    (hn : 8 = 1 + σ * σ + xB * xB + xD * xD + xω * xω + s) :
    yD = κ * τ₀ * yB ∧ yω = yB ∧ xB = xω - τ₀ ∧ xD = κ + κ * τ₀ * xω ∧
      3 * (xω * xω) + s = 4 := by
  have hrel : yD = κ * τ₀ * yB ∧ yω = yB ∧ xB = xω - τ₀ ∧ xD = κ + κ * τ₀ * xω := by
    rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨hrel.1, hrel.2.1, hrel.2.2.1, hrel.2.2.2, ?_⟩
  rw [hrel.2.2.1, hrel.2.2.2] at hn
  rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;>
    linarith

theorem even_column_contra {τ₀ κ yB xω yψ xψ : ℤ} (hτ₀ : τ₀ = 1 ∨ τ₀ = -1)
    (hκ : κ = 1 ∨ κ = -1) (hyB : yB = 1 ∨ yB = -1) (hxω : xω = 1 ∨ xω = -1)
    (hyψ : yψ = 1 ∨ yψ = -1) (hxψ : xψ = 1 ∨ xψ = -1)
    (hip : yB * (xω - τ₀) + κ * τ₀ * yB * (κ + κ * τ₀ * xω) + yB * xω + yψ * xψ = 0) :
    False := by
  rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;> rcases hyB with rfl | rfl <;>
    rcases hxω with rfl | rfl <;> rcases hyψ with rfl | rfl <;> rcases hxψ with rfl | rfl <;>
    norm_num at hip

theorem even_column {A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {y₀ C yr xk : ι → ℤ}
    (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B) (hDq : Dq ∈ B) (hω : ω ∈ B)
    (hAp : A ≠ p) (hBp : Bq ≠ p) (hDp : Dq ≠ p) (hωp : ω ≠ p) (hBA : Bq ≠ A) (hDA : Dq ≠ A)
    (hωA : ω ≠ A) (hDB : Dq ≠ Bq) (hωB : ω ≠ Bq) (hωD : ω ≠ Dq)
    (hσ : σ = 1 ∨ σ = -1) (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1)
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + σ * unitVector A φ - τ₀ * unitVector Bq φ +
      κ * unitVector Dq φ)
    (hC : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
      κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ)
    (hyv : ∀ φ ∈ B, yr φ = 0 ∨ yr φ = 1 ∨ yr φ = -1)
    (hy4 : (B.filter fun φ => yr φ ≠ 0).card = 4) (hyp : yr p = 0) (hyA : yr A = 0)
    (hyy₀ : ∑ φ ∈ B, yr φ * y₀ φ = 0) (hyC : ∑ φ ∈ B, yr φ * C φ = 0)
    (hyx : ∑ φ ∈ B, yr φ * xk φ = 0) (hxp : xk p = -1) (hxA : xk A = -σ)
    (hxsq : ∑ φ ∈ B, xk φ * xk φ = 8) (hxy₀ : ∑ φ ∈ B, xk φ * y₀ φ = 0)
    (hxC : ∑ φ ∈ B, xk φ * C φ = 0) (hpar : ∀ φ ∈ B, xk φ ≡ y₀ φ + yr φ [ZMOD 2]) :
    yr Bq = 0 ∧ yr Dq = 0 ∧ yr ω = 0 ∧ xk Bq = -τ₀ ∧ xk Dq = κ ∧ xk ω = 0 ∧
      (∀ φ ∈ B, yr φ ≠ 0 → xk φ = 1 ∨ xk φ = -1) ∧
      ∀ φ ∈ B, φ ≠ p → φ ≠ A → φ ≠ Bq → φ ≠ Dq → yr φ = 0 → xk φ = 0 := by
  have ey₀ : ∀ f : ι → ℤ, ∑ φ ∈ B, f φ * y₀ φ = f p + σ * f A - τ₀ * f Bq + κ * f Dq := by
    intro f
    calc ∑ φ ∈ B, f φ * y₀ φ = ∑ φ ∈ B, f φ * (1 * unitVector p φ + σ * unitVector A φ +
        (-τ₀) * unitVector Bq φ + κ * unitVector Dq φ + 0 * unitVector ω φ) :=
          Finset.sum_congr rfl fun φ hφ => by rw [hy₀ φ hφ]; ring
      _ = _ := by rw [sum_mul_five_unitVector hp hA hBq hDq hω]; ring
  have eC : ∀ f : ι → ℤ, ∑ φ ∈ B, f φ * C φ =
      f p - σ * f A - τ₀ * f Bq - κ * f Dq + 2 * τ₀ * f ω := by
    intro f
    calc ∑ φ ∈ B, f φ * C φ = ∑ φ ∈ B, f φ * (1 * unitVector p φ + (-σ) * unitVector A φ +
        (-τ₀) * unitVector Bq φ + (-κ) * unitVector Dq φ + (2 * τ₀) * unitVector ω φ) :=
          Finset.sum_congr rfl fun φ hφ => by rw [hC φ hφ]; ring
      _ = _ := by rw [sum_mul_five_unitVector hp hA hBq hDq hω]; ring
  have e1 := hyy₀
  rw [ey₀, hyp, hyA] at e1
  have e2 := hyC
  rw [eC, hyp, hyA] at e2
  have e3 := hxy₀
  rw [ey₀, hxp, hxA] at e3
  have e4 := hxC
  rw [eC, hxp, hxA] at e4
  set R := ((((B.erase p).erase A).erase Bq).erase Dq).erase ω with hR
  have hmemR : ∀ φ, φ ∈ R ↔ φ ∈ B ∧ φ ≠ p ∧ φ ≠ A ∧ φ ≠ Bq ∧ φ ≠ Dq ∧ φ ≠ ω := by
    intro φ
    simp only [hR, Finset.mem_erase]
    tauto
  have hn := sum_five_add_rest hp hA hBq hDq hω hAp hBp hBA hDp hDA hDB hωp hωA hωB hωD
    (fun φ => xk φ * xk φ)
  rw [hxsq, hxp, hxA, ← hR] at hn
  have hRnn : 0 ≤ ∑ φ ∈ R, xk φ * xk φ := Finset.sum_nonneg fun φ _ => mul_self_nonneg _
  have hy₀ω : y₀ ω = 0 := by
    rw [hy₀ ω hω, unitVector_of_ne hωp, unitVector_of_ne hωA, unitVector_of_ne hωB,
      unitVector_of_ne hωD]
    ring
  have hy₀R : ∀ φ ∈ R, y₀ φ = 0 := by
    intro φ hφ
    obtain ⟨hφB, hφp, hφA, hφBq, hφDq, -⟩ := (hmemR φ).mp hφ
    rw [hy₀ φ hφB, unitVector_of_ne hφp, unitVector_of_ne hφA, unitVector_of_ne hφBq,
      unitVector_of_ne hφDq]
    ring
  have hparR : ∀ φ ∈ R, xk φ ≡ yr φ [ZMOD 2] := fun φ hφ => by
    have h := hpar φ ((hmemR φ).mp hφ).1
    rwa [hy₀R φ hφ, zero_add] at h
  have hparω : xk ω ≡ yr ω [ZMOD 2] := by
    have h := hpar ω hω
    rwa [hy₀ω, zero_add] at h
  set Sy := B.filter fun φ => yr φ ≠ 0 with hSy
  have hmemSy : ∀ φ, φ ∈ Sy ↔ φ ∈ B ∧ yr φ ≠ 0 := fun φ => by rw [hSy, Finset.mem_filter]
  have hoddSy : ∀ φ ∈ B, yr φ ≠ 0 → Odd (yr φ) := fun φ hφ hne => by
    rcases hyv φ hφ with h | h | h
    · exact absurd h hne
    · rw [h]
      decide
    · rw [h]
      decide
  obtain ⟨hyD, hyω, hxB, hxD, hkey⟩ := even_column_relations (yB := yr Bq) (yD := yr Dq)
    (yω := yr ω) (xB := xk Bq) (xD := xk Dq) (xω := xk ω) (s := ∑ φ ∈ R, xk φ * xk φ) hσ hτ₀ hκ
    (by linear_combination e1) (by linear_combination e2) (by linear_combination e3)
    (by linear_combination e4) (by linear_combination hn)
  have hxω2 : xk ω * xk ω ≤ 1 := mul_self_le_one_of_three_mul hkey hRnn
  rcases hyv Bq hBq with hyB | hyB
  ·
    have hyD0 : yr Dq = 0 := by rw [hyD, hyB, mul_zero]
    have hyω0 : yr ω = 0 := by rw [hyω, hyB]
    have hxω : xk ω = 0 :=
      eq_zero_of_modEq_zero_of_mul_self_le_one (by rw [← hyω0]; exact hparω) hxω2
    have hR4 : ∑ φ ∈ R, xk φ * xk φ = 4 := by
      rw [hxω] at hkey
      linarith only [hkey]
    have hSyR : Sy ⊆ R := by
      intro φ hφ
      obtain ⟨hφB, hne⟩ := (hmemSy φ).mp hφ
      refine (hmemR φ).mpr ⟨hφB, ?_, ?_, ?_, ?_, ?_⟩
      · rintro rfl
        exact hne hyp
      · rintro rfl
        exact hne hyA
      · rintro rfl
        exact hne hyB
      · rintro rfl
        exact hne hyD0
      · rintro rfl
        exact hne hyω0
    have hoddx : ∀ φ ∈ Sy, Odd (xk φ) := fun φ hφ => by
      obtain ⟨hφB, hne⟩ := (hmemSy φ).mp hφ
      exact odd_of_modEq_two (hparR φ (hSyR hφ)) (hoddSy φ hφB hne)
    have hle : ∑ φ ∈ R, xk φ * xk φ ≤ Sy.card := by
      rw [hR4, hy4]
      norm_num
    refine ⟨hyB, hyD0, hyω0, by rw [hxB, hxω, zero_sub], by rw [hxD, hxω, mul_zero, add_zero],
      hxω, fun φ hφ hne => sign_of_sq_sum_le_card_odd hSyR hoddx hle φ
        ((hmemSy φ).mpr ⟨hφ, hne⟩), ?_⟩
    intro φ hφ hφp hφA hφB hφD hy0
    by_cases hφω : φ = ω
    · rw [hφω, hxω]
    · exact eq_zero_of_sq_sum_le_card_odd hSyR ((hmemR φ).mpr ⟨hφ, hφp, hφA, hφB, hφD, hφω⟩)
        (fun h => ((hmemSy φ).mp h).2 hy0) hoddx hle
  exfalso
  have hyB0 : yr Bq ≠ 0 := by rcases hyB with h | h <;> rw [h] <;> norm_num
  have hyD0 : yr Dq ≠ 0 := by
    rw [hyD]
    exact mul_ne_zero (mul_ne_zero (by rcases hκ with h | h <;> rw [h] <;> norm_num)
      (by rcases hτ₀ with h | h <;> rw [h] <;> norm_num)) hyB0
  have hyω0 : yr ω ≠ 0 := by rw [hyω]; exact hyB0
  have hxωodd : Odd (xk ω) := odd_of_modEq_two hparω (by
    rw [hyω]
    rcases hyB with h | h <;> rw [h] <;> decide)
  have hxω1 : xk ω * xk ω = 1 := le_antisymm hxω2 (one_le_mul_self_of_odd hxωodd)
  have hR1 : ∑ φ ∈ R, xk φ * xk φ = 1 := by
    rw [hxω1] at hkey
    linarith only [hkey]
  have hsub : ({Bq, Dq, ω} : Finset ι) ⊆ Sy := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact (hmemSy _).mpr ⟨hBq, hyB0⟩
    · exact (hmemSy _).mpr ⟨hDq, hyD0⟩
    · exact (hmemSy _).mpr ⟨hω, hyω0⟩
  have hcard3 : ({Bq, Dq, ω} : Finset ι).card < Sy.card := by
    rw [hy4]
    exact lt_of_le_of_lt Finset.card_le_three (by norm_num)
  obtain ⟨ψ, hψS, hψn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard3
  obtain ⟨hψB, hyψ0⟩ := (hmemSy ψ).mp hψS
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hψn
  obtain ⟨hψBq, hψDq, hψω⟩ := hψn
  have hψp : ψ ≠ p := fun h => hyψ0 (by rw [h, hyp])
  have hψA : ψ ≠ A := fun h => hyψ0 (by rw [h, hyA])
  have hψR : ψ ∈ R := (hmemR ψ).mpr ⟨hψB, hψp, hψA, hψBq, hψDq, hψω⟩
  have hsub4 : ({Bq, Dq, ω, ψ} : Finset ι) ⊆ Sy := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact (hmemSy _).mpr ⟨hBq, hyB0⟩
    · exact (hmemSy _).mpr ⟨hDq, hyD0⟩
    · exact (hmemSy _).mpr ⟨hω, hyω0⟩
    · exact hψS
  have hcard4 : ({Bq, Dq, ω, ψ} : Finset ι).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hDB.symm, hωB.symm, Ne.symm hψBq]),
      Finset.card_insert_of_notMem (by simp [hωD.symm, Ne.symm hψDq]),
      Finset.card_pair (Ne.symm hψω)]
  have hSyeq : ({Bq, Dq, ω, ψ} : Finset ι) = Sy :=
    Finset.eq_of_subset_of_card_le hsub4 (by rw [hcard4, hy4])
  have hy0 : ∀ φ ∈ B, φ ≠ Bq → φ ≠ Dq → φ ≠ ω → φ ≠ ψ → yr φ = 0 := by
    intro φ hφ h1 h2 h3 h4
    by_contra hne
    have hφS : φ ∈ Sy := (hmemSy φ).mpr ⟨hφ, hne⟩
    rw [← hSyeq] at hφS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφS
    rcases hφS with h | h | h | h <;> contradiction
  have hxψodd : Odd (xk ψ) := odd_of_modEq_two (hparR ψ hψR) (hoddSy ψ hψB hyψ0)
  have hxψ1 : xk ψ * xk ψ ≤ 1 := by
    have hle := Finset.single_le_sum (f := fun φ => xk φ * xk φ)
      (fun φ _ => mul_self_nonneg _) hψR
    rw [hR1] at hle
    exact hle
  have hip := hyx
  rw [sum_mul_four hBq hDq hω hψB hDB (Ne.symm hωD) (Ne.symm hψDq) hωB hψBq (Ne.symm hψω)
    hy0, hyD, hyω, hxB, hxD] at hip
  have hyψ : yr ψ = 1 ∨ yr ψ = -1 := by
    rcases hyv ψ hψB with h | h
    · exact absurd h hyψ0
    · exact h
  exact even_column_contra hτ₀ hκ hyB (sign_of_odd_of_mul_self_le_one hxωodd hxω2) hyψ
    (sign_of_odd_of_mul_self_le_one hxψodd hxψ1) (by linear_combination hip)

end CFSG.Wreathed.ConditionalFiveFixed
