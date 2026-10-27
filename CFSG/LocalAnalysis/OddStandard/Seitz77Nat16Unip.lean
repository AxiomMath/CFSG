module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Basic
public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Table
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

variable {F : Type*} [Field F]

section Sums

variable (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)

include hF hζ

theorem sum_zeta : ζ ^ 2 + ζ ^ 3 + ζ ^ 5 + ζ ^ 7 = 1 := by
  have := charP_two hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (ζ ^ 3 + ζ + 1) * hζ + (ζ ^ 3 + ζ ^ 2 + ζ) * h2

theorem sum_zeta_inv : ζ⁻¹ ^ 2 + ζ⁻¹ ^ 3 + ζ⁻¹ ^ 5 + ζ⁻¹ ^ 7 = 0 := by
  have := charP_two hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hz := zeta_ne_zero hζ
  have h4 : ζ ^ 4 + ζ + 1 = 0 := by linear_combination hζ + (ζ + 1) * h2
  have hu4 : ζ⁻¹ ^ 4 + ζ⁻¹ ^ 3 + 1 = 0 := by
    have : ζ⁻¹ ^ 4 + ζ⁻¹ ^ 3 + 1 = ζ⁻¹ ^ 4 * (ζ ^ 4 + ζ + 1) := by
      field_simp
      ring
    rw [this, h4, mul_zero]
  linear_combination (ζ⁻¹ ^ 3 + ζ⁻¹ ^ 2) * hu4 + (-ζ⁻¹ ^ 6) * h2

end Sums

section CaseA

variable (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)
variable (U : F → (F × F →+ F × F)) (h0 : ∀ v, U 0 v = v)
  (hadd : ∀ c c' v, U (c + c') v = U c (U c' v))
  (hequiv : ∀ c v, (ζ * (U c v).1, ζ⁻¹ * (U c v).2) = U (ζ * ζ * c) (ζ * v.1, ζ⁻¹ * v.2))

include hF hζ h0 hadd hequiv

theorem unip_caseA (hA : ∀ s c, U c (s, 0) = (s, 0)) :
    ∃ κ : F, ∀ c v, U c v = (v.1 + κ * c * v.2, v.2) := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  have hz : ζ ≠ 0 := zeta_ne_zero hζ
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hv : ∀ c v, U c v = (v.1 + (U c (0, v.2)).1, (U c (0, v.2)).2) := by
    intro c v
    have hv' : v = (v.1, 0) + (0, v.2) := by ext <;> simp
    conv_lhs => rw [hv', map_add, hA]
    ext <;> simp
  have hact : ∀ c c' y, U (c + c') (0, y) =
      ((U c' (0, y)).1 + (U c (0, (U c' (0, y)).2)).1, (U c (0, (U c' (0, y)).2)).2) := by
    intro c c' y
    rw [hadd, hv c (U c' (0, y))]
  have hd_add : ∀ c c' y, (U (c + c') (0, y)).2 = (U c (0, (U c' (0, y)).2)).2 := by
    intro c c' y
    rw [hact]
  have hd_zero : ∀ y, (U 0 (0, y)).2 = y := fun y => by rw [h0]
  have hd_map : ∀ c y y', (U c (0, y + y')).2 = (U c (0, y)).2 + (U c (0, y')).2 := by
    intro c y y'
    have : ((0 : F), y + y') = (0, y) + (0, y') := by simp
    rw [this, map_add]
    rfl
  let dd : F → (F →+ F) := fun c =>
    AddMonoidHom.mk' (fun y => (U c (0, y)).2) (hd_map c)
  obtain ⟨y₀, hy₀, hfix⟩ := exists_fixed_ne_zero (G := F) (M := F) hF (by rw [hF]; decide) dd
    hd_zero (fun c c' y => hd_add c c' y)
  have hfix' : ∀ c, (U c (0, y₀)).2 = y₀ := hfix
  have heq : ∀ c y, (ζ * (U c (0, y)).1, ζ⁻¹ * (U c (0, y)).2) =
      U (ζ * ζ * c) (0, ζ⁻¹ * y) := by
    intro c y
    have := hequiv c (0, y)
    simpa using this
  have heq2 : ∀ c y, ζ⁻¹ * (U c (0, y)).2 = (U (ζ * ζ * c) (0, ζ⁻¹ * y)).2 := by
    intro c y
    have := congrArg Prod.snd (heq c y)
    simpa using this
  have heq1 : ∀ c y, ζ * (U c (0, y)).1 = (U (ζ * ζ * c) (0, ζ⁻¹ * y)).1 := by
    intro c y
    have := congrArg Prod.fst (heq c y)
    simpa using this
  have hclosed : ∀ y, (∀ c, (U c (0, y)).2 = y) → ∀ c, (U c (0, ζ * y)).2 = ζ * y := by
    intro y hy c
    have h1 := heq2 c (ζ * y)
    rw [inv_mul_cancel_left₀ hz, hy] at h1
    calc (U c (0, ζ * y)).2 = ζ * (ζ⁻¹ * (U c (0, ζ * y)).2) := by field_simp
      _ = ζ * y := by rw [h1]
  have hall : ∀ s c, (U c (0, s)).2 = s := by
    intro s c
    by_cases hs : s = 0
    · subst hs
      have : ((0 : F), (0 : F)) = 0 := rfl
      rw [this, map_zero]
      rfl
    · obtain ⟨k, hk⟩ := exists_pow_eq hF hord (div_ne_zero hs hy₀)
      have hpow : ∀ k : ℕ, ∀ c, (U c (0, ζ ^ k * y₀)).2 = ζ ^ k * y₀ := by
        intro k
        induction k with
        | zero => intro c; simpa using hfix' c
        | succ k ih =>
          intro c
          rw [pow_succ', mul_assoc]
          exact hclosed _ ih c
      have hs' : s = ζ ^ k * y₀ := by rw [hk]; field_simp
      rw [hs']
      exact hpow k c
  have hb_y : ∀ c y y', (U c (0, y + y')).1 = (U c (0, y)).1 + (U c (0, y')).1 := by
    intro c y y'
    have : ((0 : F), y + y') = (0, y) + (0, y') := by simp
    rw [this, map_add]
    rfl
  have hb_c : ∀ c c' y, (U (c + c') (0, y)).1 = (U c (0, y)).1 + (U c' (0, y)).1 := by
    intro c c' y
    have h1 := congrArg Prod.fst (hact c c' y)
    simp only at h1
    rw [h1, hall y c', add_comm]
  have hweights : ∀ x y, (U (ζ ^ 2 * x) (0, ζ ^ 14 * y)).1 = ζ * (U x (0, y)).1 := by
    intro x y
    have h1 := heq1 x y
    rw [Weights16.inv_eq_pow_fourteen hord] at h1
    rw [h1, pow_two]
  obtain ⟨κ, hκ⟩ := Weights16.biadditive_U_Lambda_W0 hF hord
    (β := fun c y => (U c (0, y)).1) (fun x x' y => hb_c x x' y) (fun x y y' => hb_y x y y')
    hweights
  refine ⟨κ, fun c v => ?_⟩
  rw [hv c v, hall v.2 c, hκ c v.2]

theorem unip_caseB (hB : ∀ s c, U c (0, s) = (0, s)) : ∀ c v, U c v = v := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  have hz : ζ ≠ 0 := zeta_ne_zero hζ
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hv : ∀ c v, U c v = ((U c (v.1, 0)).1, (U c (v.1, 0)).2 + v.2) := by
    intro c v
    have hv' : v = (v.1, 0) + (0, v.2) := by ext <;> simp
    conv_lhs => rw [hv', map_add, hB]
    ext <;> simp
  have hact : ∀ c c' x, U (c + c') (x, 0) = ((U c ((U c' (x, 0)).1, 0)).1,
      (U c ((U c' (x, 0)).1, 0)).2 + (U c' (x, 0)).2) := by
    intro c c' x
    rw [hadd, hv c (U c' (x, 0))]
  have ha_add : ∀ c c' x, (U (c + c') (x, 0)).1 = (U c ((U c' (x, 0)).1, 0)).1 := by
    intro c c' x
    rw [hact]
  have ha_zero : ∀ x, (U 0 (x, 0)).1 = x := fun x => by rw [h0]
  have ha_map : ∀ c x x', (U c (x + x', 0)).1 = (U c (x, 0)).1 + (U c (x', 0)).1 := by
    intro c x x'
    have : (x + x', (0 : F)) = (x, 0) + (x', 0) := by simp
    rw [this, map_add]
    rfl
  let aa : F → (F →+ F) := fun c =>
    AddMonoidHom.mk' (fun x => (U c (x, 0)).1) (ha_map c)
  obtain ⟨x₀, hx₀, hfix⟩ := exists_fixed_ne_zero (G := F) (M := F) hF (by rw [hF]; decide) aa
    ha_zero (fun c c' x => ha_add c c' x)
  have hfix' : ∀ c, (U c (x₀, 0)).1 = x₀ := hfix
  have heq : ∀ c x, (ζ * (U c (x, 0)).1, ζ⁻¹ * (U c (x, 0)).2) = U (ζ * ζ * c) (ζ * x, 0) := by
    intro c x
    have := hequiv c (x, 0)
    simpa using this
  have heq1 : ∀ c x, ζ * (U c (x, 0)).1 = (U (ζ * ζ * c) (ζ * x, 0)).1 := by
    intro c x
    have := congrArg Prod.fst (heq c x)
    simpa using this
  have heq2 : ∀ c x, ζ⁻¹ * (U c (x, 0)).2 = (U (ζ * ζ * c) (ζ * x, 0)).2 := by
    intro c x
    have := congrArg Prod.snd (heq c x)
    simpa using this
  have hclosed : ∀ x, (∀ c, (U c (x, 0)).1 = x) → ∀ c, (U c (ζ * x, 0)).1 = ζ * x := by
    intro x hx c
    have h1 := heq1 (ζ⁻¹ * ζ⁻¹ * c) x
    have h2 : ζ * ζ * (ζ⁻¹ * ζ⁻¹ * c) = c := by field_simp
    rw [h2, hx] at h1
    exact h1.symm
  have hall : ∀ x c, (U c (x, 0)).1 = x := by
    intro x c
    by_cases hx : x = 0
    · subst hx
      have : ((0 : F), (0 : F)) = 0 := rfl
      rw [this, map_zero]
      rfl
    · obtain ⟨k, hk⟩ := exists_pow_eq hF hord (div_ne_zero hx hx₀)
      have hpow : ∀ k : ℕ, ∀ c, (U c (ζ ^ k * x₀, 0)).1 = ζ ^ k * x₀ := by
        intro k
        induction k with
        | zero => intro c; simpa using hfix' c
        | succ k ih =>
          intro c
          rw [pow_succ', mul_assoc]
          exact hclosed _ ih c
      have hx' : x = ζ ^ k * x₀ := by rw [hk]; field_simp
      rw [hx']
      exact hpow k c
  have he_x : ∀ c x x', (U c (x + x', 0)).2 = (U c (x, 0)).2 + (U c (x', 0)).2 := by
    intro c x x'
    have : (x + x', (0 : F)) = (x, 0) + (x', 0) := by simp
    rw [this, map_add]
    rfl
  have he_c : ∀ c c' x, (U (c + c') (x, 0)).2 = (U c (x, 0)).2 + (U c' (x, 0)).2 := by
    intro c c' x
    have h1 := congrArg Prod.snd (hact c c' x)
    simp only at h1
    rw [h1, hall x c']
  have hweights : ∀ x y, (U (ζ ^ 2 * x) (ζ * y, 0)).2 = ζ ^ 14 * (U x (y, 0)).2 := by
    intro x y
    have h1 := heq2 x y
    rw [Weights16.inv_eq_pow_fourteen hord] at h1
    rw [pow_two]
    exact h1.symm
  have he0 := Weights16.biadditive_U_W0_Lambda hF hord (β := fun c x => (U c (x, 0)).2)
    (fun x x' y => he_c x x' y) (fun x y y' => he_x x y y') hweights
  intro c v
  rw [hv c v, hall v.1 c, he0 c v.1, zero_add]


theorem unip_form (hnt : ∃ v, U 1 v ≠ v) :
    ∃ κ : F, κ ≠ 0 ∧ ∀ c v, U c v = (v.1 + κ * c * v.2, v.2) := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  have hz : ζ ≠ 0 := zeta_ne_zero hζ
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨w, hw0, hwfix⟩ := exists_fixed_ne_zero (G := F) (M := F × F) hF
    (by rw [Nat.card_prod, hF]; decide) U h0 hadd
  have hH : ∀ w : F × F, (∀ c, U c w = w) →
      ∀ c, U c (ζ * w.1, ζ⁻¹ * w.2) = (ζ * w.1, ζ⁻¹ * w.2) := by
    intro w hw c
    have h1 := hequiv (ζ⁻¹ * ζ⁻¹ * c) w
    have h2 : ζ * ζ * (ζ⁻¹ * ζ⁻¹ * c) = c := by field_simp
    rw [h2, hw] at h1
    exact h1.symm
  have hHi : ∀ w : F × F, (∀ c, U c w = w) →
      ∀ c, U c (ζ⁻¹ * w.1, ζ * w.2) = (ζ⁻¹ * w.1, ζ * w.2) := by
    intro w hw c
    have h1 := hequiv c (ζ⁻¹ * w.1, ζ * w.2)
    have h2 : (ζ * (ζ⁻¹ * w.1), ζ⁻¹ * (ζ * w.2)) = w := by
      ext <;> simp [hz]
    simp only at h1
    rw [h2, hw] at h1
    have h3 := congrArg Prod.fst h1
    have h4 := congrArg Prod.snd h1
    simp only at h3 h4
    refine Prod.ext ?_ ?_
    · calc (U c (ζ⁻¹ * w.1, ζ * w.2)).1 = ζ⁻¹ * (ζ * (U c (ζ⁻¹ * w.1, ζ * w.2)).1) := by
            field_simp
        _ = ζ⁻¹ * w.1 := by rw [h3]
    · calc (U c (ζ⁻¹ * w.1, ζ * w.2)).2 = ζ * (ζ⁻¹ * (U c (ζ⁻¹ * w.1, ζ * w.2)).2) := by
            field_simp
        _ = ζ * w.2 := by rw [h4]
  have hHk : ∀ k : ℕ, ∀ w : F × F, (∀ c, U c w = w) →
      ∀ c, U c (ζ ^ k * w.1, ζ⁻¹ ^ k * w.2) = (ζ ^ k * w.1, ζ⁻¹ ^ k * w.2) := by
    intro k
    induction k with
    | zero => intro w hw c; simpa using hw c
    | succ k ih =>
      intro w hw c
      have := hH _ (ih w hw) c
      simpa [pow_succ', mul_assoc] using this
  have hHik : ∀ k : ℕ, ∀ w : F × F, (∀ c, U c w = w) →
      ∀ c, U c (ζ⁻¹ ^ k * w.1, ζ ^ k * w.2) = (ζ⁻¹ ^ k * w.1, ζ ^ k * w.2) := by
    intro k
    induction k with
    | zero => intro w hw c; simpa using hw c
    | succ k ih =>
      intro w hw c
      have := hHi _ (ih w hw) c
      simpa [pow_succ', mul_assoc] using this
  have hproj1 : ∀ w : F × F, (∀ c, U c w = w) → ∀ c, U c (w.1, 0) = (w.1, 0) := by
    intro w hw c
    have hs : (w.1, (0 : F)) = (ζ ^ 2 * w.1, ζ⁻¹ ^ 2 * w.2) + (ζ ^ 3 * w.1, ζ⁻¹ ^ 3 * w.2) +
        (ζ ^ 5 * w.1, ζ⁻¹ ^ 5 * w.2) + (ζ ^ 7 * w.1, ζ⁻¹ ^ 7 * w.2) := by
      ext
      · simp only [Prod.fst_add]
        linear_combination (-w.1) * sum_zeta hF hζ
      · simp only [Prod.snd_add]
        linear_combination (-w.2) * sum_zeta_inv hF hζ
    rw [hs, map_add, map_add, map_add, hHk 2 w hw c, hHk 3 w hw c, hHk 5 w hw c, hHk 7 w hw c]
  have hproj2 : ∀ w : F × F, (∀ c, U c w = w) → ∀ c, U c (0, w.2) = (0, w.2) := by
    intro w hw c
    have hs : ((0 : F), w.2) = (ζ⁻¹ ^ 2 * w.1, ζ ^ 2 * w.2) + (ζ⁻¹ ^ 3 * w.1, ζ ^ 3 * w.2) +
        (ζ⁻¹ ^ 5 * w.1, ζ ^ 5 * w.2) + (ζ⁻¹ ^ 7 * w.1, ζ ^ 7 * w.2) := by
      ext
      · simp only [Prod.fst_add]
        linear_combination (-w.1) * sum_zeta_inv hF hζ
      · simp only [Prod.snd_add]
        linear_combination (-w.2) * sum_zeta hF hζ
    rw [hs, map_add, map_add, map_add, hHik 2 w hw c, hHik 3 w hw c, hHik 5 w hw c,
      hHik 7 w hw c]
  by_cases hx : w.1 = 0
  · have hy : w.2 ≠ 0 := by
      intro hy
      apply hw0
      ext <;> simp [hx, hy]
    have h02 := hproj2 w hwfix
    have hB : ∀ s c, U c (0, s) = (0, s) := by
      intro s c
      by_cases hs : s = 0
      · subst hs
        have : ((0 : F), (0 : F)) = 0 := rfl
        rw [this, map_zero]
      · obtain ⟨k, hk⟩ := exists_pow_eq hF hord (div_ne_zero hs hy)
        have := hHik k (0, w.2) h02 c
        simp only [mul_zero] at this
        have hs' : s = ζ ^ k * w.2 := by rw [hk]; field_simp
        rw [hs']
        exact this
    exfalso
    obtain ⟨v, hv⟩ := hnt
    exact hv (unip_caseB hF hζ U h0 hadd hequiv hB 1 v)
  · have h01 := hproj1 w hwfix
    have hA : ∀ s c, U c (s, 0) = (s, 0) := by
      intro s c
      by_cases hs : s = 0
      · subst hs
        have : ((0 : F), (0 : F)) = 0 := rfl
        rw [this, map_zero]
      · obtain ⟨k, hk⟩ := exists_pow_eq hF hord (div_ne_zero hs hx)
        have := hHk k (w.1, 0) h01 c
        simp only [mul_zero] at this
        have hs' : s = ζ ^ k * w.1 := by rw [hk]; field_simp
        rw [hs']
        exact this
    obtain ⟨κ, hκ⟩ := unip_caseA hF hζ U h0 hadd hequiv hA
    refine ⟨κ, ?_, hκ⟩
    rintro rfl
    obtain ⟨v, hv⟩ := hnt
    apply hv
    rw [hκ 1 v]
    simp

end CaseA


end Nat16

end CFSG.OddStandard.Seitz77
