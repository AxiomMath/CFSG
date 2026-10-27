module

public import CFSG.ClassicalInvolution.Uniform.U4Basic
public import CFSG.ClassicalInvolution.Asc77.Lemma310

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4

variable {F : Type} [Group F] [Finite F]

theorem exists_fixed_mul_mem {c : F} (hc : c * c = 1) {N : Subgroup F} (hN : Odd (Nat.card N))
    (hcN : ∀ n ∈ N, c * n * c⁻¹ ∈ N) {x : F} (hx : x⁻¹ * (c * x * c⁻¹) ∈ N) :
    ∃ n ∈ N, c * (x * n) * c⁻¹ = x * n := by
  classical
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  set S : Set F := {y | x⁻¹ * y ∈ N} with hS
  have hmem : ∀ y ∈ S, c * y * c⁻¹ ∈ S := by
    intro y hy
    have h1 : x⁻¹ * (c * y * c⁻¹) = (x⁻¹ * (c * x * c⁻¹)) * (c * (x⁻¹ * y) * c⁻¹) := by group
    show x⁻¹ * (c * y * c⁻¹) ∈ N
    rw [h1]
    exact N.mul_mem hx (hcN _ hy)
  have hinv : ∀ y : F, c * (c * y * c⁻¹) * c⁻¹ = y := by
    intro y
    rw [hci]
    calc c * (c * y * c) * c = (c * c) * y * (c * c) := by group
      _ = y := by rw [hc]; group
  let σ : Equiv.Perm S :=
    { toFun := fun y => ⟨c * y * c⁻¹, hmem y y.2⟩
      invFun := fun y => ⟨c * y * c⁻¹, hmem y y.2⟩
      left_inv := fun y => Subtype.ext (hinv y)
      right_inv := fun y => Subtype.ext (hinv y) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    apply Equiv.ext
    intro y
    apply Subtype.ext
    show c * (c * y.1 * c⁻¹) * c⁻¹ = y.1
    exact hinv y.1
  have hcard : Nat.card S = Nat.card N :=
    Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun n => ⟨x * n.1, by show x⁻¹ * (x * n.1) ∈ N; simp⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have : Fintype S := Fintype.ofFinite S
  have hodd : ¬ 2 ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Nat.not_even_iff_odd.mpr hN) ∘ even_iff_two_dvd.mpr
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hodd hσ
  refine ⟨x⁻¹ * a.1, a.2, ?_⟩
  rw [mul_inv_cancel_left]
  exact congrArg Subtype.val ha

theorem odd_orderOf_of_pow_mem {N : Subgroup F} (hN : Odd (Nat.card N)) {g : F} {m : ℕ}
    (hm : Odd m) (hg : g ^ m ∈ N) : Odd (orderOf g) := by
  have h1 : orderOf (g ^ m) ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N hg
    exact this
  have h2 : orderOf g ∣ m * orderOf (g ^ m) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
    exact pow_orderOf_eq_one _
  exact (hm.mul (hN.of_dvd_nat h1)).of_dvd_nat h2

end CFSG.ClassicalInvolution.Q3.Q3T6B
