module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

section Coset

variable {A : Type} [Group A] [Finite A]

theorem exists_mem_coset_centralized {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X X₀ U : Subgroup A}
    (hX : IsPGroup p ↥X) (hX₀ : X₀ ≤ X) (hX₀n : ∀ x ∈ X, ∀ y ∈ X₀, x * y * x⁻¹ ∈ X₀)
    (hU : IsPGroup 2 ↥U) (hUX : U ≤ normalizer (X : Set A))
    (hUtriv : ∀ u ∈ U, ∀ x ∈ X, u * x * u⁻¹ * x⁻¹ ∈ X₀) {x : A} (hx : x ∈ X) :
    ∃ y ∈ X, x⁻¹ * y ∈ X₀ ∧ ∀ u ∈ U, u * y = y * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Type := {y : A // y ∈ X ∧ x⁻¹ * y ∈ X₀}
  have hmem : ∀ (u : ↥U) (y : T), (u : A) * y.1 * (u : A)⁻¹ ∈ X ∧
      x⁻¹ * ((u : A) * y.1 * (u : A)⁻¹) ∈ X₀ := by
    intro u y
    have huX : (u : A) ∈ normalizer (X : Set A) := hUX u.2
    have h1 : (u : A) * y.1 * (u : A)⁻¹ ∈ X := (mem_normalizer_iff.mp huX y.1).mp y.2.1
    refine ⟨h1, ?_⟩
    set w : A := x⁻¹ * y.1 with hw
    have hwX₀ : w ∈ X₀ := y.2.2
    have hwX : w ∈ X := hX₀ hwX₀
    have hc := hUtriv u u.2 x hx
    have hd := hUtriv u u.2 w hwX
    have hy : y.1 = x * w := by rw [hw]; group
    have hcalc : x⁻¹ * ((u : A) * y.1 * (u : A)⁻¹) =
        (x⁻¹ * ((u : A) * x * (u : A)⁻¹ * x⁻¹) * x⁻¹⁻¹) * (((u : A) * w * (u : A)⁻¹ * w⁻¹) * w) := by
      rw [hy]; group
    rw [hcalc]
    exact X₀.mul_mem (hX₀n x⁻¹ (X.inv_mem hx) _ hc) (X₀.mul_mem hd hwX₀)
  let _ : SMul ↥U T := ⟨fun u y => ⟨(u : A) * y.1 * (u : A)⁻¹, hmem u y⟩⟩
  have hsmul : ∀ (u : ↥U) (y : T), (u • y).1 = (u : A) * y.1 * (u : A)⁻¹ := fun _ _ => rfl
  let _ : MulAction ↥U T :=
    { one_smul := fun y => Subtype.ext (by rw [hsmul]; simp)
      mul_smul := fun u₁ u₂ y => Subtype.ext (by simp only [hsmul]; simp [mul_assoc]) }
  have hcard : Nat.card T = Nat.card ↥X₀ := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2.2⟩
        invFun := fun w => ⟨x * w.1, X.mul_mem hx (hX₀ w.2), by simp⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro y; exact Subtype.ext (by simp)
    · intro w; exact Subtype.ext (by simp)
  have hnd : ¬ 2 ∣ Nat.card T := by
    rw [hcard]
    obtain ⟨n, hn⟩ := (hX.to_subgroup (X₀.subgroupOf X)).exists_card_eq
    have hX₀card : Nat.card ↥X₀ = Nat.card ↥(X₀.subgroupOf X) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀).toEquiv).symm
    rw [hX₀card, hn]
    intro h2
    have : 2 ∣ p := by
      rcases n with _ | n
      · simp at h2
      · exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two (n := n + 1) h2
    have hp2' := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp this
    exact hp2 hp2'.symm
  obtain ⟨y, hy⟩ := hU.nonempty_fixed_point_of_prime_not_dvd_card T hnd
  refine ⟨y.1, y.2.1, y.2.2, fun u hu => ?_⟩
  have h2 : (u : A) * y.1 * (u : A)⁻¹ = y.1 := congrArg Subtype.val (hy ⟨u, hu⟩)
  rw [mul_inv_eq_iff_eq_mul] at h2
  exact h2

end Coset

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
