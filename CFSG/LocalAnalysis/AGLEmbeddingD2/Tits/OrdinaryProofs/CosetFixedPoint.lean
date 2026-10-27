module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint

theorem exists_fixed_point_in_coset {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A D : Subgroup G) (hA : IsPGroup p A) (hD : ¬ p ∣ Nat.card D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (l : G)
    (hl : ∀ a ∈ A, l⁻¹ * (a * l * a⁻¹) ∈ D) :
    ∃ d ∈ D, ∀ a ∈ A, a * (l * d) * a⁻¹ = l * d := by
  let T := {x : G // ∃ d ∈ D, x = l * d}
  have hstab : ∀ a : G, a ∈ A → ∀ x : T, ∃ d ∈ D, a * x.1 * a⁻¹ = l * d := by
    intro a ha x
    obtain ⟨d, hd, hx⟩ := x.2
    have he : l⁻¹ * (a * l * a⁻¹) ∈ D := hl a ha
    have hadj : a * d * a⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hAD ha) d).mp hd
    refine ⟨l⁻¹ * (a * l * a⁻¹) * (a * d * a⁻¹), D.mul_mem he hadj, ?_⟩
    rw [hx]
    simp [mul_assoc]
  let e : D ≃ T :=
    { toFun := fun d => ⟨l * d.1, d.1, d.2, rfl⟩
      invFun := fun x => ⟨l⁻¹ * x.1, by
        obtain ⟨d, hd, hx⟩ := x.2
        rw [hx, inv_mul_cancel_left]
        exact hd⟩
      left_inv := fun d => Subtype.ext (inv_mul_cancel_left l d.1)
      right_inv := fun x => Subtype.ext (mul_inv_cancel_left l x.1) }
  have hT : Nat.card T = Nat.card D := (Nat.card_congr e).symm
  have hpT : ¬ p ∣ Nat.card T := by
    rw [hT]
    exact hD
  let act : MulAction A T :=
    { smul := fun a x => ⟨(a : G) * x.1 * (a : G)⁻¹, hstab (a : G) a.2 x⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : A) : G) * x.1 * ((1 : A) : G)⁻¹ = x.1
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a * b : A) : G) * x.1 * ((a * b : A) : G)⁻¹ =
          (a : G) * ((b : G) * x.1 * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc, mul_inv_rev]) }
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card T hpT
  rw [MulAction.mem_fixedPoints] at hx
  obtain ⟨d, hd, hxd⟩ := x.2
  refine ⟨d, hd, fun a ha => ?_⟩
  have h1 : (a : G) * x.1 * (a : G)⁻¹ = x.1 := congrArg Subtype.val (hx ⟨a, ha⟩)
  rw [hxd] at h1
  exact h1

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.CosetFixedPoint
