module

public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mul_eq_of_not_inv {U : Subgroup G} {z s : G} (hU2 : IsPGroup 2 U)
    (hz : IsUniqueInvolution U z) (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hsU : ∀ u ∈ U, s * u * s⁻¹ ∈ U) (hninv : ¬ ∀ u ∈ U, s * u * s⁻¹ = u⁻¹) :
    ∃ u ∈ U, s * u * s⁻¹ * u = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N₁ : ↥U →* ↥U :=
    { toFun := fun u => ⟨s * u * s⁻¹ * u, U.mul_mem (hsU u u.2) u.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        simp only [Subgroup.coe_mul]
        have h1 := hab _ (hsU y y.2) _ x.2
        calc s * (↑x * ↑y) * s⁻¹ * (↑x * ↑y)
            = (s * ↑x * s⁻¹) * ((s * ↑y * s⁻¹) * ↑x) * ↑y := by group
          _ = (s * ↑x * s⁻¹) * (↑x * (s * ↑y * s⁻¹)) * ↑y := by rw [h1]
          _ = s * ↑x * s⁻¹ * ↑x * (s * ↑y * s⁻¹ * ↑y) := by group }
  have hne : N₁.range ≠ ⊥ := by
    intro h
    apply hninv
    intro u hu
    have h1 : N₁ ⟨u, hu⟩ = 1 := by
      have : N₁ ⟨u, hu⟩ ∈ N₁.range := ⟨⟨u, hu⟩, rfl⟩
      rw [h] at this
      exact this
    have h2 : s * u * s⁻¹ * u = 1 := congrArg Subtype.val h1
    calc s * u * s⁻¹ = s * u * s⁻¹ * u * u⁻¹ := by group
      _ = u⁻¹ := by rw [h2, one_mul]
  have hR2 : IsPGroup 2 ↥N₁.range := hU2.to_subgroup N₁.range
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁.range) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  obtain ⟨u, hu⟩ := x.2
  have hx2 : ((x : ↥U) : G) * ((x : ↥U) : G) = 1 := by
    have h1 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
    have h2 := congrArg (fun y : ↥N₁.range => ((y : ↥U) : G)) h1
    simpa [_root_.sq] using h2
  have hx1 : ((x : ↥U) : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hx
    omega
  have hxz := (hz.unique _ (x : ↥U).2 hx2).resolve_left hx1
  refine ⟨u, u.2, ?_⟩
  rw [← hxz, ← hu]
  rfl

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
