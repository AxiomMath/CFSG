module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.GH74.Generic.S45

open CFSG.LieType.Steinberg Subgroup
open scoped commutatorElement

theorem exists_equivariant_cover {K S P : Type} [Group K] [Group S] [Group P] [Finite K] [Finite P]
    (hKp : Group.IsPerfect K) (hPp : Group.IsPerfect P)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* P), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker → ∃ σ : P →* E, ∀ x, π (σ x) = x)
    {η : K →* S} (hη : Function.Surjective η) (hηc : η.ker ≤ Subgroup.center K)
    (hη2 : IsPGroup 2 η.ker) {β : P →* S} (hβ : Function.Surjective β)
    {y : MulAut K} {yb : MulAut S} (hy : ∀ k, η (y k) = yb (η k))
    {τ : MulAut P} (hτ : ∀ g, β (τ g) = yb (β g)) :
    ∃ α : P →* K, (∀ g, η (α g) = β g) ∧ Function.Surjective α ∧ ∀ g, y (α g) = α (τ g) := by
  have := hKp
  obtain ⟨α, hα, hαs, -⟩ := exists_surjective_of_isPerfect hsplit hβ hη hηc hη2
  refine ⟨α, hα, hαs, ?_⟩
  let f₁ : P →* K := y.toMonoidHom.comp α
  let f₂ : P →* K := α.comp τ.toMonoidHom
  have hz : ∀ g : P, f₁ g * (f₂ g)⁻¹ ∈ Subgroup.center K := fun g => by
    apply hηc
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have h1 : η (f₁ g) = yb (β g) := by
      change η (y (α g)) = _
      rw [hy, hα]
    have h2 : η (f₂ g) = yb (β g) := by
      change η (α (τ g)) = _
      rw [hα, hτ]
    rw [h1, h2, mul_inv_cancel]
  have hcomm : ∀ a b : P, f₁ ⁅a, b⁆ = f₂ ⁅a, b⁆ := fun a b => by
    have ha : f₁ a = (f₁ a * (f₂ a)⁻¹) * f₂ a := by rw [inv_mul_cancel_right]
    have hb : f₁ b = (f₁ b * (f₂ b)⁻¹) * f₂ b := by rw [inv_mul_cancel_right]
    rw [map_commutatorElement, map_commutatorElement, ha, hb,
      commutatorElement_mul_mul_of_mem_center (hz a) (hz b)]
  have hle : commutator P ≤ f₁.eqLocus f₂ := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  intro g
  exact hle (by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top g)

theorem exists_fixed_dvd_of_cover {K S P : Type} [Group K] [Group S] [Group P] [Finite K] [Finite P]
    (hKp : Group.IsPerfect K) (hPp : Group.IsPerfect P)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* P), Function.Surjective π →
      π.ker ≤ Subgroup.center E → IsPGroup 2 π.ker → ∃ σ : P →* E, ∀ x, π (σ x) = x)
    {η : K →* S} (hη : Function.Surjective η) (hηc : η.ker ≤ Subgroup.center K)
    (hη2 : IsPGroup 2 η.ker) {β : P →* S} (hβ : Function.Surjective β)
    {y : MulAut K} {yb : MulAut S} (hy : ∀ k, η (y k) = yb (η k))
    {τ : MulAut P} (hτ : ∀ g, β (τ g) = yb (β g)) {c : P} (hc : τ c = c)
    (h4 : 4 ∣ orderOf (β c)) : ∃ x : K, y x = x ∧ 4 ∣ orderOf x := by
  obtain ⟨α, hα, -, hαy⟩ := exists_equivariant_cover hKp hPp hsplit hη hηc hη2 hβ hy hτ
  refine ⟨α c, by rw [hαy, hc], ?_⟩
  have h1 : orderOf (η (α c)) ∣ orderOf (α c) := orderOf_map_dvd η (α c)
  rw [hα] at h1
  exact h4.trans h1

end CFSG.GH74.Generic.S45
