module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section MatLift

variable {K M : Type} [Group K] [Monoid M] {X : Type} [Group X]
  (ρ : K →* M) (μ : X →* M)

@[expose] def liftImage : Subgroup K where
  carrier := {t | ∃ x, μ x = ρ t}
  mul_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [map_mul, map_mul, hx, hy]⟩
  one_mem' := ⟨1, by rw [map_one, map_one]⟩
  inv_mem' := by
    rintro a ⟨x, hx⟩
    refine ⟨x⁻¹, ?_⟩
    have h1 : μ x⁻¹ * μ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    calc μ x⁻¹ = μ x⁻¹ * (ρ a * ρ a⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = (μ x⁻¹ * μ x) * ρ a⁻¹ := by rw [hx, mul_assoc]
      _ = ρ a⁻¹ := by rw [h1, one_mul]

variable (L : Subgroup K) (hρ : Function.Injective ρ) (E1 : ∀ x, ∃ t ∈ L, ρ t = μ x)

@[expose] noncomputable def matLiftFun (x : X) : K := Classical.choose (E1 x)

theorem matLiftFun_mem (x : X) : matLiftFun ρ μ L E1 x ∈ L := (Classical.choose_spec (E1 x)).1

theorem rho_matLiftFun (x : X) : ρ (matLiftFun ρ μ L E1 x) = μ x := (Classical.choose_spec (E1 x)).2

include hρ in
theorem matLiftFun_eq (x : X) (t : K) (ht : ρ t = μ x) : matLiftFun ρ μ L E1 x = t :=
  hρ ((rho_matLiftFun ρ μ L E1 x).trans ht.symm)

@[expose] noncomputable def matLiftHom : X →* ↥L where
  toFun x := ⟨matLiftFun ρ μ L E1 x, matLiftFun_mem ρ μ L E1 x⟩
  map_one' := Subtype.ext (matLiftFun_eq ρ μ L hρ E1 1 1 (by rw [map_one, map_one]))
  map_mul' x y := Subtype.ext (matLiftFun_eq ρ μ L hρ E1 (x * y)
    (matLiftFun ρ μ L E1 x * matLiftFun ρ μ L E1 y) (by
      rw [map_mul, map_mul, rho_matLiftFun, rho_matLiftFun]))

theorem rho_matLiftHom (x : X) : ρ (matLiftHom ρ μ L hρ E1 x : K) = μ x := rho_matLiftFun ρ μ L E1 x

theorem matLiftHom_injective (hμ : Function.Injective μ) :
    Function.Injective (matLiftHom ρ μ L hρ E1) := by
  intro x y h
  apply hμ
  rw [← rho_matLiftHom ρ μ L hρ E1 x, ← rho_matLiftHom ρ μ L hρ E1 y, h]

theorem matLiftHom_surjective (E2 : L ≤ liftImage ρ μ) :
    Function.Surjective (matLiftHom ρ μ L hρ E1) := by
  intro t
  obtain ⟨x, hx⟩ := E2 t.2
  refine ⟨x, Subtype.ext ?_⟩
  exact hρ ((rho_matLiftHom ρ μ L hρ E1 x).trans hx)

@[expose] noncomputable def matLiftEquiv (hμ : Function.Injective μ) (E2 : L ≤ liftImage ρ μ) :
    X ≃* ↥L :=
  MulEquiv.ofBijective (matLiftHom ρ μ L hρ E1)
    ⟨matLiftHom_injective ρ μ L hρ E1 hμ, matLiftHom_surjective ρ μ L hρ E1 E2⟩

end MatLift

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
