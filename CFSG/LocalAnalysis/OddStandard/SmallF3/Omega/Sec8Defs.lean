module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8Setting (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) : Prop
    extends Sec3SettingLB G t L, Asc82Notation t L S z where
  omega6m : IsOmega6Minus L

structure Sec8Base (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) : Prop extends Sec8Setting G t L S z where
  tz : g⁻¹ * t * g = t * z
  B_le : B ≤ L ⊓ S
  B_e16 : IsElemAb2 B 4

structure Sec8Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) : Prop extends Sec8Base G t L S z g B where
  no_i3 : ∀ s : G, s ∈ centralizer ({t} : Set G) → orderOf s = 2 →
    ∀ α : ℤˣ, ¬ InducesTypeSome L s 6 (-1) 3 α

structure Sec9Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) (t₀ : G) : Prop extends Sec8Base G t L S z g B where
  t0_inv : orderOf t₀ = 2
  t0_cent : t₀ ∈ centralizer ({t} : Set G)
  t0_type : ∃ α : ℤˣ, InducesTypeSome L t₀ 6 (-1) 3 α
  t0_B : ∀ b ∈ B, t₀ * b = b * t₀

variable {G : Type} [Group G]

@[expose] def centMod (A B : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ normalizer (B : Set G) ∧ ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B}
  one_mem' := by
    refine ⟨one_mem _, fun a _ => ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨mul_mem hx hy, fun a ha => ?_⟩
    have h1 : x * y * a * (x * y)⁻¹ * a⁻¹ =
        x * (y * a * y⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹) := by group
    rw [h1]
    refine mul_mem ?_ (hx' a ha)
    have := (Subgroup.mem_normalizer_iff.mp hx (y * a * y⁻¹ * a⁻¹)).mp (hy' a ha)
    exact this
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨inv_mem hx, fun a ha => ?_⟩
    have h1 : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [h1]
    have hxi : x⁻¹ ∈ normalizer (B : Set G) := inv_mem hx
    exact (Subgroup.mem_normalizer_iff.mp hxi _).mp (inv_mem (hx' a ha))

@[expose] def InducesOutsideGStar (L : Subgroup G) (n : ℕ) (ε : ℤˣ) (s : G) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (x : ProjSim Q),
    Module.finrank (ZMod 3) V = n ∧ quadSign Q = ε ∧
      InducesViaP L (Subgroup.center ↥L) hQ e s x ∧ x * x = 1 ∧ ¬ SimInGStar x

end CFSG.OddStandard.SmallF3.Omega
