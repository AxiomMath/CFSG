module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] abbrev E16 : Type := Fin 4 → Multiplicative (ZMod 2)

@[expose] abbrev Z4Pow4 : Type := Fin 4 → Multiplicative (ZMod 4)

structure Sec7Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) : Prop
    extends Sec3SettingLB G t L, Asc82Notation t L S z where
  omega6 : IsOmega6Plus L

variable {G : Type} [Group G]

@[expose] def ASub (S B : Subgroup G) : Subgroup G :=
  omega1 (S ⊓ centralizer (B : Set G))

@[expose] def MSub (S B : Subgroup G) : Subgroup G :=
  normalizer ((ASub S B : Subgroup G) : Set G)

structure Sec7Choice (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) : Prop where
  ctx : Sec7Ctx G t L S z
  normalE16 : IsNormalE16In (S ⊓ L) B
  s_mem : g⁻¹ * t * g ∈ S
  s_ne : g⁻¹ * t * g ≠ t
  choice : g⁻¹ * t * g = t * z ∨
    (¬ IsConj t (t * z) ∧ g⁻¹ * t * g ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ∧
      (∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 1 α) ∧
      ∃ n ∈ L ⊓ normalizer (B : Set G), g⁻¹ * t * g * n ≠ n * (g⁻¹ * t * g))

end CFSG.OddStandard.SmallF3.Omega
