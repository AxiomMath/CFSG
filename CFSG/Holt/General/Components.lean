module

public import CFSG.Holt.General.Defs
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.LBalancePrimeCore

public section

namespace CFSG.Holt.General

open Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G]

theorem mem_zStarIn_iff {B : Subgroup G} {x : B} :
    x ∈ zStarIn B ↔ ∀ y : B, (y * x)⁻¹ * (x * y) ∈ CFSG.pPrimeCore 2 B := by
  have : (CFSG.pPrimeCore 2 B).Normal := CFSG.pPrimeCore_normal
  change QuotientGroup.mk' (CFSG.pPrimeCore 2 B) x ∈ center (B ⧸ CFSG.pPrimeCore 2 B) ↔ _
  rw [mem_center_iff, QuotientGroup.mk'_apply]
  constructor
  · intro h y
    apply QuotientGroup.eq.mp
    simpa only [QuotientGroup.mk_mul] using h (y : B ⧸ CFSG.pPrimeCore 2 B)
  · intro h q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have := QuotientGroup.eq.mpr (h y)
      simpa only [QuotientGroup.mk_mul] using this

variable [Finite G]

theorem isPGroup_center_quotient_pPrimeCore (X : Type*) [Group X] [Finite X] :
    IsPGroup 2 (center (X ⧸ CFSG.pPrimeCore 2 X)) := by
  have : (CFSG.pPrimeCore 2 X).Normal := CFSG.pPrimeCore_normal
  exact CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two)

end CFSG.Holt.General
