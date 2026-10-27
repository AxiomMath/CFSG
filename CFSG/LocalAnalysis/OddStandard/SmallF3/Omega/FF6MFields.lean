module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MSylowE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MAutB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MCentB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MOuterSwaps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure FF6MSylow : Prop where
  sylow_E16 : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∃ B₁ B₂ : Subgroup G, B₁ ≠ B₂ ∧ IsNormalE16In P B₁ ∧
      IsNormalE16In P B₂ ∧ ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 → B = B₁ ∨ B = B₂
  aut_B : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) ∧
        (∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 → ∃ n ∈ L ⊓ normalizer (B : Set G), n * b * n⁻¹ = b') ∧
        L ⊓ centralizer (B : Set G) = B ⊔ centerIn L
  cent_B : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
      ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
        (∃ b ∈ B, x * b⁻¹ ∈ centralizer (L : Set G)) ∨
          (∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 1 α) ∨ ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α
  outer_swaps : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → InducesOutsideGStar L 6 (-1) s →
      ∀ U : Subgroup G, U ≤ L → IsElemAb2 U 4 → s ∉ normalizer (U : Set G)

theorem ffTab6MSylow_holds : FF6MSylow where
  sylow_E16 := ff6m_sylow_E16
  aut_B := ff6m_aut_B
  cent_B := ff6m_cent_B
  outer_swaps := fun G _ _ L h s _ hsN hout U hUL hU =>
    ff6m_outer_swaps G L h s hsN hout U hUL hU

theorem asc82Tab6M_holds : Asc82Tab6M where
  layer_trivial := ffTab6MClass_holds.layer_trivial
  layer_i4m := ffTab6MClass_holds.layer_i4m
  layer_rho := ffTab6MClass_holds.layer_rho
  layer_i1 := ffTab6MClass_holds.layer_i1
  layer_gamma := ffTab6MClass_holds.layer_gamma
  inner_iff := ffTab6MClass_holds.inner_iff
  out_two := ffTab6MClass_holds.out_two
  inv_one_class := ffTab6MClass_holds.inv_one_class
  ex_u_outer := ffTab6MClass_holds.ex_u_outer
  sylow_E16 := ffTab6MSylow_holds.sylow_E16
  aut_B := ffTab6MSylow_holds.aut_B
  cent_B := ffTab6MSylow_holds.cent_B
  outer_swaps := ffTab6MSylow_holds.outer_swaps
  classify := ffTab6MClass_holds.classify
  nontrivial := ffTab6MClass_holds.nontrivial
  xout_eq := ffTab6MClass_holds.xout_eq
  xout_i3 := ffTab6MClass_holds.xout_i3

end CFSG.OddStandard.SmallF3.Omega
