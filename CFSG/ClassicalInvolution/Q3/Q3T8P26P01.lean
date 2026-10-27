module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZA3
public import CFSG.ClassicalInvolution.Q3.Q3EXD4FModel
public import CFSG.ClassicalInvolution.Asc77.AscMuTabD4

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8ZZ

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.TG3
open CFSG.ClassicalInvolution.Asc77.T8ZZ
open CFSG.ClassicalInvolution.Q3.Q3W.EX

local notation "𝔽₃" => GaloisField 3 1


theorem invOf_central (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) {ζ : spinGroup (quadPlus 4 𝔽₃)} (hζ : InvOf R ζ) :
    (∀ r ∈ R, ζ * r = r * ζ) ∧ ζ ≠ 1 := by
  obtain ⟨hζR, hord⟩ := hζ
  have hne : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    omega
  have hsq : ζ * ζ = 1 := by
    rw [← pow_two]
    exact hord ▸ pow_orderOf_eq_one ζ
  obtain ⟨e⟩ := hF.sl2 R hR
  have h1 : e ⟨ζ, hζR⟩ * e ⟨ζ, hζR⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hsq
  rcases Generic.sl2_sq_eq_one two_ne_zero_three h1 with h | h
  · exfalso
    have : (⟨ζ, hζR⟩ : R) = 1 := e.injective (by rw [h, map_one])
    exact hne (congrArg Subtype.val this)
  · have hc : (⟨ζ, hζR⟩ : R) ∈ Subgroup.center R :=
      (CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mpr
        (by rw [h]; exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mpr (Or.inr rfl))
    refine ⟨fun r hr => ?_, hne⟩
    have := Subgroup.mem_center_iff.mp hc ⟨r, hr⟩
    exact (congrArg Subtype.val this).symm

theorem plusModelFacts : PlusModelFacts 3 1 := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have e := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_refl 4⟩
  have hsc : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Nat.prime_three trivial hadm (by decide)
      (by decide)
  have hsc' : FundamentalSingleClass .POmegaPlus (plusDatum 4 𝔽₃ hn3) := by
    revert hsc
    rw [e]
    exact id
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := 𝔽₃) hn3 (le_refl 4)
  refine ⟨?_, perfectK_of_admissible Nat.prime_three trivial hadm, ?_, ?_, ?_⟩
  · rw [e]
    exact ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  · rw [e]
    exact plus_card_center_le
  · rw [e]
    exact central_of_stdPair (p := 3) (f := 1)
      (Y := ⟨spinGroup (quadPlus 4 𝔽₃), plusDatum 4 𝔽₃ hn3⟩) hsc'
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (⟨0, by show 0 < 4; omega⟩ : Fin 4)) hW₁
  · rw [e]
    intro R₁ h₁ R₂ h₂ hc ζ₁ ζ₂ hζ₁ hζ₂
    have hF := D4Facts3.of_gf3
    obtain ⟨hz₁, hn₁⟩ := invOf_central hF h₁ hζ₁
    obtain ⟨hz₂, hn₂⟩ := invOf_central hF h₂ hζ₂
    exact hF.fund_pair_mul_central h₁ h₂ hc hζ₁.1 hζ₂.1 hz₁ hz₂ hn₁ hn₂

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8ZZ
