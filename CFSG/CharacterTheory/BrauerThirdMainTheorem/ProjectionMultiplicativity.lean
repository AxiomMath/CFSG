module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Convolution

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem brauerProj_convolution_fixed {G : Type*} [Group G] [Finite G]
    (subgroup overgroup : Subgroup G)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (left right : G → ℂ) (element : overgroup)
    (helement : element.val ∈ Subgroup.centralizer (subgroup : Set G)) :
    coefficientConvolution (BlocksBrauerProj subgroup overgroup left)
      (BlocksBrauerProj subgroup overgroup right) element =
      ∑ᶠ factor : G, (Subgroup.centralizer (subgroup : Set G) : Set G).indicator
        (fun factor => left factor * right (factor⁻¹ * element.val)) factor := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype overgroup := Fintype.ofFinite _
  rw [coefficientConvolution_apply, finsum_eq_sum_of_fintype]
  have hproduct (factor : overgroup) :
      BlocksBrauerProj subgroup overgroup left factor *
        BlocksBrauerProj subgroup overgroup right (factor⁻¹ * element) =
      if factor.val ∈ Subgroup.centralizer (subgroup : Set G) then
        left factor.val * right (factor.val⁻¹ * element.val) else 0 := by
    rw [brauerProj_apply, brauerProj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    by_cases hfactor : factor.val ∈ Subgroup.centralizer (subgroup : Set G)
    · have hother := (Subgroup.centralizer (subgroup : Set G)).mul_mem
        ((Subgroup.centralizer (subgroup : Set G)).inv_mem hfactor) helement
      simp only [hfactor, hother, ↓reduceIte]
    · simp only [hfactor, ↓reduceIte, zero_mul]
  rw [Finset.sum_congr rfl (fun factor _ => hproduct factor)]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun factor _ => factor.val)
  · intro factor hfactor
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hfactor).2⟩
  · intro left _ right _ hequal
    exact Subtype.ext hequal
  · intro factor hfactor
    have hmember := (Finset.mem_filter.mp hfactor).2
    exact ⟨⟨factor, hcentralizer hmember⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmember⟩, rfl⟩
  · intro _ _
    rfl

theorem brauerProj_convolution_nonfixed {G : Type*} [Group G] [Finite G]
    (subgroup overgroup : Subgroup G) (left right : G → ℂ) (element : overgroup)
    (helement : element.val ∉ Subgroup.centralizer (subgroup : Set G)) :
    coefficientConvolution (BlocksBrauerProj subgroup overgroup left)
      (BlocksBrauerProj subgroup overgroup right) element = 0 := by
  classical
  let : Fintype overgroup := Fintype.ofFinite _
  rw [coefficientConvolution_apply]
  apply Finset.sum_eq_zero
  intro factor _
  rw [brauerProj_apply, brauerProj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  by_cases hfactor : factor.val ∈ Subgroup.centralizer (subgroup : Set G)
  · have hother : factor.val⁻¹ * element.val ∉ Subgroup.centralizer (subgroup : Set G) := by
      intro hother
      have hproduct := (Subgroup.centralizer (subgroup : Set G)).mul_mem hfactor hother
      rw [mul_inv_cancel_left] at hproduct
      exact helement hproduct
    simp only [hfactor, hother, ↓reduceIte, mul_zero]
  · simp only [hfactor, ↓reduceIte, zero_mul]

theorem brauerProj_convolution_congr {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (prime : ℕ) (hprime : prime.Prime)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (subgroup overgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    {left right : G → ℂ} (hleft : BlocksIsCentralR m left) (hright : BlocksIsCentralR m right)
    (element : overgroup) :
    BlocksBrauerProj subgroup overgroup (coefficientConvolution left right) element -
      coefficientConvolution (BlocksBrauerProj subgroup overgroup left)
        (BlocksBrauerProj subgroup overgroup right) element ∈ BlocksLocalMaxIdeal m := by
  classical
  by_cases helement : element.val ∈ Subgroup.centralizer (subgroup : Set G)
  · rw [brauerProj_apply, ite_eq_left helement,
      brauerProj_convolution_fixed subgroup overgroup hcentralizer left right element helement]
    let : MulAction subgroup G := {
      smul member factor := member.val * factor * member.val⁻¹
      one_smul factor := by
        change (1 : G) * factor * (1 : G)⁻¹ = factor
        group
      mul_smul left right factor := by
        change (left.val * right.val) * factor * (left.val * right.val)⁻¹ =
          left.val * (right.val * factor * right.val⁻¹) * left.val⁻¹
        group
    }
    have hfixed : MulAction.fixedPoints subgroup G =
        (Subgroup.centralizer (subgroup : Set G) : Set G) := by
      ext factor
      rw [MulAction.mem_fixedPoints]
      change (∀ member : subgroup, member • factor = factor) ↔
        factor ∈ Subgroup.centralizer (subgroup : Set G)
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hmember member hmemberSubgroup
        have hequal := hmember ⟨member, hmemberSubgroup⟩
        change member * factor * member⁻¹ = factor at hequal
        exact (mul_inv_eq_iff_eq_mul).mp hequal
      · intro hmember member
        change member.val * factor * member.val⁻¹ = factor
        rw [hmember member.val member.property, mul_inv_cancel_right]
    rw [← hfixed]
    apply invariant_sum_congr_fixed m hm prime hprime hprimeMem hpGroup
    · intro factor
      exact localRing_mul m hm (hleft.1 factor) (hright.1 (factor⁻¹ * element.val))
    · intro member factor
      change left (member.val * factor * member.val⁻¹) *
        right ((member.val * factor * member.val⁻¹)⁻¹ * element.val) =
        left factor * right (factor⁻¹ * element.val)
      rw [hleft.2]
      have helementFixed : member.val * element.val * member.val⁻¹ = element.val := by
        rw [(Subgroup.mem_centralizer_iff.mp helement) member.val member.property,
          mul_inv_cancel_right]
      have hfactor : (member.val * factor * member.val⁻¹)⁻¹ * element.val =
          member.val * (factor⁻¹ * element.val) * member.val⁻¹ := by
        conv_lhs => rhs; rw [← helementFixed]
        group
      rw [hfactor, hright.2]
  · rw [brauerProj_apply, ite_eq_right helement,
      brauerProj_convolution_nonfixed subgroup overgroup left right element helement, sub_self]
    exact localMaxIdeal_zero m hm

end CFSG.BrauerThirdMainTheorem.Helpers
