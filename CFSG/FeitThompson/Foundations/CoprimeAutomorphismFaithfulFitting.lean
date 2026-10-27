module

public import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
import CFSG.FeitThompson.Foundations.SolvableExtensionNormalQuotient
import CFSG.FeitThompson.Foundations.AbelianSolvable

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open SemidirectProduct Subgroup

variable {G A : Type*} [Group G] [Group A]

instance instIsSolvableSemidirectProduct {φ : A →* MulAut G} [Group.IsSolvable G]
    [Group.IsSolvable A] : Group.IsSolvable (G ⋊[φ] A) := by
  have : Group.IsSolvable ((rightHom : G ⋊[φ] A →* A).ker) := by
    rw [← range_inl_eq_ker_rightHom]
    exact Group.isSolvable_of_surjective (inl : G →* G ⋊[φ] A).rangeRestrict_surjective
  have : Group.IsSolvable ((G ⋊[φ] A) ⧸ (rightHom : G ⋊[φ] A →* A).ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivOfSurjective (rightHom : G ⋊[φ] A →* A)
        rightHom_surjective).toMonoidHom) (MulEquiv.injective _)
  exact isSolvable_of_normal_of_quotient (rightHom : G ⋊[φ] A →* A).ker

theorem eq_one_of_fixes_fittingRaw [Finite G] [Finite A] [Group.IsSolvable G]
    (ρ : A →* MulAut G) (hρ : Function.Injective ρ)
    (hcop : (Nat.card A).Coprime (Nat.card G)) {a : A}
    (ha : ∀ x ∈ fittingRaw G, ρ a x = x) : a = 1 := by
  set B := Subgroup.zpowers a with hBdef
  have : Group.IsSolvable B := isSolvable_of_isMulCommutative
  set φ : B →* MulAut G := ρ.comp B.subtype with hφdef
  have hφinj : Function.Injective φ := hρ.comp Subtype.val_injective
  have hcopB : (Nat.card G).Coprime (Nat.card B) :=
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B) hcop).symm
  set b : B := ⟨a, Subgroup.mem_zpowers a⟩ with hbdef
  have hmem : (inr b : G ⋊[φ] B) ∈ Subgroup.centralizer (fittingRaw (G ⋊[φ] B) : Set _) := by
    rw [fittingRaw_semidirectProduct_eq_map_inl hcopB hφinj, Subgroup.mem_centralizer_iff]
    rintro y hy
    obtain ⟨g, hg, rfl⟩ := hy
    have h2 : φ b g = g := ha g hg
    have h1 : (inl (φ b g) : G ⋊[φ] B) = inr b * inl g * inr b⁻¹ := inl_aut b g
    rw [h2] at h1
    calc (inl g : G ⋊[φ] B) * inr b = (inr b * inl g * inr b⁻¹) * inr b := by rw [← h1]
      _ = inr b * inl g := by simp [mul_assoc]
  have h3 : (inr b : G ⋊[φ] B) ∈ (inl : G →* G ⋊[φ] B).range :=
    fittingRaw_semidirectProduct_le_range_inl hcopB hφinj
      (centralizer_fittingRaw_le_fittingRaw (G ⋊[φ] B) hmem)
  rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker, rightHom_inr] at h3
  exact congrArg Subtype.val h3

theorem map_eq_one_of_fixes_fittingRaw [Finite G] [Finite A] [Group.IsSolvable G]
    (ρ : A →* MulAut G) (hρ : Function.Injective ρ)
    (hcop : (Nat.card A).Coprime (Nat.card G)) {a : A}
    (ha : ∀ x ∈ fittingRaw G, ρ a x = x) : ρ a = 1 := by
  rw [eq_one_of_fixes_fittingRaw ρ hρ hcop ha, map_one]

theorem injective_characteristic_comp_of_coprime [Finite G] [Finite A] [Group.IsSolvable G]
    (ρ : A →* MulAut G) (hρ : Function.Injective ρ)
    (hcop : (Nat.card A).Coprime (Nat.card G)) :
    Function.Injective ((MulAut.characteristic (fittingRaw G)).comp ρ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine eq_one_of_fixes_fittingRaw ρ hρ hcop fun x hx => ?_
  have h := congrArg (fun e : MulAut (fittingRaw G) => (e ⟨x, hx⟩ : G)) ha
  simpa [MulAut.characteristic_apply_apply_coe] using h

end

end CFSG.FeitThompson
