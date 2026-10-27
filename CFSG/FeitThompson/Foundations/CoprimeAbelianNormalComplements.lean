module

public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.CorrectingSectionToHom
import CFSG.FeitThompson.Foundations.AveragingFactorSetCoboundary
import CFSG.FeitThompson.Foundations.SectionNormalizedFactorSet
import Mathlib.Data.Rat.Floor

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

open scoped IsMulCommutative

section Existence

variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal]

theorem coprime_natCard_quotient_additive (A : Subgroup G) [A.Normal]
    (h : (Nat.card ↥A).Coprime A.index) :
    (Nat.card (G ⧸ A)).Coprime (Nat.card (Additive ↥A)) := by
  rw [← A.index_eq_card, Nat.card_congr (Additive.toMul (α := ↥A))]
  exact h.symm

variable [IsMulCommutative ↥A]

theorem exists_monoidHom_section_of_coprime_index [Finite (G ⧸ A)]
    (h : (Nat.card ↥A).Coprime A.index) :
    ∃ t : (G ⧸ A) →* G, ∀ x, ((t x : G) : G ⧸ A) = x := by
  have : Fintype (G ⧸ A) := Fintype.ofFinite _
  have h' : (Nat.card (G ⧸ A)).Coprime (Nat.card (Additive ↥A)) :=
    coprime_natCard_quotient_additive A h
  set s := normalizedSection A with hsdef
  have hs : ∀ x, ((s x : G) : G ⧸ A) = x := mk_normalizedSection A
  have hb : ∀ x y, s x * s y * (s (x * y))⁻¹ =
      (((factorSetAverage h' (sectionFactorSet hs) x
        + x • factorSetAverage h' (sectionFactorSet hs) y
        - factorSetAverage h' (sectionFactorSet hs) (x * y)).toMul : ↥A) : G) := fun x y => by
    rw [← coe_toMul_sectionFactorSet hs x y,
      factorSetAverage_coboundary h' (sectionFactorSet_cocycle hs) x y]
  exact ⟨correctedSectionHom hs hb, mk_correctedSectionHom hs hb⟩

omit [IsMulCommutative ↥A] in
theorem isComplement'_range_of_monoidHom_section {t : (G ⧸ A) →* G}
    (ht : ∀ x, ((t x : G) : G ⧸ A) = x) : A.IsComplement' t.range := by
  have h := isComplement_range_of_section ht
  rwa [Subgroup.IsComplement', MonoidHom.coe_range]

theorem exists_isComplement'_of_coprime_index [Finite (G ⧸ A)]
    (h : (Nat.card ↥A).Coprime A.index) : ∃ H : Subgroup G, A.IsComplement' H := by
  obtain ⟨t, ht⟩ := exists_monoidHom_section_of_coprime_index h
  exact ⟨t.range, isComplement'_range_of_monoidHom_section ht⟩

theorem exists_mul_coe_eq_univ_and_inf_eq_bot [Finite (G ⧸ A)]
    (h : (Nat.card ↥A).Coprime A.index) :
    ∃ H : Subgroup G, (A : Set G) * (H : Set G) = Set.univ ∧ A ⊓ H = ⊥ := by
  obtain ⟨H, hH⟩ := exists_isComplement'_of_coprime_index h
  exact ⟨H, hH.mul_eq, disjoint_iff.mp hH.disjoint⟩

end Existence

section Quotient

variable {G : Type*} [Group G] {A H : Subgroup G} [A.Normal]

omit [A.Normal] in
theorem mul_coe_eq_univ_and_inf_eq_bot_of_isComplement' (h : A.IsComplement' H) :
    (A : Set G) * (H : Set G) = Set.univ ∧ A ⊓ H = ⊥ :=
  ⟨h.mul_eq, disjoint_iff.mp h.disjoint⟩

noncomputable def complementMulEquivQuotient (h : A.IsComplement' H) : ↥H ≃* G ⧸ A :=
  MulEquiv.ofBijective ((QuotientGroup.mk' A).comp H.subtype)
    (Subgroup.isComplement_subgroup_right_iff_bijective.mp h.symm)

@[simp]
theorem complementMulEquivQuotient_apply (h : A.IsComplement' H) (x : ↥H) :
    complementMulEquivQuotient h x = ((x : G) : G ⧸ A) := (rfl)

@[simp] theorem coe_complementMulEquivQuotient_symm (h : A.IsComplement' H) (x : G ⧸ A) :
    (((complementMulEquivQuotient h).symm x : ↥H) : G ⧸ A) = x := by
  rw [← complementMulEquivQuotient_apply h, MulEquiv.apply_symm_apply]

theorem complementMulEquivQuotient_symm_apply_mem (h : A.IsComplement' H) (g : G) :
    ((complementMulEquivQuotient h).symm (g : G ⧸ A) : G) ∈ H :=
  ((complementMulEquivQuotient h).symm (g : G ⧸ A)).2

end Quotient

end CFSG.FeitThompson
