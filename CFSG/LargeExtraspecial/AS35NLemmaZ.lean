module

public import CFSG.LargeExtraspecial.AS35NBasic
public import CFSG.LargeExtraspecial.AS35KFisE
public import CFSG.LargeExtraspecial.AS35NModelA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem coe_conj_mem_BSet (hS : S.SixHyp)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet)
    (hQX : S.QG ≤ S.BStab) (hMX : ∀ m ∈ S.M, ∀ y ∈ S.BStab, m * y * m⁻¹ ∈ S.BStab)
    (l : S.BStab) :
    ((l * (S.restrict S.BStab hQX hMX).z * l⁻¹ : S.BStab) : G) ∈ S.BSet := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_restrict_z]
  exact (S.mem_BStab_iff_of hS h69).mp l.2

theorem exists_unitary_model_BStab
    (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet)
    (h610 : ∀ a ∈ S.BSet, ∀ b ∈ S.BSet, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ))
    (hQX : S.QG ≤ S.BStab) (hMX : ∀ m ∈ S.M, ∀ y ∈ S.BStab, m * y * m⁻¹ ∈ S.BStab)
    (hA2 : (S.restrict S.BStab hQX hMX).AschTwo) :
    ∃ m : ℕ, 6 ≤ m ∧ ∃ ψ : (S.restrict S.BStab hQX hMX).zGen ≃* PG m,
      (∀ l, IsConj (S.restrict S.BStab hQX hMX).zL l ↔ ψ l ∈ DG m) ∧
      centralizer ((S.restrict S.BStab hQX hMX).zGen : Set S.BStab) = ⊥ := by
  set T := S.restrict S.BStab hQX hMX with hT
  have hw : T.width = S.width := S.restrict_width _ hQX hMX
  have h4 := h65.four_le_width
  obtain ⟨hs, hC, -⟩ := hA2
  have h3 : ∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ) := by
    intro l₁ _ l₂ _
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact h610 _ (S.coe_conj_mem_BSet hS h69 hQX hMX l₁) _ (S.coe_conj_mem_BSet hS h69 hQX hMX l₂)
  obtain ⟨m, hm, ψ, hψ⟩ := S14.aschTwoUnitaryModelStmt_of_spRefl
    (S14.aschTwoSpReflStmt_of_reflSix S14.aschTwoReflSixStmt) S.BStab T (by omega) hs hC h3
  obtain ⟨e, he0, he, hez⟩ := (hψ T.zL).mp (IsConj.refl _)
  obtain ⟨-, hwm⟩ := T.QG_eq_map_Rbar hm hC ψ he0 he hez
  exact ⟨m, by omega, ψ, hψ, hC⟩

end Setting

end CFSG.LargeExtraspecial

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem mem_BSet_of_isConj_zL (hS : S.SixHyp)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet)
    (hQX : S.QG ≤ S.BStab) (hMX : ∀ m ∈ S.M, ∀ y ∈ S.BStab, m * y * m⁻¹ ∈ S.BStab)
    {l : (S.restrict S.BStab hQX hMX).zGen} (hl : IsConj (S.restrict S.BStab hQX hMX).zL l) :
    (((l : S.BStab)) : G) ∈ S.BSet := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hl
  have h1 := S.coe_conj_mem_BSet hS h69 hQX hMX (c : S.BStab)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_zL] using h1

end Setting

end CFSG.LargeExtraspecial
