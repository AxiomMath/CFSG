module

public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.CatalogueBUnitaryIsometry

noncomputable section

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

universe u

variable {K : Type u} [Field K]

@[expose] def Uid (sigma : K ≃+* K) (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {A | ∀ x y, herm sigma (A.val *ᵥ x) (A.val *ᵥ y) = herm sigma x y}
  one_mem' := by
    intro x y
    simp
  mul_mem' {A B} hA hB := by
    intro x y
    rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hA, hB]
  inv_mem' {A} hA := by
    intro x y
    have hx : A.val *ᵥ (A⁻¹).val *ᵥ x = x := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hy : A.val *ᵥ (A⁻¹).val *ᵥ y = y := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    exact (hA ((A⁻¹).val *ᵥ x) ((A⁻¹).val *ᵥ y)).symm.trans (congrArg₂ (herm sigma) hx hy)

theorem mem_Uid_iff (sigma : K ≃+* K) (n : ℕ) (A : GL (Fin n) K) :
    A ∈ Uid sigma n ↔ conjTr sigma A.val * A.val = 1 := by
  constructor
  · exact conjTr_mul_self_of_isometry sigma
  · intro h x y
    rw [herm_mulVec, h, one_mulVec]

theorem SUid_le_Uid (sigma : K ≃+* K) (n : ℕ) : SUid sigma n ≤ Uid sigma n := by
  intro A hA
  exact (mem_SUid_iff sigma).mp hA |>.2

@[expose] def determinant (sigma : K ≃+* K) (n : ℕ) : Uid sigma n →* Kˣ :=
  (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp (Uid sigma n).subtype

abbrev specialUnitary (sigma : K ≃+* K) (n : ℕ) : Subgroup (Uid sigma n) :=
  (determinant sigma n).ker

theorem specialUnitary_eq_subgroupOf (sigma : K ≃+* K) (n : ℕ) :
    specialUnitary sigma n = (SUid sigma n).subgroupOf (Uid sigma n) := by
  ext A
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_SUid_iff]
  change Matrix.GeneralLinearGroup.det A.val = 1 ↔
    A.val.val.det = 1 ∧ ∀ x y, herm sigma (A.val.val *ᵥ x)
      (A.val.val *ᵥ y) = herm sigma x y
  constructor
  · intro h
    exact ⟨congrArg Units.val h, A.property⟩
  · intro h
    exact Units.ext h.1

@[expose] def specialUnitaryEquivSUid (sigma : K ≃+* K) (n : ℕ) :
    specialUnitary sigma n ≃* SUid sigma n :=
  (MulEquiv.subgroupCongr (specialUnitary_eq_subgroupOf sigma n)).trans
    (Subgroup.subgroupOfEquivOfLe (SUid_le_Uid sigma n))

theorem specialUnitaryEquivSUid_val (sigma : K ≃+* K) (n : ℕ)
    (A : specialUnitary sigma n) :
    (specialUnitaryEquivSUid sigma n A).val = A.val.val := rfl

instance determinantQuotientComm (sigma : K ≃+* K) (n : ℕ) :
    IsMulCommutative (Uid sigma n ⧸ specialUnitary sigma n) := by
  let e := QuotientGroup.quotientKerEquivRange (determinant sigma n)
  exact isMulCommutative_iff.mpr (fun x y => e.injective (by
    rw [map_mul, map_mul, mul_comm]))

theorem pComponent_eq_specialUnitary [Finite K]
    (sigma : K ≃+* K) (n : ℕ)
    (hquasi : CFSG.IsQuasisimple (SUid sigma n)) (p : ℕ) (hp : p.Prime)
    (L : Subgroup (Uid sigma n)) (hL : CFSG.IsPComponent p L) :
    L = specialUnitary sigma n ∧ CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  have hkernelQuasi : CFSG.IsQuasisimple (specialUnitary sigma n) :=
    CatalogueBAlternating.quasisimple_iff_native.mpr
      (Components.quasisimple_of_equiv (specialUnitaryEquivSUid sigma n)
        (CatalogueBAlternating.quasisimple_iff_native.mp hquasi))
  obtain ⟨hle, hrestricted⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient
      p (specialUnitary sigma n) L hL
  let J := L.subgroupOf (specialUnitary sigma n)
  let : Group.IsPerfect J := CatalogueBAlternating.pComponent_perfect hrestricted
  let : Nontrivial J := CatalogueBAlternating.pComponent_nontrivial hrestricted
  have htop : J = ⊤ :=
    (Quasisimple.perfect_subnormal_eq_bot_or_eq_top
      (CatalogueBAlternating.quasisimple_iff_native.mp hkernelQuasi) J
      (Components.chain_of_mathlib_subnormal hrestricted.choose_spec.2.1)).resolve_left
        (J.nontrivial_iff_ne_bot.mp inferInstance)
  have heq : L = specialUnitary sigma n :=
    le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hkernelQuasi

end

end CFSG.ComponentClassification.CatalogueBUnitaryIsometry
