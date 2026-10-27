module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def scalars : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | ∃ c : Kˣ, c ^ n = 1 ∧
    (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c : K)}
  one_mem' := ⟨1, one_pow n, by simp⟩
  mul_mem' := by
    rintro A B ⟨c, hc, hA⟩ ⟨d, hd, hB⟩
    refine ⟨c * d, by rw [mul_pow, hc, hd, one_mul], ?_⟩
    rw [SpecialLinearGroup.coe_mul, hA, hB, Units.val_mul, map_mul]
  inv_mem' := by
    rintro A ⟨c, hc, hA⟩
    refine ⟨c⁻¹, by rw [inv_pow, hc, inv_one], ?_⟩
    set B : Matrix (Fin n) (Fin n) K := ((A⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) with hB
    have h1 : (A : Matrix (Fin n) (Fin n) K) * B = 1 := by
      rw [hB, ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
    calc B = scalar (Fin n) ((c⁻¹ : Kˣ) : K) * (scalar (Fin n) (c : K) * B) := by
          rw [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
            one_mul]
      _ = scalar (Fin n) ((c⁻¹ : Kˣ) : K) := by rw [← hA, h1, mul_one]

variable {n K}

theorem mem_scalars {A : SpecialLinearGroup (Fin n) K} :
    A ∈ scalars n K ↔ ∃ c : Kˣ, c ^ n = 1 ∧
      (A : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c : K) :=
  Iff.rfl

@[expose] def scalarElement (c : Kˣ) (hc : c ^ n = 1) : SpecialLinearGroup (Fin n) K :=
  ⟨scalar (Fin n) (c : K), by
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩

@[simp]
theorem coe_scalarElement (c : Kˣ) (hc : c ^ n = 1) :
    (scalarElement c hc : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c : K) :=
  rfl

theorem scalarElement_mem_scalars (c : Kˣ) (hc : c ^ n = 1) :
    scalarElement c hc ∈ scalars n K :=
  ⟨c, hc, rfl⟩

variable (n K)

theorem scalars_eq_center : scalars n K = Subgroup.center (SpecialLinearGroup (Fin n) K) := by
  ext A
  rw [mem_scalars, SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨c, hc, hA⟩
    exact ⟨c, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one], hA.symm⟩
  · rintro ⟨r, hr, hA⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨1, one_pow 0, ?_⟩
      ext i
      exact i.elim0
    · have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow hn.ne'] at hr
        exact zero_ne_one hr
      refine ⟨Units.mk0 r hr0, ?_, hA.symm⟩
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr, Units.val_one]

theorem scalars_le_center : scalars n K ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
  (scalars_eq_center n K).le

instance scalars_normal : (scalars n K).Normal :=
  Subgroup.normal_of_le_center (scalars_le_center n K)

abbrev projectiveSL : Type _ :=
  SpecialLinearGroup (Fin n) K ⧸ scalars n K

@[expose] def proj : SpecialLinearGroup (Fin n) K →* projectiveSL n K :=
  QuotientGroup.mk' (scalars n K)

theorem proj_surjective : Function.Surjective (proj n K) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem ker_proj : (proj n K).ker = scalars n K :=
  QuotientGroup.ker_mk' _

variable {n K}

theorem proj_eq_one_iff {A : SpecialLinearGroup (Fin n) K} : proj n K A = 1 ↔ A ∈ scalars n K :=
  QuotientGroup.eq_one_iff A

theorem proj_eq_proj_iff {A B : SpecialLinearGroup (Fin n) K} :
    proj n K A = proj n K B ↔ A⁻¹ * B ∈ scalars n K :=
  QuotientGroup.eq

@[expose] def elationGenerators (L : Submodule K (Fin n → K)) :
    Set (SpecialLinearGroup (Fin n) K) :=
  {A | (∀ v : Fin n → K, ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ L) ∧
    ∀ v ∈ L, ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v = 0}

theorem mem_elationGenerators {L : Submodule K (Fin n → K)} {A : SpecialLinearGroup (Fin n) K} :
    A ∈ elationGenerators L ↔ (∀ v : Fin n → K, ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v ∈ L) ∧
      ∀ v ∈ L, ((A : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v = 0 :=
  Iff.rfl

@[expose] def elationSubgroup (L : Submodule K (Fin n → K)) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  Subgroup.closure (elationGenerators L)

theorem elationGenerators_subset (L : Submodule K (Fin n → K)) :
    elationGenerators L ⊆ elationSubgroup L :=
  Subgroup.subset_closure

theorem mem_elationSubgroup_of_mem {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ elationGenerators L) :
    A ∈ elationSubgroup L :=
  Subgroup.subset_closure hA

theorem one_mem_elationGenerators (L : Submodule K (Fin n → K)) :
    (1 : SpecialLinearGroup (Fin n) K) ∈ elationGenerators L := by
  refine ⟨fun v => ?_, fun v _ => ?_⟩ <;>
    simp only [SpecialLinearGroup.coe_one, sub_self, zero_mulVec, Submodule.zero_mem]

@[expose] def projElationSubgroup (L : Submodule K (Fin n → K)) :
    Subgroup (projectiveSL n K) :=
  (elationSubgroup L).map (proj n K)

theorem mem_projElationSubgroup {L : Submodule K (Fin n → K)} {x : projectiveSL n K} :
    x ∈ projElationSubgroup L ↔ ∃ A ∈ elationSubgroup L, proj n K A = x :=
  Subgroup.mem_map

theorem proj_mem_projElationSubgroup {L : Submodule K (Fin n → K)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ elationSubgroup L) :
    proj n K A ∈ projElationSubgroup L :=
  Subgroup.mem_map_of_mem _ hA

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
