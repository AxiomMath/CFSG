module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K]

theorem mul_similitude {r ε : ℕ} (h : UnitaryFieldData p f K)
    {A B : Matrix (HypIndex r ε) (HypIndex r ε) K} {μ ν : K}
    (hA : (A.map h.bar)ᵀ * hypGram r ε K * A = μ • hypGram r ε K)
    (hB : (B.map h.bar)ᵀ * hypGram r ε K * B = ν • hypGram r ε K) :
    ((A * B).map h.bar)ᵀ * hypGram r ε K * (A * B) = (μ * ν) • hypGram r ε K := by
  rw [conjTranspose_mul_mul, hA, Matrix.mul_smul, Matrix.smul_mul, hB, smul_smul]

theorem fieldAut_mul_comm (h : UnitaryFieldData p f K) (σ τ : K ≃+* K) : σ * τ = τ * σ := by
  have := h.finite
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  exact IsCyclic.commGroup.mul_comm σ τ

theorem eq_inl_of_right_eq_one {r ε : ℕ} {x : SemiGL (HypIndex r ε) K} (hx : x.right = 1) :
    x = SemidirectProduct.inl x.left :=
  SemidirectProduct.ext (SemidirectProduct.left_inl _).symm
    (by rw [SemidirectProduct.right_inl, hx])

variable {h : UnitaryFieldData p f K} {r ε : ℕ}

theorem commutator_mem_map_inl {x y : SemiGL (HypIndex r ε) K}
    (hx : x ∈ semilinearSimilitudes h r ε) (hy : y ∈ semilinearSimilitudes h r ε)
    (hx1 : x.right = 1) (hy1 : y.right = 1) :
    ⁅x, y⁆ ∈ (hypSU h r ε).map SemidirectProduct.inl := by
  obtain ⟨μ, hμ0, -, hA⟩ := hx
  obtain ⟨ν, hν0, -, hB⟩ := hy
  rw [eq_inl_of_right_eq_one hx1, eq_inl_of_right_eq_one hy1, ← map_commutatorElement]
  refine ⟨_, mem_gramSU.mpr ⟨?_, ?_⟩, rfl⟩
  · have hAA : ((x.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((x.left⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBB : ((y.left : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((y.left⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hC := mul_similitude h (mul_similitude h (mul_similitude h hA hB)
      (inv_similitude h hμ0 hA hAA)) (inv_similitude h hν0 hB hBB)
    have hμν : μ * ν * μ⁻¹ * ν⁻¹ = 1 := by field_simp
    rw [hμν, one_smul] at hC
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
    exact hC
  · rw [← Matrix.GeneralLinearGroup.val_det_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _), Units.val_one]

variable (h r ε)

theorem derivedSeries_two_semilinearSimilitudes_le :
    derivedSeries (semilinearSimilitudes h r ε) 2 ≤
      ((hypSU h r ε).map SemidirectProduct.inl).comap (semilinearSimilitudes h r ε).subtype := by
  have h1 : derivedSeries (semilinearSimilitudes h r ε) 1 ≤
      (SemidirectProduct.rightHom.comp (semilinearSimilitudes h r ε).subtype).ker := by
    rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact fieldAut_mul_comm h _ _
  rw [derivedSeries_succ, Subgroup.commutator_le]
  intro x hx y hy
  have hx1 := h1 hx
  have hy1 := h1 hy
  rw [MonoidHom.mem_ker] at hx1 hy1
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact commutator_mem_map_inl x.2 y.2 hx1 hy1

noncomputable abbrev projLineImage : Subgroup (semilinearPointGroup h r ε) :=
  (hypProjLineAction h r ε).range.subgroupOf (semilinearPointGroup h r ε)

instance projLineImage_normal : (projLineImage h r ε).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hypProjLineAction_range_le).mpr
    semilinearPointGroup_le_normalizer

@[expose] noncomputable def pointActionOnto :
    semilinearSimilitudes h r ε →* semilinearPointGroup h r ε :=
  (semilinearPointAction h r ε).codRestrict _ fun x => ⟨x, rfl⟩

theorem pointActionOnto_surjective : Function.Surjective (pointActionOnto h r ε) := by
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

theorem derivedSeries_two_semilinearPointGroup_le :
    derivedSeries (semilinearPointGroup h r ε) 2 ≤ projLineImage h r ε := by
  rw [← map_derivedSeries_eq (pointActionOnto_surjective h r ε), Subgroup.map_le_iff_le_comap]
  refine (derivedSeries_two_semilinearSimilitudes_le h r ε).trans ?_
  rintro x ⟨g, hg, hgx⟩
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  refine ⟨hypProj h r ε ⟨g, hg⟩, ?_⟩
  rw [hypProjLineAction_eq_semilinearPointAction]
  exact congrArg _ (Subtype.ext hgx)

theorem unitary_semilinear_point_quotient :
    (projLineImage h r ε).Normal ∧
      derivedSeries (semilinearPointGroup h r ε ⧸ projLineImage h r ε) 2 = ⊥ ∧
      Group.IsSolvable (semilinearPointGroup h r ε ⧸ projLineImage h r ε) := by
  have h2 : derivedSeries (semilinearPointGroup h r ε ⧸ projLineImage h r ε) 2 = ⊥ := by
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact derivedSeries_two_semilinearPointGroup_le h r ε
  exact ⟨inferInstance, h2, (Group.isSolvable_def _).mpr ⟨2, h2⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
