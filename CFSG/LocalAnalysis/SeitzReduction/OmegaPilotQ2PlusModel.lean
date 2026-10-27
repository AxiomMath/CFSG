module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (reindexQuadraticForm reindexQuadraticForm_apply reindexVectorEquiv plusIndexEquiv
    coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply)

section Lin

variable {K : Type*} [Field K] {m : ℕ}

@[expose] def plusAnisoFun (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    Fin (m + 2) ⊕ Fin (m + 2) → K :=
  Sum.elim
    (Fin.cases (v (.inl 0) + v (.inl 1))
      (Fin.cases (v (.inr 0) + v (.inr 1)) fun j => v (.inl j.succ.succ)))
    (Fin.cases (v (.inl 0) + b * v (.inr 0) + v (.inl 1))
      (Fin.cases (c * v (.inr 0) + b * v (.inl 1) + c * v (.inr 1)) fun j => v (.inr j.succ.succ)))

@[simp] theorem plusAnisoFun_inl_zero (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    plusAnisoFun b c v (.inl 0) = v (.inl 0) + v (.inl 1) := rfl

@[simp] theorem plusAnisoFun_inr_zero (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    plusAnisoFun b c v (.inr 0) = v (.inl 0) + b * v (.inr 0) + v (.inl 1) := rfl

@[simp] theorem plusAnisoFun_inl_one (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    plusAnisoFun b c v (.inl 1) = v (.inr 0) + v (.inr 1) := rfl

@[simp] theorem plusAnisoFun_inr_one (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    plusAnisoFun b c v (.inr 1) = c * v (.inr 0) + b * v (.inl 1) + c * v (.inr 1) := rfl

@[simp] theorem plusAnisoFun_inl_succ_succ (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K)
    (j : Fin m) : plusAnisoFun b c v (.inl j.succ.succ) = v (.inl j.succ.succ) := rfl

@[simp] theorem plusAnisoFun_inr_succ_succ (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K)
    (j : Fin m) : plusAnisoFun b c v (.inr j.succ.succ) = v (.inr j.succ.succ) := rfl

theorem fin_cases_two (i : Fin (m + 2)) : i = 0 ∨ i = 1 ∨ ∃ j : Fin m, i = j.succ.succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨i', rfl⟩
  · exact Or.inl h
  · rcases Fin.eq_zero_or_eq_succ i' with h | ⟨j, rfl⟩
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr ⟨j, rfl⟩)

@[expose] def plusAnisoLin (b c : K) :
    (Fin (m + 2) ⊕ Fin (m + 2) → K) →ₗ[K] (Fin (m + 2) ⊕ Fin (m + 2) → K) where
  toFun := plusAnisoFun b c
  map_add' v w := by
    funext s
    rcases s with i | i <;> rcases fin_cases_two i with rfl | rfl | ⟨j, rfl⟩ <;>
      simp only [plusAnisoFun_inl_zero, plusAnisoFun_inr_zero, plusAnisoFun_inl_one,
        plusAnisoFun_inr_one, plusAnisoFun_inl_succ_succ, plusAnisoFun_inr_succ_succ,
        Pi.add_apply] <;> ring
  map_smul' a v := by
    funext s
    rcases s with i | i <;> rcases fin_cases_two i with rfl | rfl | ⟨j, rfl⟩ <;>
      simp only [plusAnisoFun_inl_zero, plusAnisoFun_inr_zero, plusAnisoFun_inl_one,
        plusAnisoFun_inr_one, plusAnisoFun_inl_succ_succ, plusAnisoFun_inr_succ_succ,
        Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

theorem plusAnisoLin_apply (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    plusAnisoLin b c v = plusAnisoFun b c v := rfl

theorem plusAnisoLin_injective {b c : K} (hb : b ≠ 0) :
    Function.Injective (plusAnisoLin (m := m) b c) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h := fun s => congrFun hv s
  simp only [plusAnisoLin_apply, Pi.zero_apply] at h
  have h0 := h (.inl 0)
  have h0' := h (.inr 0)
  have h1 := h (.inl 1)
  have h1' := h (.inr 1)
  simp only [plusAnisoFun_inl_zero, plusAnisoFun_inr_zero, plusAnisoFun_inl_one,
    plusAnisoFun_inr_one] at h0 h0' h1 h1'
  have hβ : v (.inr 0) = 0 := by
    have : b * v (.inr 0) = 0 := by linear_combination h0' - h0
    exact (mul_eq_zero.mp this).resolve_left hb
  have hδ : v (.inr 1) = 0 := by linear_combination h1 - hβ
  have hγ : v (.inl 1) = 0 := by
    have : b * v (.inl 1) = 0 := by linear_combination h1' - c * hβ - c * hδ
    exact (mul_eq_zero.mp this).resolve_left hb
  have hα : v (.inl 0) = 0 := by linear_combination h0 - hγ
  funext s
  rcases s with i | i <;> rcases fin_cases_two i with rfl | rfl | ⟨j, rfl⟩
  · exact hα
  · exact hγ
  · simpa using h (.inl j.succ.succ)
  · exact hβ
  · exact hδ
  · simpa using h (.inr j.succ.succ)

theorem quadPlus_plusAnisoFun [CharP K 2] (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    quadPlus (m + 2) K (plusAnisoFun b c v) =
      (v (.inl 0) ^ 2 + b * v (.inl 0) * v (.inr 0) + c * v (.inr 0) ^ 2) +
      (v (.inl 1) ^ 2 + b * v (.inl 1) * v (.inr 1) + c * v (.inr 1) ^ 2) +
      ∑ j : Fin m, v (.inl j.succ.succ) * v (.inr j.succ.succ) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [quadPlus_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have e1 : ((0 : Fin (m + 1)).succ : Fin (m + 2)) = 1 := rfl
  simp only [e1, plusAnisoFun_inl_zero, plusAnisoFun_inr_zero, plusAnisoFun_inl_one,
    plusAnisoFun_inr_one, plusAnisoFun_inl_succ_succ, plusAnisoFun_inr_succ_succ]
  linear_combination (v (.inl 0) * v (.inl 1) + b * v (.inr 0) * v (.inl 1) +
    c * v (.inr 0) * v (.inr 1)) * h2

end Lin

section Form

variable (K : Type*) [Field K] (m : ℕ)

@[expose] noncomputable def plusAnisoQuad₀ (b c : K) :
    QuadraticForm K (Fin (m + 2) ⊕ Fin (m + 2) → K) :=
  (quadPlus (m + 2) K).comp (plusAnisoLin b c)

variable {K m}

theorem plusAnisoQuad₀_apply [CharP K 2] (b c : K) (v : Fin (m + 2) ⊕ Fin (m + 2) → K) :
    plusAnisoQuad₀ K m b c v =
      (v (.inl 0) ^ 2 + b * v (.inl 0) * v (.inr 0) + c * v (.inr 0) ^ 2) +
      (v (.inl 1) ^ 2 + b * v (.inl 1) * v (.inr 1) + c * v (.inr 1) ^ 2) +
      ∑ j : Fin m, v (.inl j.succ.succ) * v (.inr j.succ.succ) :=
  quadPlus_plusAnisoFun b c v

theorem fin_one_ne_zero' : (1 : Fin (m + 2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem fin_succ_succ_ne_zero (j : Fin m) : (j.succ.succ : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero _

theorem fin_succ_succ_ne_one (j : Fin m) : (j.succ.succ : Fin (m + 2)) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_succ] at this

theorem isAnisoCoord_plusAnisoQuad₀ [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsAnisoCoord (plusAnisoQuad₀ K m b c) (.inl 0) (.inr 0) b c where
  ne := Sum.inl_ne_inr
  map_left := by
    rw [plusAnisoQuad₀_apply]
    simp
  map_right := by
    rw [plusAnisoQuad₀_apply]
    simp
  polar_left v := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [QuadraticMap.polar, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply]
    simp only [Pi.add_apply, Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false,
      fin_one_ne_zero', fin_succ_succ_ne_zero, ite_true, zero_add]
    simp
    linear_combination v (.inl 0) * h2
  polar_right v := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [QuadraticMap.polar, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply]
    simp only [Pi.add_apply, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false,
      fin_one_ne_zero', fin_succ_succ_ne_zero, ite_true, zero_add]
    simp
    linear_combination c * v (.inr 0) * h2
  irr := hirr

theorem isHypCoord_plusAnisoQuad₀ [CharP K 2] (b c : K) (j : Fin m) :
    IsHypCoord (plusAnisoQuad₀ K m b c) (.inl j.succ.succ) (.inr j.succ.succ) where
  ne := Sum.inl_ne_inr
  map_left := by
    rw [plusAnisoQuad₀_apply]
    simp [Pi.single_apply, fin_succ_succ_ne_one]
  map_right := by
    rw [plusAnisoQuad₀_apply]
    simp [Pi.single_apply, fin_succ_succ_ne_one]
  polar_left v := by
    rw [QuadraticMap.polar, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply]
    simp [Pi.single_apply, fin_succ_succ_ne_one, add_mul, ite_mul,
      Finset.sum_add_distrib]
  polar_right v := by
    rw [QuadraticMap.polar, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply, plusAnisoQuad₀_apply]
    simp [Pi.single_apply, fin_succ_succ_ne_one, mul_add, mul_ite,
      Finset.sum_add_distrib]

end Form

section Coordinates

variable (K : Type) [Field K] (m : ℕ)

@[expose] noncomputable def plusAnisoQuad (b c : K) : QuadraticForm K (Fin (2 * (m + 2)) → K) :=
  reindexQuadraticForm (plusIndexEquiv (m + 2)) (plusAnisoQuad₀ K m b c)

@[expose] noncomputable def plusAnisoLeft : Fin (2 * (m + 2)) := plusIndexEquiv (m + 2) (.inl 0)

@[expose] noncomputable def plusAnisoRight : Fin (2 * (m + 2)) := plusIndexEquiv (m + 2) (.inr 0)

variable {K m}

@[expose] noncomputable def plusAnisoLinEquiv (b c : K) (hb : b ≠ 0) :
    (Fin (m + 2) ⊕ Fin (m + 2) → K) ≃ₗ[K] (Fin (m + 2) ⊕ Fin (m + 2) → K) :=
  LinearEquiv.ofInjectiveEndo (plusAnisoLin b c) (plusAnisoLin_injective hb)

@[expose] noncomputable def plusAnisoIsometry (b c : K) (hb : b ≠ 0) :
    (plusAnisoQuad K m b c).IsometryEquiv (coordinateQuadPlus (m + 2) K) where
  toLinearEquiv := ((reindexVectorEquiv (plusIndexEquiv (m + 2))).symm.trans
    (plusAnisoLinEquiv b c hb)).trans (reindexVectorEquiv (plusIndexEquiv (m + 2)))
  map_app' v := by
    change quadPlus (m + 2) K ((reindexVectorEquiv (plusIndexEquiv (m + 2))).symm
        (reindexVectorEquiv (plusIndexEquiv (m + 2))
          (plusAnisoLin b c ((reindexVectorEquiv (plusIndexEquiv (m + 2))).symm v)))) =
      quadPlus (m + 2) K (plusAnisoLin b c ((reindexVectorEquiv (plusIndexEquiv (m + 2))).symm v))
    rw [LinearEquiv.symm_apply_apply]

theorem regular_plusAnisoQuad {b c : K} (hb : b ≠ 0) (hm : 1 ≤ m) :
    (polarBilin (plusAnisoQuad K m b c)).Nondegenerate ∧
      ∃ T : Submodule K (Fin (2 * (m + 2)) → K), finrank K T = 3 ∧
        ∀ x ∈ T, plusAnisoQuad K m b c x = 0 := by
  have hreg := regular_coordinateQuadPlus (m + 2) K (by omega)
  exact ⟨nondegenerate_of_isometryEquiv (plusAnisoIsometry b c hb) hreg.1,
    exists_threeSingular_of_isometryEquiv (plusAnisoIsometry b c hb) hreg.2⟩

theorem isAnisoCoord_plusAnisoQuad [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsAnisoCoord (plusAnisoQuad K m b c) (plusAnisoLeft m) (plusAnisoRight m) b c :=
  (isAnisoCoord_plusAnisoQuad₀ hirr).reindex (plusIndexEquiv (m + 2))

theorem isHypCoord_plusAnisoQuad [CharP K 2] (b c : K) (j : Fin m) :
    IsHypCoord (plusAnisoQuad K m b c) (plusIndexEquiv (m + 2) (.inl j.succ.succ))
      (plusIndexEquiv (m + 2) (.inr j.succ.succ)) :=
  (isHypCoord_plusAnisoQuad₀ b c j).reindex (plusIndexEquiv (m + 2))

theorem pairDisjoint_plusAniso (j : Fin m) :
    PairDisjoint (plusAnisoLeft m) (plusAnisoRight m) (plusIndexEquiv (m + 2) (.inl j.succ.succ))
      (plusIndexEquiv (m + 2) (.inr j.succ.succ)) where
  left_ne_left h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp only [Sum.inl.injEq] at this
    exact fin_succ_succ_ne_zero j this
  left_ne_right h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp at this
  right_ne_left h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp at this
  right_ne_right h := by
    have := (plusIndexEquiv (m + 2)).injective h
    simp only [Sum.inr.injEq] at this
    exact fin_succ_succ_ne_zero j this

theorem pairDisjoint_plusAniso_hyp {j j' : Fin m} (h : j ≠ j') :
    PairDisjoint (plusIndexEquiv (m + 2) (.inl j.succ.succ))
      (plusIndexEquiv (m + 2) (.inr j.succ.succ)) (plusIndexEquiv (m + 2) (.inl j'.succ.succ))
      (plusIndexEquiv (m + 2) (.inr j'.succ.succ)) where
  left_ne_left h' := by
    have := (plusIndexEquiv (m + 2)).injective h'
    simp only [Sum.inl.injEq, Fin.succ_inj] at this
    exact h this.symm
  left_ne_right h' := by
    have := (plusIndexEquiv (m + 2)).injective h'
    simp at this
  right_ne_left h' := by
    have := (plusIndexEquiv (m + 2)).injective h'
    simp at this
  right_ne_right h' := by
    have := (plusIndexEquiv (m + 2)).injective h'
    simp only [Sum.inr.injEq, Fin.succ_inj] at this
    exact h this.symm

@[expose] noncomputable def plusAnisoMatrix (b c : K) (hb : b ≠ 0) : GL (Fin (2 * (m + 2))) K :=
  matrixLinearIso.symm (plusAnisoIsometry (m := m) b c hb).toLinearEquiv

theorem matrixLinearIso_plusAnisoMatrix (b c : K) (hb : b ≠ 0) :
    matrixLinearIso (plusAnisoMatrix (m := m) b c hb) =
      (plusAnisoIsometry (m := m) b c hb).toLinearEquiv :=
  MulEquiv.apply_symm_apply _ _

theorem coordinateQuadPlus_plusAnisoMatrix (b c : K) (hb : b ≠ 0) (v : Fin (2 * (m + 2)) → K) :
    coordinateQuadPlus (m + 2) K (matrixLinearIso (plusAnisoMatrix b c hb) v) =
      ((1 : Kˣ) : K) * plusAnisoQuad K m b c v := by
  rw [matrixLinearIso_plusAnisoMatrix, Units.val_one, one_mul]
  exact (plusAnisoIsometry b c hb).map_app v

end Coordinates

end CFSG.SeitzReduction.OmegaPilot
