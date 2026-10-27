module

public import CFSG.GroupTheory.HyperplaneGeneration
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_fixed_vec_of_coprime [Finite K] {r : ℕ} [Fact r.Prime] (hr : ¬ r ∣ Nat.card K)
    {A : Type} [Group A] [Finite A] [CFSG.IsElementaryAbelian r A] (hA : r ^ 2 ≤ Nat.card A)
    (ρ : A →* Matrix.GeneralLinearGroup ι K) (U : Submodule K (ι → K)) (hU : U ≠ ⊥)
    (hinv : ∀ a : A, ∀ u ∈ U, (ρ a : Matrix ι ι K) *ᵥ u ∈ U) :
    ∃ a : A, a ≠ 1 ∧ ∃ u ∈ U, u ≠ 0 ∧ (ρ a : Matrix ι ι K) *ᵥ u = u := by
  classical
  let _ : MulDistribMulAction A (Multiplicative ↥U) :=
    { smul := fun a m => Multiplicative.ofAdd ⟨(ρ a : Matrix ι ι K) *ᵥ (Multiplicative.toAdd m).1,
        hinv a _ (Multiplicative.toAdd m).2⟩
      one_smul := fun m => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show (ρ 1 : Matrix ι ι K) *ᵥ _ = _
        rw [map_one, Units.val_one, Matrix.one_mulVec]
      mul_smul := fun a b m => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show (ρ (a * b) : Matrix ι ι K) *ᵥ _ = (ρ a : Matrix ι ι K) *ᵥ ((ρ b : Matrix ι ι K) *ᵥ _)
        rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]
      smul_mul := fun a m n => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show (ρ a : Matrix ι ι K) *ᵥ ((Multiplicative.toAdd m).1 + (Multiplicative.toAdd n).1) = _
        rw [Matrix.mulVec_add]
        rfl
      smul_one := fun a => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        show (ρ a : Matrix ι ι K) *ᵥ 0 = 0
        rw [Matrix.mulVec_zero] }
  have hcard : ¬ r ∣ Nat.card (Multiplicative ↥U) := by
    intro h
    have h1 : Nat.card (Multiplicative ↥U) = Nat.card K ^ Module.finrank K U := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative ↥U ≃ ↥U)]
      have : Fintype K := Fintype.ofFinite K
      have : Fintype ↥U := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank
    rw [h1] at h
    exact hr ((Fact.out : r.Prime).dvd_of_dvd_pow h)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := r) (A := A)
    (H := Multiplicative ↥U) hA hcard
  by_contra hcon
  push Not at hcon
  have hbot : (⨆ (a : A) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a)
      (Multiplicative ↥U)) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun a ha => ?_)
    intro x hx
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hx0 : (Multiplicative.toAdd x).1 ≠ 0 := fun h0 =>
      hx1 (Multiplicative.toAdd.injective (Subtype.ext h0))
    apply hcon a ha (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 hx0
    have := congrArg (fun m => (Multiplicative.toAdd m).1) hx
    exact this
  rw [hbot] at hgen
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have : (Multiplicative.ofAdd (⟨u, huU⟩ : ↥U) : Multiplicative ↥U) ∈
      (⊤ : Subgroup (Multiplicative ↥U)) :=
    Subgroup.mem_top _
  rw [← hgen, Subgroup.mem_bot] at this
  exact hu0 (congrArg (fun m => (Multiplicative.toAdd m).1) this)

end CFSG.GH74.GLS.Stage2.OddAut
