module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsSigma
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalAut
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaInputs
open scoped MatrixGroups

namespace SL44

@[expose] def twist (ε : ℕ) (x : SL(4, F4)) : SL(4, F4) := if ε = 0 then x else x⁻¹

@[expose] def HasTrType (β : MulAut SL(4, F4)) (σ : F4 ≃+* F4) (ε : ℕ) : Prop :=
  ∀ x : SL(4, F4), (β x : Matrix (Fin 4) (Fin 4) F4).trace =
    σ (twist ε x : Matrix (Fin 4) (Fin 4) F4).trace

theorem trace_map (σ : F4 ≃+* F4) (M : Matrix (Fin 4) (Fin 4) F4) :
    (M.map σ).trace = σ M.trace := by
  simp [Matrix.trace, map_sum]

theorem trace_conj (A : GL (Fin 4) F4) (M : Matrix (Fin 4) (Fin 4) F4) :
    ((A : Matrix (Fin 4) (Fin 4) F4) * M *
      ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem coe_stdSL_zero (A : GL (Fin 4) F4) (σ : F4 ≃+* F4) (x : SL(4, F4)) :
    (stdSL 4 F4 A σ 0 x : Matrix (Fin 4) (Fin 4) F4) =
      (A : Matrix (Fin 4) (Fin 4) F4) * (x : Matrix (Fin 4) (Fin 4) F4).map σ *
        ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) := by
  rw [stdSL, pow_zero, mul_one, MulAut.mul_apply,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
  rfl

@[simp] theorem twist_zero (x : SL(4, F4)) : twist 0 x = x := rfl

@[simp] theorem twist_one (x : SL(4, F4)) : twist 1 x = x⁻¹ := rfl

theorem hasTrType_stdSL (A : GL (Fin 4) F4) (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1) :
    HasTrType (stdSL 4 F4 A σ ε) σ ε := by
  intro x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [coe_stdSL_zero, trace_conj, trace_map, twist_zero]
  · rw [coe_stdSL_graphField, trace_conj, Matrix.trace_transpose, trace_map, twist_one]

theorem twist_twist {ε ε' : ℕ} (hε : ε ≤ 1) (hε' : ε' ≤ 1) (x : SL(4, F4)) :
    twist ε' (twist ε x) = twist ((ε + ε') % 2) x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε' with rfl | rfl <;> simp

theorem twist_map (β : MulAut SL(4, F4)) (ε : ℕ) (x : SL(4, F4)) :
    twist ε (β x) = β (twist ε x) := by
  unfold twist
  split_ifs
  · rfl
  · rw [map_inv]

theorem HasTrType.mul {β β' : MulAut SL(4, F4)} {σ σ' : F4 ≃+* F4} {ε ε' : ℕ}
    (h : HasTrType β σ ε) (h' : HasTrType β' σ' ε') (hε : ε ≤ 1) (hε' : ε' ≤ 1) :
    HasTrType (β * β') (σ * σ') ((ε + ε') % 2) := by
  intro x
  rw [MulAut.mul_apply, h, twist_map, h', twist_twist hε hε', RingAut.mul_apply]

@[expose] def x₀Mat : Matrix (Fin 4) (Fin 4) F4 := Matrix.diagonal ![F4.ω, F4.ω, F4.ω, 1]

@[expose] def y₀Mat : Matrix (Fin 4) (Fin 4) F4 :=
  Matrix.diagonal ![F4.ω * F4.ω, F4.ω * F4.ω, F4.ω * F4.ω, 1]

@[expose] def x₁Mat : Matrix (Fin 4) (Fin 4) F4 :=
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1]

@[expose] def y₁Mat : Matrix (Fin 4) (Fin 4) F4 :=
  !![0, 1, 0, 0; 1, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1]

@[expose] def x₀ : SL(4, F4) :=
  ⟨x₀Mat, by simp [x₀Mat, Matrix.det_diagonal, Fin.prod_univ_four]; decide⟩

@[expose] def x₁ : SL(4, F4) :=
  ⟨x₁Mat, by simp [x₁Mat, Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide⟩

theorem coe_inv_eq {x : SL(4, F4)} {M : Matrix (Fin 4) (Fin 4) F4}
    (h : (x : Matrix (Fin 4) (Fin 4) F4) * M = 1) :
    ((x⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) = M := by
  have h2 : ((x⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) * x = 1 :=
    congrArg Subtype.val (inv_mul_cancel x)
  calc ((x⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4)
      = ((x⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4) *
          ((x : Matrix (Fin 4) (Fin 4) F4) * M) := by
        rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem traces :
    (x₀ : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω * F4.ω ∧
      ((x₀⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω ∧
      (x₁ : Matrix (Fin 4) (Fin 4) F4).trace = 0 ∧
      ((x₁⁻¹ : SL(4, F4)) : Matrix (Fin 4) (Fin 4) F4).trace = 1 := by
  rw [coe_inv_eq (M := y₀Mat) (by decide), coe_inv_eq (M := y₁Mat) (by decide)]
  decide

theorem signature (σ : F4 ≃+* F4) {ε : ℕ} (hε : ε ≤ 1) :
    (σ = 1 ∧ ε = 0 ∧ σ (twist ε x₀ : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω * F4.ω ∧
        σ (twist ε x₁ : Matrix (Fin 4) (Fin 4) F4).trace = 0) ∨
      (σ = barEquiv ∧ ε = 0 ∧ σ (twist ε x₀ : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω ∧
        σ (twist ε x₁ : Matrix (Fin 4) (Fin 4) F4).trace = 0) ∨
      (σ = 1 ∧ ε = 1 ∧ σ (twist ε x₀ : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω ∧
        σ (twist ε x₁ : Matrix (Fin 4) (Fin 4) F4).trace = 1) ∨
      (σ = barEquiv ∧ ε = 1 ∧ σ (twist ε x₀ : Matrix (Fin 4) (Fin 4) F4).trace = F4.ω * F4.ω ∧
        σ (twist ε x₁ : Matrix (Fin 4) (Fin 4) F4).trace = 1) := by
  obtain ⟨t₀, t₀', t₁, t₁'⟩ := traces
  rcases ringEquiv_eq_one_or_eq_barEquiv σ with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exact Or.inl ⟨rfl, rfl, by rw [twist_zero, t₀]; rfl, by rw [twist_zero, t₁]; rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by rw [twist_one, t₀']; rfl,
      by rw [twist_one, t₁']; rfl⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl, by rw [twist_zero, t₀, barEquiv_apply]; decide,
      by rw [twist_zero, t₁, map_zero]⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by rw [twist_one, t₀', barEquiv_apply]; decide,
      by rw [twist_one, t₁', map_one]⟩))

theorem HasTrType.unique {β : MulAut SL(4, F4)} {σ σ' : F4 ≃+* F4} {ε ε' : ℕ}
    (h : HasTrType β σ ε) (h' : HasTrType β σ' ε') (hε : ε ≤ 1) (hε' : ε' ≤ 1) :
    σ = σ' ∧ ε = ε' := by
  have e₀ := (h x₀).symm.trans (h' x₀)
  have e₁ := (h x₁).symm.trans (h' x₁)
  rcases signature σ hε with ⟨rfl, rfl, a₀, a₁⟩ | ⟨rfl, rfl, a₀, a₁⟩ | ⟨rfl, rfl, a₀, a₁⟩ |
      ⟨rfl, rfl, a₀, a₁⟩ <;>
    rcases signature σ' hε' with ⟨rfl, rfl, b₀, b₁⟩ | ⟨rfl, rfl, b₀, b₁⟩ | ⟨rfl, rfl, b₀, b₁⟩ |
      ⟨rfl, rfl, b₀, b₁⟩ <;>
    first
    | exact ⟨rfl, rfl⟩
    | (rw [a₀, b₀] at e₀; exact absurd e₀ (by decide))
    | (rw [a₁, b₁] at e₁; exact absurd e₁ (by decide))

theorem frobeniusEquiv_eq_barEquiv : frobeniusEquiv F4 2 = barEquiv :=
  RingEquiv.ext fun c => by
    rw [frobeniusEquiv_apply, frobenius_def, barEquiv_apply, bar_apply]

theorem hasTrType_sigmaSL :
    HasTrType (CFSG.EvenSmallLie.UnitarySix.YamadaEnd.sigmaSL F4) barEquiv 1 := by
  rw [sigmaSL_eq_stdSL, frobeniusEquiv_eq_barEquiv]
  exact hasTrType_stdSL _ _ le_rfl

theorem ringEquiv_mul_self (σ : F4 ≃+* F4) : σ * σ = 1 := by
  rcases ringEquiv_eq_one_or_eq_barEquiv σ with rfl | rfl
  · exact mul_one 1
  · exact RingEquiv.ext fun c => by
      rw [RingAut.mul_apply, barEquiv_apply, barEquiv_apply, bar_bar, RingAut.one_apply]

end SL44

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
