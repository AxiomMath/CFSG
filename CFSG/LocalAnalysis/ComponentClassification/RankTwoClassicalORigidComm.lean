module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidQEGrp

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Comm

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι] [DecidableEq ι]
  (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

theorem qE_commutator (u u' : Fin 2 → ι₂ → K) (c c' : K) :
    ⁅qEGL oe Q₂ u c, qEGL oe Q₂ u' c'⁆ =
      qEGL oe Q₂ 0 (Q₂.polarBilin (u' 0) (u 1) + Q₂.polarBilin (u 0) (u' 1)) := by
  apply Units.ext
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
  change qE oe Q₂ u c * qE oe Q₂ u' c' * qE oe Q₂ u (c + Q₂.polarBilin (u 0) (u 1)) *
    qE oe Q₂ u' (c' + Q₂.polarBilin (u' 0) (u' 1)) = _
  rw [qE_mul, qE_mul, qE_mul, coe_qEGL]
  congr 1
  · funext t a
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination (u t a + u' t a) * CharTwo.two_eq_zero (R := K)
  · simp only [Pi.add_apply, map_add]
    linear_combination (c + c' + Q₂.polarBilin (u 0) (u 1) + Q₂.polarBilin (u' 0) (u' 1) +
      Q₂.polarBilin (u' 0) (u 1)) * CharTwo.two_eq_zero (R := K)

end Comm

section Torus

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] in
theorem exists_torusSL {t : K} (ht : t ≠ 0) :
    ∃ A : SL(2, K), (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹] :=
  exists_diag_sl2 ht

theorem qE_torus_commutator {t : K} {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) (u : Fin 2 → ι₂ → K) (c : K) :
    ∃ c'' : K, ⁅oRhoTwoGL oe A, qEGL oe Q₂ u c⁆ =
      qEGL oe Q₂ (fun s => if s = 0 then (t + 1) • u 0 else (t⁻¹ + 1) • u 1) c'' := by
  obtain ⟨c', hc'⟩ := conj_qE_levi hQ (Y := 1) (fun w => by simp) A u c
  simp only [map_one, one_mul, Units.val_one, one_mulVec] at hc'
  refine ⟨c' + (c + Q₂.polarBilin (u 0) (u 1)) + Q₂.polarBilin (u 0)
    (∑ r, (A : Matrix (Fin 2) (Fin 2) K) 1 r • u r), ?_⟩
  rw [commutatorElement_def, hc']
  apply Units.ext
  rw [Units.val_mul]
  change qE oe Q₂ _ c' * qE oe Q₂ u (c + Q₂.polarBilin (u 0) (u 1)) = _
  rw [qE_mul, coe_qEGL]
  congr 1
  funext s a
  fin_cases s <;> simp [hA, Fin.sum_univ_two, add_mul]

end Torus

end CFSG.ComponentClassification.RankTwoClassical.ORigid
