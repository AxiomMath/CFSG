module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo Equiv Equiv.Perm

namespace CaseII

@[expose] def pv (σ : Perm (Fin 6)) (x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun i => x (σ⁻¹ i)

theorem pv_mul (σ τ : Perm (Fin 6)) (x : Fin 6 → ZMod 2) : pv (σ * τ) x = pv σ (pv τ x) := by
  funext i
  simp [pv, mul_inv_rev]

theorem pv_sub (σ : Perm (Fin 6)) (x y : Fin 6 → ZMod 2) : pv σ (x - y) = pv σ x - pv σ y := rfl

theorem pv_one_left (x : Fin 6 → ZMod 2) : pv 1 x = x := rfl

theorem pv_inv_pv (σ : Perm (Fin 6)) (x : Fin 6 → ZMod 2) : pv σ⁻¹ (pv σ x) = x := by
  rw [← pv_mul, inv_mul_cancel, pv_one_left]

theorem pv_injective (σ : Perm (Fin 6)) : Function.Injective (pv σ) := fun x y h => by
  rw [← pv_inv_pv σ x, h, pv_inv_pv]

theorem pv_zero (σ : Perm (Fin 6)) : pv σ 0 = 0 := rfl

theorem pv_allOnes (σ : Perm (Fin 6)) : pv σ (allOnes 6) = allOnes 6 := rfl

theorem sum_pv (σ : Perm (Fin 6)) (x : Fin 6 → ZMod 2) : ∑ i, pv σ x i = ∑ i, x i :=
  Equiv.sum_comp σ⁻¹ x

theorem pv_conj (π σ : Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    pv (π * σ * π⁻¹) (pv π x) - pv π x = pv π (pv σ x - x) := by
  rw [pv_sub, ← pv_mul, ← pv_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

@[expose] def IsTriv (x : Fin 6 → ZMod 2) : Prop := x = 0 ∨ x = allOnes 6

instance (x : Fin 6 → ZMod 2) : Decidable (IsTriv x) := by
  unfold IsTriv
  infer_instance

theorem isTriv_pv_iff (σ : Perm (Fin 6)) (x : Fin 6 → ZMod 2) : IsTriv (pv σ x) ↔ IsTriv x := by
  unfold IsTriv
  constructor
  · rintro (h | h)
    · left
      exact pv_injective σ (h.trans (pv_zero σ).symm)
    · right
      exact pv_injective σ (h.trans (pv_allOnes σ).symm)
  · rintro (rfl | rfl)
    · exact Or.inl (pv_zero σ)
    · exact Or.inr (pv_allOnes σ)

@[expose] def dt₀ : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def d3₀ : Perm (Fin 6) := swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)

@[expose] def c3₀ : Perm (Fin 6) := swap 0 1 * swap 1 2

theorem c3₀_eq : c3₀ = (CFSG.ComponentClassification.RankTwoAlt.a6c012 : Perm (Fin 6)) := rfl

@[expose] def dtx : Fin 3 → Fin 6 → ZMod 2 := ![![1, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0],
  ![1, 0, 1, 0, 0, 0]]

theorem dtx_sum : ∀ k, ∑ i, dtx k i = 0 := by decide

theorem dt_three : (∀ k, ¬ IsTriv (pv dt₀ (dtx k) - dtx k)) ∧
    ∀ k l, k ≠ l → ¬ IsTriv ((pv dt₀ (dtx k) - dtx k) - (pv dt₀ (dtx l) - dtx l)) := by
  decide

theorem d3_no_fixed : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 → IsTriv (pv d3₀ x - x) → IsTriv x := by
  decide

@[expose] def c3x : Fin 6 → ZMod 2 := ![0, 0, 0, 1, 1, 0]

theorem c3_fixed : ∑ i, c3x i = 0 ∧ ¬ IsTriv c3x ∧ pv c3₀ c3x = c3x := by decide

@[expose] def c3y : Fin 4 → Fin 6 → ZMod 2 := ![0, ![1, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0]]

theorem c3_comm_le : ∀ x : Fin 6 → ZMod 2, ∑ i, x i = 0 → ∃ k, pv c3₀ x - x = c3y k := by decide

theorem c3_comm_ge : ∀ k, ∃ x : Fin 6 → ZMod 2, ∑ i, x i = 0 ∧ pv c3₀ x - x = c3y k := by decide

theorem c3y_distinct : ∀ k l, k ≠ l → ¬ IsTriv (c3y k - c3y l) := by decide

end CaseII

end CFSG.CGT.Foote82
