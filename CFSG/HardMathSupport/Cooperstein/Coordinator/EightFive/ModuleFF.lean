module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleU1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

section General

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_isFFStarOffender_le_of_index_le {G E : Subgroup (MulAut W)} (hEG : E ≤ G)
    (hE : E ≠ ⊥) (hel : IsElemAbelian2 E) (hoff : (fixV E).index ≤ Nat.card E) :
    ∃ A₀, A₀ ≤ E ∧ IsFFStarOffender G A₀ ∧
      Nat.card E * Nat.card (fixV E) ≤ Nat.card A₀ * Nat.card (fixV A₀) := by
  have hW : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := by
    rw [← (fixV E).index_mul_card]
    exact Nat.mul_le_mul_right _ hoff
  obtain ⟨A₀, hA₀E, hA₀, hc⟩ := B1.exists_offender_below (X := G) ⟨hEG, hE, hel⟩
    (Nat.card E * Nat.card (fixV E) - Nat.card W) (by omega)
  exact ⟨A₀, hA₀E, hA₀, by omega⟩

theorem index_fixV_lt_card_of_le {E A₀ : Subgroup (MulAut W)}
    (hlt : (fixV E).index < Nat.card E)
    (hle : Nat.card E * Nat.card (fixV E) ≤ Nat.card A₀ * Nat.card (fixV A₀)) :
    (fixV A₀).index < Nat.card A₀ := by
  have h1 : Nat.card W < Nat.card E * Nat.card (fixV E) := by
    rw [← (fixV E).index_mul_card]
    exact Nat.mul_lt_mul_of_pos_right hlt Nat.card_pos
  have h2 : (fixV A₀).index * Nat.card (fixV A₀) < Nat.card A₀ * Nat.card (fixV A₀) := by
    rw [(fixV A₀).index_mul_card]
    omega
  exact Nat.lt_of_mul_lt_mul_right h2

theorem card_le_index_fixV_of_one_le_qOf (hW : ∀ w : W, w ^ 2 = 1) {G B : Subgroup (MulAut W)}
    (hq : (1 : WithTop ℚ) ≤ qOf G) (hBG : B ≤ G) (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) :
    Nat.card B ≤ (fixV B).index := by
  by_contra hlt
  push Not at hlt
  refine not_isStrongFFModule_of_one_le_qOf hW hq ⟨B, hBG, hB, hel, ?_⟩
  rw [← (fixV B).index_mul_card]
  exact Nat.mul_lt_mul_of_pos_right hlt Nat.card_pos

end General

section AltPre

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {Y₀ Y₁ : Subgroup V}

theorem exists_isFFStarOffender_autSec (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) {B : Subgroup (MulAut V)} (hBH : B ≤ H)
    (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) (hcod : (fixV (autSec B Y₁ Y₀)).index ≤ Nat.card B) :
    ∃ A₀, A₀ ≤ autSec B Y₁ Y₀ ∧ IsFFStarOffender (autSec H Y₁ Y₀) A₀ ∧
      Nat.card (autSec B Y₁ Y₀) * Nat.card (fixV (autSec B Y₁ Y₀)) ≤
        Nat.card A₀ * Nat.card (fixV A₀) := by
  have hcard := card_autSec_eq_card h5 hψ hAlt hH₀ hH₁ hL hBH
  exact exists_isFFStarOffender_le_of_index_le (autSec_mono hBH Y₁ Y₀)
    (autSec_ne_bot h5 hψ hAlt hH₀ hH₁ hL hBH hB) (isElemAbelian2_autSec Y₁ Y₀ hel)
    (hcard ▸ hcod)

theorem exists_isFFStarOffender_autSec_of_offender (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (h01 : Y₀ ≤ Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender H A) :
    ∃ A₀, A₀ ≤ autSec A Y₁ Y₀ ∧ IsFFStarOffender (autSec H Y₁ Y₀) A₀ ∧
      Nat.card (autSec A Y₁ Y₀) * Nat.card (fixV (autSec A Y₁ Y₀)) ≤
        Nat.card A₀ * Nat.card (fixV A₀) :=
  exists_isFFStarOffender_autSec h5 hψ hAlt hH₀ hH₁ hL hA.1 hA.2.1 hA.2.2.1
    (index_fixV_autSec_le hA h01 (hA.1.trans hH₁))

theorem exists_strong_isFFStarOffender_autSec (h5 : 5 ≤ n) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) {B : Subgroup (MulAut V)} (hBH : B ≤ H)
    (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) (hcod : (fixV (autSec B Y₁ Y₀)).index < Nat.card B) :
    ∃ A₀, A₀ ≤ autSec B Y₁ Y₀ ∧ IsFFStarOffender (autSec H Y₁ Y₀) A₀ ∧
      (fixV A₀).index < Nat.card A₀ := by
  obtain ⟨A₀, hA₀B, hA₀, hle⟩ :=
    exists_isFFStarOffender_autSec h5 hψ hAlt hH₀ hH₁ hL hBH hB hel hcod.le
  have hcard := card_autSec_eq_card h5 hψ hAlt hH₀ hH₁ hL hBH
  exact ⟨A₀, hA₀B, hA₀, index_fixV_lt_card_of_le (hcard ▸ hcod) hle⟩

theorem card_le_index_fixV_autSec (hV : ∀ v : V, v ^ 2 = 1) (h5 : 5 ≤ n)
    (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)
    (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁)
    (hq : (1 : WithTop ℚ) ≤ qOf (autSec H Y₁ Y₀)) {B : Subgroup (MulAut V)} (hBH : B ≤ H)
    (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) : Nat.card B ≤ (fixV (autSec B Y₁ Y₀)).index := by
  rw [← card_autSec_eq_card h5 hψ hAlt hH₀ hH₁ hL hBH]
  exact card_le_index_fixV_of_one_le_qOf (sq_eq_one_sec hV Y₁ Y₀) hq (autSec_mono hBH Y₁ Y₀)
    (autSec_ne_bot h5 hψ hAlt hH₀ hH₁ hL hBH hB) (isElemAbelian2_autSec Y₁ Y₀ hel)

theorem oneNoncentral_of_one_le_qOf (hV : ∀ v : V, v ^ 2 = 1) (h5 : 5 ≤ n)
    (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)
    (hP : ∃ A : Subgroup (MulAut V), IsFFStarOffender H A)
    (hq : ∀ Y₀ Y₁ : Subgroup V, IsChiefFac H Y₀ Y₁ → ¬ IsCentralSec (altPre ψ) Y₀ Y₁ →
      (1 : WithTop ℚ) ≤ qOf (autSec H Y₁ Y₀)) :
    OneNoncentral H (altPre ψ) := by
  obtain ⟨A, hA⟩ := hP
  exact oneNoncentral_altPre h5 hψ hAlt hA fun Y₀ Y₁ hY hYL =>
    card_le_index_fixV_autSec hV h5 hψ hAlt hY.stab₀ hY.stab₁ hYL (hq Y₀ Y₁ hY hYL) hA.1
      hA.2.1 hA.2.2.1

end AltPre

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
