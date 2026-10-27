module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PlusAut
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (reindexQuadraticForm reindexQuadraticForm_apply plusIndexEquiv minusIndexEquiv
    coordinateQuadPlus coordinateQuadMinus coordinateQuadMinus_apply regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section PerpCoord

variable {m : ℕ}

variable (m) in
@[expose] def plusAnisoPerpIdx :
    Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → Fin (m + 2) ⊕ Fin (m + 2)
  | .inl i => .inl (i : Fin m).succ.succ
  | .inr (.inl i) => .inr (i : Fin m).succ.succ
  | .inr (.inr t) => if t = 0 then .inl 1 else .inr 1

theorem plusAnisoPerpIdx_injective : Function.Injective (plusAnisoPerpIdx m) := by
  have ht : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  have h1 := fin_succ_succ_ne_one (m := m)
  intro s s' h
  rcases s with i | i | t <;> rcases s' with i' | i' | t'
  · simp only [plusAnisoPerpIdx, Sum.inl.injEq, Fin.succ_inj] at h
    rw [h]
  · simp [plusAnisoPerpIdx] at h
  · rcases ht t' with rfl | rfl <;> simp_all [plusAnisoPerpIdx]
  · simp [plusAnisoPerpIdx] at h
  · simp only [plusAnisoPerpIdx, Sum.inr.injEq, Fin.succ_inj] at h
    rw [h]
  · rcases ht t' with rfl | rfl <;> simp_all [plusAnisoPerpIdx]
  · rcases ht t with rfl | rfl <;> simp_all [plusAnisoPerpIdx, eq_comm]
  · rcases ht t with rfl | rfl <;> simp_all [plusAnisoPerpIdx, eq_comm]
  · rcases ht t with rfl | rfl <;> rcases ht t' with rfl | rfl <;> simp_all [plusAnisoPerpIdx]

theorem plusAnisoPerpIdx_ne_inl_zero (s : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :
    plusAnisoPerpIdx m s ≠ .inl 0 := by
  rcases s with i | i | t <;> simp only [plusAnisoPerpIdx, ne_eq]
  · simp only [Sum.inl.injEq]
    exact fin_succ_succ_ne_zero (m := m) i
  · simp
  · split_ifs <;> simp

theorem plusAnisoPerpIdx_ne_inr_zero (s : Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) :
    plusAnisoPerpIdx m s ≠ .inr 0 := by
  rcases s with i | i | t <;> simp only [plusAnisoPerpIdx, ne_eq]
  · simp
  · simp only [Sum.inr.injEq]
    exact fin_succ_succ_ne_zero (m := m) i
  · split_ifs <;> simp

theorem exists_plusAnisoPerpIdx_eq {s : Fin (m + 2) ⊕ Fin (m + 2)} (h0 : s ≠ .inl 0)
    (h0' : s ≠ .inr 0) : ∃ s', plusAnisoPerpIdx m s' = s := by
  rcases s with i | i <;> rcases fin_cases_two i with rfl | rfl | ⟨j, rfl⟩
  · exact absurd rfl h0
  · exact ⟨.inr (.inr 0), by simp [plusAnisoPerpIdx]⟩
  · exact ⟨.inl (j : Fin (m + 1 - 1)), rfl⟩
  · exact absurd rfl h0'
  · exact ⟨.inr (.inr 1), by simp [plusAnisoPerpIdx]⟩
  · exact ⟨.inr (.inl (j : Fin (m + 1 - 1))), rfl⟩

variable (m) in
@[expose] noncomputable def plusAnisoPerpCoord (x : Fin (2 * (m + 1))) : Fin (2 * (m + 2)) :=
  plusIndexEquiv (m + 2) (plusAnisoPerpIdx m ((minusIndexEquiv (m + 1) (by omega)).symm x))

theorem plusAnisoPerpCoord_injective : Function.Injective (plusAnisoPerpCoord m) := fun x y h =>
  (minusIndexEquiv (m + 1) (by omega)).symm.injective
    (plusAnisoPerpIdx_injective ((plusIndexEquiv (m + 2)).injective h))

theorem plusAnisoPerpCoord_ne_left (x : Fin (2 * (m + 1))) :
    plusAnisoPerpCoord m x ≠ plusAnisoLeft m := fun h =>
  plusAnisoPerpIdx_ne_inl_zero _ ((plusIndexEquiv (m + 2)).injective h)

theorem plusAnisoPerpCoord_ne_right (x : Fin (2 * (m + 1))) :
    plusAnisoPerpCoord m x ≠ plusAnisoRight m := fun h =>
  plusAnisoPerpIdx_ne_inr_zero _ ((plusIndexEquiv (m + 2)).injective h)

theorem exists_plusAnisoPerpCoord_eq {i : Fin (2 * (m + 2))} (hia : i ≠ plusAnisoLeft m)
    (hib : i ≠ plusAnisoRight m) : ∃ x, plusAnisoPerpCoord m x = i := by
  obtain ⟨s', hs'⟩ := exists_plusAnisoPerpIdx_eq (m := m) (s := (plusIndexEquiv (m + 2)).symm i)
    (fun h => hia ((Equiv.symm_apply_eq _).mp h))
    (fun h => hib ((Equiv.symm_apply_eq _).mp h))
  refine ⟨minusIndexEquiv (m + 1) (by omega) s', ?_⟩
  rw [plusAnisoPerpCoord, Equiv.symm_apply_apply, hs', Equiv.apply_symm_apply]

theorem plusAnisoQuad_extend_perp {K : Type} [Field K] [CharP K 2] (b c : K)
    (w : Fin (2 * (m + 1)) → K) :
    plusAnisoQuad K m b c (Function.extend (plusAnisoPerpCoord m) w 0) =
      coordinateQuadMinus (m + 1) K (by omega) b c w := by
  have hinj := plusAnisoPerpCoord_injective (m := m)
  set v : Fin (m + 2) ⊕ Fin (m + 2) → K :=
    fun s => Function.extend (plusAnisoPerpCoord m) w 0 (plusIndexEquiv (m + 2) s) with hv
  have hval : ∀ s', v (plusAnisoPerpIdx m s') = w (minusIndexEquiv (m + 1) (by omega) s') := by
    intro s'
    have e : plusIndexEquiv (m + 2) (plusAnisoPerpIdx m s') =
        plusAnisoPerpCoord m (minusIndexEquiv (m + 1) (by omega) s') := by
      simp [plusAnisoPerpCoord]
    rw [hv]
    dsimp only
    rw [e, hinj.extend_apply]
  have h0 : v (.inl 0) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => plusAnisoPerpCoord_ne_left x hx
  have h0' : v (.inr 0) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => plusAnisoPerpCoord_ne_right x hx
  have h1 : v (.inl 1) = w (minusIndexEquiv (m + 1) (by omega) (.inr (.inr 0))) := by
    rw [← hval]
    simp [plusAnisoPerpIdx]
  have h1' : v (.inr 1) = w (minusIndexEquiv (m + 1) (by omega) (.inr (.inr 1))) := by
    rw [← hval]
    simp [plusAnisoPerpIdx]
  rw [plusAnisoQuad, reindexQuadraticForm_apply, plusAnisoQuad₀_apply, coordinateQuadMinus_apply]
  change (v (.inl 0) ^ 2 + b * v (.inl 0) * v (.inr 0) + c * v (.inr 0) ^ 2) +
      (v (.inl 1) ^ 2 + b * v (.inl 1) * v (.inr 1) + c * v (.inr 1) ^ 2) +
      ∑ j : Fin m, v (.inl j.succ.succ) * v (.inr j.succ.succ) = _
  rw [h0, h0', h1, h1']
  have hs : ∀ j : Fin m, v (.inl j.succ.succ) * v (.inr j.succ.succ) =
      w (minusIndexEquiv (m + 1) (by omega) (.inl j)) *
        w (minusIndexEquiv (m + 1) (by omega) (.inr (.inl j))) := fun j => by
    rw [← hval (.inl j), ← hval (.inr (.inl j))]
    rfl
  have hsum : (∑ j : Fin m, w (minusIndexEquiv (m + 1) (by omega) (.inl j)) *
        w (minusIndexEquiv (m + 1) (by omega) (.inr (.inl j)))) =
      ∑ i : Fin (m + 1 - 1), w (minusIndexEquiv (m + 1) (by omega) (.inl i)) *
        w (minusIndexEquiv (m + 1) (by omega) (.inr (.inl i))) := rfl
  rw [Finset.sum_congr rfl fun j _ => hs j, hsum]
  ring

end PerpCoord

section Perp

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

variable (m) in
@[expose] noncomputable def plusAnisoPerpIsometry (b c : K) :
    ((plusAnisoQuad K m b c).comp
      (perpSub K (plusAnisoLeft m) (plusAnisoRight m)).subtype).IsometryEquiv
      (coordinateQuadMinus (m + 1) K (by omega) b c) :=
  perpIsometry (plusAnisoPerpCoord m) plusAnisoPerpCoord_injective plusAnisoPerpCoord_ne_left
    plusAnisoPerpCoord_ne_right (fun _ hia hib => exists_plusAnisoPerpCoord_eq hia hib)
    (plusAnisoQuad_extend_perp b c)

variable [Finite K]

theorem regular_plusAnisoPerp (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin ((plusAnisoQuad K m b c).comp
      (perpSub K (plusAnisoLeft m) (plusAnisoRight m)).subtype)).Nondegenerate ∧
    ∃ T : Submodule K (perpSub K (plusAnisoLeft m) (plusAnisoRight m)),
      finrank K T = 3 ∧ ∀ x ∈ T, (plusAnisoQuad K m b c).comp
        (perpSub K (plusAnisoLeft m) (plusAnisoRight m)).subtype x = 0 := by
  have hreg := regular_coordinateQuadMinus (m + 1) K b c (by omega) hirr
  have e := plusAnisoPerpIsometry (K := K) m b c
  exact ⟨nondegenerate_of_isometryEquiv e hreg.1, exists_threeSingular_of_isometryEquiv e hreg.2⟩

@[expose] noncomputable def plusAnisoPerpEquiv (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    plusAnisoPerp (K := K) m b c ≃* orthDerived (coordinateQuadMinus (m + 1) K (by omega) b c) :=
  ((isAnisoCoord_plusAnisoQuad hirr).pairPerpOfEquiv
    (regular_plusAnisoQuad (coeff_ne_zero_of_irreducible' hirr) (by omega)).1
    (regular_plusAnisoPerp hm hirr).1 (regular_plusAnisoPerp hm hirr).2).trans
    (orthDerivedCongr (plusAnisoPerpIsometry m b c))

theorem isQuasisimple_plusAnisoPerp (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.IsQuasisimple (plusAnisoPerp (K := K) m b c) :=
  (isAnisoCoord_plusAnisoQuad hirr).isQuasisimple_pairPerpOf
    (regular_plusAnisoQuad (coeff_ne_zero_of_irreducible' hirr) (by omega)).1
    (regular_plusAnisoPerp hm hirr).1 (regular_plusAnisoPerp hm hirr).2

theorem center_plusAnisoPerp (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    center (plusAnisoPerp (K := K) m b c) = ⊥ := by
  have hreg := regular_coordinateQuadMinus (m + 1) K b c (by omega) hirr
  rw [eq_bot_iff]
  intro x hx
  have hx' : plusAnisoPerpEquiv hm hirr x ∈
      center (orthDerived (coordinateQuadMinus (m + 1) K _ b c)) := by
    rw [← map_center_eq (plusAnisoPerpEquiv hm hirr)]
    exact ⟨x, hx, rfl⟩
  rw [center_orthDerived_eq_bot' hreg.1 hreg.2
    (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ m + 1) b c
      (⟨0, by omega⟩ : Fin (m + 1 - 1))).exists_ne_zero, mem_bot] at hx'
  rw [mem_bot, ← (plusAnisoPerpEquiv hm hirr).symm_apply_apply x, hx', map_one]

theorem lieModel_plusAnisoPerp {f : ℕ} (hK : Nat.card K = 2 ^ f) (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Blueprint.LieModel (plusAnisoPerp (K := K) m b c) .POmegaMinus (m + 1) 2 f :=
  lieModel_of_mulEquiv_orthDerived_minus (by omega) (LinearPilot.one_le_of_card_eq_two_pow hK) hK
    hirr (plusAnisoPerpEquiv hm hirr)

@[expose] noncomputable def plusAnisoPerpProjEquiv (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    plusAnisoPerp (K := K) m b c ≃*
      matrixProjectiveDerived (coordinateQuadMinus (m + 1) K (by omega) b c) :=
  (plusAnisoPerpEquiv hm hirr).trans (MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ m + 1) b c
      (⟨0, by omega⟩ : Fin (m + 1 - 1))).exists_ne_zero, projHom_surjective _⟩)

end Perp

end CFSG.SeitzReduction.OmegaPilot
