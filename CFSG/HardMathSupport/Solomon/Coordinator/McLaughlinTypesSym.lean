module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal

variable {m : ℕ}

theorem mclt_exists_notMem (s : Finset (Fin m)) (hs : s.card < m) : ∃ l, l ∉ s := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by rwa [Finset.card_univ, Fintype.card_fin])
  exact ⟨l, hl⟩

theorem mclt_permCoord_pairVec_sub_ne_const (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)}
    (hσ : σ ≠ 1) : ∃ i k : Fin m, ∀ c : ZMod 2,
      permCoord σ (pairVec i k : Fin m → ZMod 2) - (pairVec i k : Fin m → ZMod 2) ≠
        fun _ => c := by
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra! h
    exact hσ (Equiv.ext h)
  obtain ⟨k, hk⟩ := mclt_exists_notMem {i, σ i}
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨l, hl⟩ := mclt_exists_notMem {i, σ i, k, σ k}
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
  obtain ⟨hki, hkσ⟩ := hk
  obtain ⟨hli, hlσ, hlk, hlσk⟩ := hl
  refine ⟨i, k, fun c hc => ?_⟩
  have hl1 : σ.symm l ≠ i := fun h => hlσ (by rw [← h, Equiv.apply_symm_apply])
  have hl2 : σ.symm l ≠ k := fun h => hlσk (by rw [← h, Equiv.apply_symm_apply])
  have v1 : (permCoord σ (pairVec i k : Fin m → ZMod 2) - (pairVec i k : Fin m → ZMod 2)) (σ i) =
      1 := by
    simp [permCoord_apply, coe_pairVec, hi, Ne.symm hkσ, Ne.symm hki]
  have v2 : (permCoord σ (pairVec i k : Fin m → ZMod 2) - (pairVec i k : Fin m → ZMod 2)) l =
      0 := by
    simp [permCoord_apply, coe_pairVec, hl1, hl2, hli, hlk]
  rw [hc] at v1 v2
  exact one_ne_zero (v1.symm.trans v2)

theorem mclt_sumZeroRep_injective (hm : 5 ≤ m) : Function.Injective (sumZeroRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨i, k, hik⟩ := mclt_permCoord_pairVec_sub_ne_const hm hne
  apply hik 0
  have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m) =>
    (((g : sumZero m →ₗ[ZMod 2] sumZero m) (pairVec i k) : sumZero m) : Fin m → ZMod 2)) hσ
  simp only [sumZeroRep_apply, coe_sumZeroEquiv] at h
  rw [h]
  exact sub_self _

theorem mclt_heartRep_injective (hm : 5 ≤ m) : Function.Injective (heartRep m) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨i, k, hik⟩ := mclt_permCoord_pairVec_sub_ne_const hm hne
  have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero m ⧸ onesLine m) =>
    (g : (sumZero m ⧸ onesLine m) →ₗ[ZMod 2] (sumZero m ⧸ onesLine m))
      (Submodule.Quotient.mk (pairVec i k))) hσ
  simp only [heartRep_apply_mk, Units.val_one, Module.End.one_apply] at h
  rw [Submodule.Quotient.eq] at h
  obtain ⟨c, hc⟩ := mem_onesLine.mp h
  rw [Submodule.coe_sub, coe_sumZeroEquiv] at hc
  exact hik c hc

end CFSG.HardMathSupport.Solomon.Coordinator
