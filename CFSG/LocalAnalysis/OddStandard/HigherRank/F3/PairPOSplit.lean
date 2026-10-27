module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBBlock
public import CFSG.Open.StatedDefs

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit.T1.P54

@[expose] def poSplit (m : ℕ) : Fin 4 ⊕ Fin m ≃ Fin (m + 4) :=
  (Equiv.sumComm (Fin 4) (Fin m)).trans finSumFinEquiv

theorem sum_poSplit {K : Type} [AddCommMonoid K] (m : ℕ) (g : Fin (m + 4) → K) :
    ∑ k, g k = ∑ i : Fin 4, g (poSplit m (.inl i)) + ∑ j : Fin m, g (poSplit m (.inr j)) := by
  rw [← (poSplit m).sum_comp, Fintype.sum_sum_type]

@[expose] def poSplitPlus (m : ℕ) :
    (Fin 4 ⊕ Fin 4) ⊕ (Fin m ⊕ Fin m) ≃ Fin (m + 4) ⊕ Fin (m + 4) :=
  (Equiv.sumSumSumComm _ _ _ _).trans (Equiv.sumCongr (poSplit m) (poSplit m))

theorem pullQ_poSplitPlus {K : Type} [Field K] (m : ℕ) :
    DB.pullQ (poSplitPlus m) (StatedQuadPlus (m + 4) K) =
      DB.sumQ (StatedQuadPlus 4 K) (StatedQuadPlus m K) := by
  funext v
  have h1 : ∀ x, (poSplitPlus m).symm (.inl (poSplit m x)) =
      Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j)) x := by
    rintro (i | j) <;> rw [Equiv.symm_apply_eq] <;> rfl
  have h2 : ∀ x, (poSplitPlus m).symm (.inr (poSplit m x)) =
      Sum.elim (fun i => .inl (.inr i)) (fun j => .inr (.inr j)) x := by
    rintro (i | j) <;> rw [Equiv.symm_apply_eq] <;> rfl
  simp only [DB.pullQ, DB.sumQ, StatedQuadPlus, Function.comp_apply]
  rw [sum_poSplit m]
  simp only [h1, h2, Sum.elim_inl, Sum.elim_inr]

@[expose] def poSplitD (m : ℕ) (D : Type) :
    (Fin 4 ⊕ Fin 4) ⊕ (Fin m ⊕ Fin m ⊕ D) ≃ Fin (m + 4) ⊕ Fin (m + 4) ⊕ D :=
  (Equiv.sumSumSumComm (Fin 4) (Fin 4) (Fin m) (Fin m ⊕ D)).trans
    (Equiv.sumCongr (poSplit m)
      ((Equiv.sumAssoc (Fin 4) (Fin m) D).symm.trans
        (Equiv.sumCongr (poSplit m) (Equiv.refl D))))

theorem poSplitD_symm_inl (m : ℕ) (D : Type) (x : Fin 4 ⊕ Fin m) :
    (poSplitD m D).symm (.inl (poSplit m x)) =
      Sum.elim (fun i => .inl (.inl i)) (fun j => .inr (.inl j)) x := by
  rcases x with i | j <;> rw [Equiv.symm_apply_eq] <;> rfl

theorem poSplitD_symm_inr_inl (m : ℕ) (D : Type) (x : Fin 4 ⊕ Fin m) :
    (poSplitD m D).symm (.inr (.inl (poSplit m x))) =
      Sum.elim (fun i => .inl (.inr i)) (fun j => .inr (.inr (.inl j))) x := by
  rcases x with i | j <;> rw [Equiv.symm_apply_eq] <;> rfl

theorem poSplitD_symm_inr_inr (m : ℕ) (D : Type) (d : D) :
    (poSplitD m D).symm (.inr (.inr d)) = .inr (.inr (.inr d)) := by
  rw [Equiv.symm_apply_eq]
  rfl

theorem pullQ_poSplitOdd {K : Type} [Field K] (m : ℕ) :
    DB.pullQ (poSplitD m Unit) (StatedQuadOdd (m + 4) K) =
      DB.sumQ (StatedQuadPlus 4 K) (StatedQuadOdd m K) := by
  funext v
  simp only [DB.pullQ, DB.sumQ, StatedQuadOdd, StatedQuadPlus, Function.comp_apply]
  rw [sum_poSplit m]
  simp only [poSplitD_symm_inl, poSplitD_symm_inr_inl, poSplitD_symm_inr_inr, Sum.elim_inl,
    Sum.elim_inr]
  ring

@[expose] def poSplitMinus (m : ℕ) : (Fin 4 ⊕ Fin 4) ⊕
    (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) ≃ Fin (m + 5 - 1) ⊕ Fin (m + 5 - 1) ⊕ Fin 2 :=
  poSplitD m (Fin 2)

theorem pullQ_poSplitMinus {K : Type} [Field K] (m : ℕ) (b c : K) :
    DB.pullQ (poSplitMinus m) (StatedQuadMinus (m + 5) K b c) =
      DB.sumQ (StatedQuadPlus 4 K) (StatedQuadMinus (m + 1) K b c) := by
  funext v
  have hsum : ∀ g : Fin (m + 5 - 1) → K, ∑ k, g k =
      ∑ i : Fin 4, g (poSplit m (.inl i)) + ∑ j : Fin m, g (poSplit m (.inr j)) :=
    fun g => sum_poSplit m g
  have hS : ∀ f : Fin m → K, ∑ x : Fin m, f x = ∑ x : Fin (m + 1 - 1), f x := fun f => rfl
  simp only [DB.pullQ, DB.sumQ, StatedQuadMinus, StatedQuadPlus, Function.comp_apply, poSplitMinus]
  rw [hsum]
  simp only [poSplitD_symm_inl, poSplitD_symm_inr_inl, poSplitD_symm_inr_inr, Sum.elim_inl,
    Sum.elim_inr]
  rw [hS]
  ring

end CFSG.OddStandard.HigherRank.F3
