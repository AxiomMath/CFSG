module

public import Certificates.Data.Kernel.MonsterB.Co2Count
public import Mathlib.Data.Fintype.BigOperators

public section

namespace CFSG.KC.Co2Mem

theorem cntK_eq_card (N : ℕ) (f : ℕ → Bool) :
    cntK N f = ((Finset.range N).filter fun k => f k = true).card := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change cntK N f + Bool.rec (motive := fun _ => ℕ) 0 1 (f N) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases hf : f N
    · simp
    · rw [ite_eq_left rfl, Finset.card_insert_of_notMem (by simp)]

theorem card_filter_fin (N : ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → Bool)
    (h : ∀ k < N, p k ↔ f k = true) :
    (Finset.univ.filter fun j : Fin N => p j.val).card = cntK N f := by
  rw [cntK_eq_card, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun k => if p k then 1 else 0)]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [h k (Finset.mem_range.1 hk)]

end CFSG.KC.Co2Mem

end
