module

public import CFSG.HardMathSupport.Cooperstein.Proving.EvenWeightCard

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Equiv CFSG.QuasithinUnique

theorem noncommProd_fix_of_forall {ι α : Type*} [DecidableEq ι] {f : ι → Perm α}
    (p : α) (s : Finset ι) :
    ∀ (hs : Set.Pairwise (s : Set ι) (Function.onFun Commute f)),
      (∀ j ∈ s, f j p = p) → s.noncommProd f hs p = p := by
  induction s using Finset.induction_on with
  | empty => intro hs _; simp
  | insert k s hk ih =>
    intro hs h
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hk, Equiv.Perm.mul_apply]
    rw [ih _ (fun j hj => h j (Finset.mem_insert_of_mem hj))]
    exact h k (Finset.mem_insert_self _ _)

theorem noncommProd_univ_apply {ι α : Type*} [Fintype ι] [DecidableEq ι] {f : ι → Perm α}
    (hs : Set.Pairwise (↑(Finset.univ : Finset ι) : Set ι) (Function.onFun Commute f))
    (i : ι) (p : α) (hfix : ∀ j, j ≠ i → f j p = p) :
    (Finset.univ.noncommProd f hs) p = f i p := by
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) f hs, Equiv.Perm.mul_apply]
  congr 1
  exact noncommProd_fix_of_forall p (Finset.univ.erase i) _
    (fun j hj => hfix j (Finset.ne_of_mem_erase hj))

end CFSG.HardMathSupport.Cooperstein.Proving

end
