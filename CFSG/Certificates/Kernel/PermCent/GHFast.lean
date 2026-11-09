module

public import CFSG.Certificates.Kernel.PermCent.FastDecide

public section

namespace CFSG.Certificates.Kernel.PkCV

open Equiv Equiv.Perm

@[expose] noncomputable def allPL (m : ℕ) [hs : Small m] : List (Perm (Fin m)) :=
  (allPermsP m hs).map fun x => ev x.1

theorem mem_allPL {m : ℕ} [hs : Small m] (σ : Perm (Fin m)) : σ ∈ allPL m := by
  obtain ⟨x, hx, rfl⟩ := exists_mem_allPermsP hs σ
  exact List.mem_map_of_mem hx

theorem forall_of_mem_filter_allPL {m : ℕ} [Small m] {p : Perm (Fin m) → Bool}
    {P : Perm (Fin m) → Prop} (h : ∀ x ∈ (allPL m).filter p, P x) :
    ∀ x, p x = true → P x :=
  fun x hx => h x (List.mem_filter.2 ⟨mem_allPL x, hx⟩)

theorem mem_filter_allPL_of_forall {m : ℕ} [Small m] {p : Perm (Fin m) → Bool}
    {P : Perm (Fin m) → Prop} (h : ∀ x, p x = true → P x) :
    ∀ x ∈ (allPL m).filter p, P x :=
  fun x hx => h x (List.mem_filter.1 hx).2

theorem mem_filter_allPL {m : ℕ} [Small m] {p : Perm (Fin m) → Bool} {x : Perm (Fin m)} :
    x ∈ (allPL m).filter p ↔ p x = true := by
  rw [List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPL x, h⟩⟩

open scoped FastDecide in
theorem univ_filter_eq_allPL {m : ℕ} [Small m] (p : Perm (Fin m) → Prop) [DecidablePred p] :
    Finset.univ.filter p = ((allPL m).filter fun x => decide (p x)).toFinset := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, mem_filter_allPL,
    decide_eq_true_eq]

open scoped FastDecide in
theorem card_subtype_eq_allPL {m : ℕ} [Small m] (p : Perm (Fin m) → Prop) [DecidablePred p]
    [Fintype {x // p x}] :
    Fintype.card {x // p x} = ((allPL m).filter fun x => decide (p x)).toFinset.card := by
  rw [Fintype.card_subtype, univ_filter_eq_allPL]

open scoped FastDecide in
theorem card_subtype_eq_length {m : ℕ} [Small m] (hnd : (allPL m).Nodup)
    (p : Perm (Fin m) → Prop) [DecidablePred p] [Fintype {x // p x}] :
    Fintype.card {x // p x} = ((allPL m).filter fun x => decide (p x)).length := by
  rw [card_subtype_eq_allPL, List.toFinset_card_of_nodup (hnd.filter _)]

theorem decide_eq_permBEq {n : ℕ} (a b : Perm (Fin n)) [Decidable (a = b)] :
    decide (a = b) = permBEq a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, permBEq_iff]

namespace FastDecide

scoped instance (priority := 20001) decBAllFinset {α : Type*} (p : α → Prop) [DecidablePred p]
    (s : Finset α) : Decidable (∀ x, x ∈ s → p x) :=
  Finset.decidableDforallFinset

end FastDecide

end CFSG.Certificates.Kernel.PkCV

end
