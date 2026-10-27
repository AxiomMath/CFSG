module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

theorem exists_of_zip_all {α β : Type} {l1 : List α} {l2 : List β} {p : α × β → Bool}
    (h : (l1.zip l2).all p = true) (hlen : l1.length = l2.length) {a : α} (ha : a ∈ l1) :
    ∃ b ∈ l2, p (a, b) = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ha
  have hk' : k < l2.length := hlen ▸ hk
  refine ⟨l2[k], List.getElem_mem hk', ?_⟩
  have hmem : (l1[k], l2[k]) ∈ l1.zip l2 := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp [hk, hk'], by simp⟩
  exact List.all_eq_true.1 h _ hmem

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
