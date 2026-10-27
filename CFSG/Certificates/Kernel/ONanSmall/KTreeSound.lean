module

public import Certificates.Data.Kernel.ONanSmall.KTree
public import CFSG.Certificates.Kernel.ONanSmall.PickRunSound
public import Mathlib.Tactic.Group

public section

namespace CFSG.KC.ONanSmall

namespace KTree

variable {α : Type} (key : α → Nat)

theorem mem_of_memK [DecidableEq α] {y : α} :
    ∀ {t : KTree α}, memK key y t = true → y ∈ toList t
  | leaf, h => by simp [memK] at h
  | node l x r, h => by
    unfold memK at h
    simp only [toList, List.mem_append, List.mem_cons]
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact Or.inr (Or.inl (of_decide_eq_true h))
    · split at h
      · exact Or.inl (mem_of_memK h)
      · exact Or.inr (Or.inr (mem_of_memK h))

theorem mem_insert {y z : α} :
    ∀ {t : KTree α}, z ∈ toList (insert key y t) → z = y ∨ z ∈ toList t
  | leaf, h => by simpa [insert, toList] using h
  | node l x r, h => by
    unfold insert at h
    split at h
    · simp only [toList, List.mem_append, List.mem_cons] at h ⊢
      rcases h with h | h | h
      · rcases mem_insert h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · simp only [toList, List.mem_append, List.mem_cons] at h ⊢
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases mem_insert h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))

theorem mem_foldl_insert {z : α} : ∀ (L : List α) (t : KTree α),
    z ∈ toList (L.foldl (fun t y => insert key y t) t) → z ∈ L ∨ z ∈ toList t
  | [], _, h => Or.inr h
  | y :: L, t, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_insert L _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases mem_insert key h with h | h
      · rw [h]
        exact Or.inl (List.mem_cons.2 (Or.inl rfl))
      · exact Or.inr h

theorem mem_of_memK_ofList [DecidableEq α] {L : List α} {y : α}
    (h : memK key y (ofList key L) = true) : y ∈ L := by
  rcases mem_foldl_insert key L leaf (mem_of_memK key h) with h | h
  · exact h
  · simp [toList] at h

end KTree

variable {M : Type*} [Group M] [DecidableEq M]

theorem conj_mem_productsOf {K : List M} : ∀ (Ts : List (List M)),
    (∀ T ∈ Ts, ∀ u ∈ T, ∀ k ∈ K, u⁻¹ * k * u ∈ K) →
      ∀ g ∈ productsOf Ts, ∀ k ∈ K, g⁻¹ * k * g ∈ K
  | [], _, g, hg, k, hk => by
    simp only [productsOf, List.mem_singleton] at hg
    rw [hg, inv_one, one_mul, mul_one]
    exact hk
  | T :: Ts, h, g, hg, k, hk => by
    unfold productsOf at hg
    obtain ⟨t, ht, htx⟩ := List.mem_flatMap.1 hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 htx
    have e : (t * x)⁻¹ * k * (t * x) = x⁻¹ * (t⁻¹ * k * t) * x := by group
    rw [e]
    exact conj_mem_productsOf Ts (fun T' hT' => h T' (List.mem_cons_of_mem _ hT')) x hx _
      (h T (List.mem_cons.2 (Or.inl rfl)) t ht k hk)

end CFSG.KC.ONanSmall
