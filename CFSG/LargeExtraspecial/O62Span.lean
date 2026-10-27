module

public import CFSG.LargeExtraspecial.O62Check

public section

namespace CFSG.LargeExtraspecial.O62

open Code Check

section Group

variable {G : Type*} [Group G]

@[expose] def spanG : List G → List G
  | [] => [1]
  | x :: xs => spanG xs ++ (spanG xs).map fun g => g * x

theorem length_spanG : ∀ xs : List G, (spanG xs).length = 2 ^ xs.length
  | [] => rfl
  | x :: xs => by
    rw [spanG, List.length_append, List.length_map, length_spanG xs, List.length_cons, pow_succ,
      mul_two]

theorem one_mem_spanG : ∀ xs : List G, (1 : G) ∈ spanG xs
  | [] => List.mem_singleton_self _
  | _ :: xs => List.mem_append_left _ (one_mem_spanG xs)

theorem mem_spanG_cons_of_mem {x : G} {xs : List G} {g : G} (h : g ∈ spanG xs) :
    g ∈ spanG (x :: xs) :=
  List.mem_append_left _ h

theorem spanG_subset {E : Subgroup G} :
    ∀ {xs : List G}, (∀ x ∈ xs, x ∈ E) → ∀ g ∈ spanG xs, g ∈ E
  | [], _, g, hg => by
    rw [spanG, List.mem_singleton] at hg
    rw [hg]
    exact one_mem E
  | x :: xs, h, g, hg => by
    rw [spanG, List.mem_append, List.mem_map] at hg
    have h' : ∀ y ∈ xs, y ∈ E := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact spanG_subset h' g hg
    · exact mul_mem (spanG_subset h' g' hg') (h x List.mem_cons_self)

theorem exists_mem_not_mem_spanG [Finite G] {P : Subgroup G} (xs : List G)
    (h : 2 ^ xs.length < Nat.card P) : ∃ x ∈ P, x ∉ spanG xs := by
  classical
  by_contra! hcon
  have hsub : (P : Set G) ⊆ ↑(spanG xs).toFinset := fun x hx => by simpa using hcon x hx
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h1
  have h2 := List.toFinset_card_le (spanG xs)
  rw [length_spanG] at h2
  omega

end Group

theorem spanC_cons (x : ℕ) (xs : List ℕ) :
    spanC (x :: xs) = spanC xs ++ (spanC xs).map fun c => Code.mul c x := rfl

@[expose] def Coded (g : V₀ ≃ₗ[ZMod 2] V₀) (c : ℕ) : Prop :=
  HasCode (g : V₀ →ₗ[ZMod 2] V₀) c ∧ c < 2 ^ 36

theorem Coded.mul {g h : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hg : Coded g a) (hh : Coded h b) :
    Coded (g * h) (Code.mul a b) :=
  ⟨hg.1.mul hh.1, mul_lt a b⟩

theorem coded_one : Coded 1 one := ⟨hasCode_one, one_lt⟩

theorem coded_wordProd (w : List ℕ) : Coded (wordProd w) (wordC w) :=
  ⟨hasCode_wordProd w, wordC_lt w⟩

theorem Coded.eq_iff {g h : V₀ ≃ₗ[ZMod 2] V₀} {a b : ℕ} (hg : Coded g a) (hh : Coded h b) :
    g = h ↔ a = b :=
  eq_iff_of_hasCode hg.1 hh.1 hg.2 hh.2

theorem forall₂_map_mul {gs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ} {x : V₀ ≃ₗ[ZMod 2] V₀}
    {c : ℕ} (h : List.Forall₂ Coded gs cs) (hx : Coded x c) :
    List.Forall₂ Coded (gs.map fun g => g * x) (cs.map fun d => Code.mul d c) := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hab.mul hx) ih

theorem forall₂_append {gs gs' : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs cs' : List ℕ}
    (h : List.Forall₂ Coded gs cs) (h' : List.Forall₂ Coded gs' cs') :
    List.Forall₂ Coded (gs ++ gs') (cs ++ cs') := by
  induction h with
  | nil => exact h'
  | cons hab _ ih => exact .cons hab ih

theorem forall₂_spanG {xs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded xs cs) : List.Forall₂ Coded (spanG xs) (spanC cs) := by
  induction h with
  | nil => exact .cons coded_one .nil
  | cons hab _ ih => exact forall₂_append ih (forall₂_map_mul ih hab)

theorem mem_iff_of_forall₂ {gs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded gs cs) {x : V₀ ≃ₗ[ZMod 2] V₀} {c : ℕ} (hx : Coded x c) :
    x ∈ gs ↔ c ∈ cs := by
  induction h with
  | nil => simp
  | cons hab _ ih => rw [List.mem_cons, List.mem_cons, hx.eq_iff hab, ih]

end CFSG.LargeExtraspecial.O62
