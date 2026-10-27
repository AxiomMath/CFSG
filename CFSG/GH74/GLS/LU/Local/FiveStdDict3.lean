module

public import CFSG.GH74.GLS.LU.Local.FiveStdDict

public section

namespace CFSG.GH74.GLS.LU.Local.FiveStd

open Subgroup

open scoped Pointwise

variable {G : Type} [Group G]

omit [Group G] in
theorem S_filter {ι : E → G} {L : List E} {p : E → Bool} {Q : G → Prop}
    (h : ∀ x ∈ L, p x = true ↔ Q (ι x)) : S ι (L.filter p) = {g | g ∈ S ι L ∧ Q g} := by
  ext g
  simp only [mem_S, List.mem_filter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (h x hx).1 hp⟩
  · rintro ⟨⟨x, hx, rfl⟩, hQ⟩
    exact ⟨x, ⟨hx, (h x hx).2 hQ⟩, rfl⟩

theorem mem_dedupL (L : List E) (x : E) : x ∈ dedupL L ↔ x ∈ L := by
  have key : ∀ (L acc : List E), x ∈ L.foldl (fun acc x => if inL x acc then acc else acc ++ [x]) acc ↔
      x ∈ acc ∨ x ∈ L := by
    intro L
    induction L with
    | nil => intro acc; simp
    | cons y L ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases hy : inL y acc = true
      · simp only [hy, ↓reduceIte]
        have hy' : y ∈ acc := List.contains_iff_mem.1 hy
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
        · rintro (h | h)
          · exact Or.inl h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl hy'
            · exact Or.inr h
      · have hy' : inL y acc = false := Bool.eq_false_iff.2 hy
        simp only [hy', Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons]
        tauto
  unfold dedupL
  rw [key]
  simp

theorem fin5_mem : ∀ i : Fin 5, i ∈ allFin5 := by decide

theorem mem_allBlocks (m : Fin 5 × Fin 5 × Fin 5 × Fin 5) : m ∈ allBlocks := by
  obtain ⟨a0, a1, a2, a3⟩ := m
  simp only [allBlocks, List.mem_flatMap, List.mem_map]
  exact ⟨a0, fin5_mem _, a1, fin5_mem _, a2, fin5_mem _, a3, fin5_mem _, rfl⟩

theorem mem_Cs_iff (x : E) : x ∈ Cs ↔ validE x = true := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, s⟩ := x
  simp only [Cs, validE, isNorm, detA, detB, glBlocks, det4, List.mem_flatMap, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq, ne_eq]
  constructor
  · rintro ⟨⟨a0', a1', a2', a3'⟩, ⟨⟨_, _⟩, hnorm⟩, ⟨b0', b1', b2', b3'⟩, ⟨⟨_, _⟩, hdet⟩, hx | hx⟩ <;>
      simp only [E.mk.injEq] at hx <;> obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hx <;>
      exact ⟨hnorm, of_decide_eq_true hdet⟩
  · rintro ⟨hnorm, hdet⟩
    have hA : a0 * a3 - a1 * a2 ≠ 0 := fun h => by
      rw [h] at hdet; exact (by decide : ∀ x : Fin 5, (0 : Fin 5) * x ≠ 1) _ hdet
    have hB : b0 * b3 - b1 * b2 ≠ 0 := fun h => by
      rw [h] at hdet; exact (by decide : ∀ x : Fin 5, x * (0 : Fin 5) ≠ 1) _ hdet
    refine ⟨(a0, a1, a2, a3), ⟨⟨mem_allBlocks _, decide_eq_true hA⟩, hnorm⟩,
      (b0, b1, b2, b3), ⟨⟨mem_allBlocks _, decide_eq_true hB⟩, decide_eq_true hdet⟩, ?_⟩
    cases s
    · exact Or.inl rfl
    · exact Or.inr rfl

namespace Model

variable {ι : E → G} (hM : Model ι)
include hM

theorem closureAux_sub {gens : List E} (hgens : V gens) :
    ∀ (fuel : ℕ) (L : List E), V L → (∀ x ∈ L, ι x ∈ closure (ι '' {x | x ∈ gens})) →
      V (closureAux gens fuel L) ∧ ∀ x ∈ closureAux gens fuel L, ι x ∈ closure (ι '' {x | x ∈ gens})
  | 0, L, hL, hc => ⟨hL, hc⟩
  | fuel + 1, L, hL, hc => by
    unfold closureAux
    set L' := dedupL (L ++ L.flatMap fun x => gens.map fun g => mulE x g) with hL'
    have hmem : ∀ y, y ∈ L' ↔ y ∈ L ∨ ∃ x ∈ L, ∃ g ∈ gens, mulE x g = y := by
      intro y
      rw [hL', mem_dedupL]
      simp only [List.mem_append, List.mem_flatMap, List.mem_map]
    have hV' : V L' := by
      intro y hy
      rcases (hmem y).1 hy with h | ⟨x, hx, g, hg, rfl⟩
      · exact hL y h
      · exact hM.valid_mul _ _ (hL x hx) (hgens g hg)
    have hc' : ∀ y ∈ L', ι y ∈ closure (ι '' {x | x ∈ gens}) := by
      intro y hy
      rcases (hmem y).1 hy with h | ⟨x, hx, g, hg, rfl⟩
      · exact hc y h
      · rw [hM.map_mul _ _ (hL x hx) (hgens g hg)]
        exact Subgroup.mul_mem _ (hc x hx) (Subgroup.subset_closure ⟨g, hg, rfl⟩)
    by_cases hlen : L'.length = L.length
    · simp only [hlen, ↓reduceIte]
      exact ⟨hL, hc⟩
    · simp only [hlen, ↓reduceIte]
      exact closureAux_sub hgens fuel L' hV' hc'

theorem closureL_sub {gens : List E} (hgens : V gens) :
    V (closureL gens) ∧ ∀ x ∈ closureL gens, ι x ∈ closure (ι '' {x | x ∈ gens}) := by
  refine hM.closureAux_sub hgens 64 [oneE] ?_ ?_
  · intro x hx
    rw [List.mem_singleton.1 hx]
    exact hM.valid_one
  · intro x hx
    rw [List.mem_singleton.1 hx, hM.map_one]
    exact Subgroup.one_mem _

theorem exists_sub {L : List E} (hL : V L) (h1 : oneE ∈ L) (hm : ∀ x ∈ L, ∀ y ∈ L, mulE x y ∈ L)
    (hi : ∀ x ∈ L, invE x ∈ L) : ∃ H : Subgroup G, (H : Set G) = S ι L := by
  refine ⟨{ carrier := S ι L, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · intro a b ha hb
    obtain ⟨x, hx, rfl⟩ := mem_S.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_S.1 hb
    exact mem_S.2 ⟨mulE x y, hm x hx y hy, hM.map_mul _ _ (hL x hx) (hL y hy)⟩
  · exact mem_S.2 ⟨oneE, h1, hM.map_one⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := mem_S.1 ha
    exact mem_S.2 ⟨invE x, hi x hx, hM.map_inv _ (hL x hx)⟩

end Model

end CFSG.GH74.GLS.LU.Local.FiveStd
