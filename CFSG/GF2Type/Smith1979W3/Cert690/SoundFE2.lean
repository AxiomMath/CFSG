module

public import CFSG.GF2Type.Smith1979W3.Cert690.Dict

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem parent_reach {α : Type*} (mul : α → α → α) (one : α) (gens : List α) (E : ℕ → α)
    (p q : ℕ → ℕ) (n : ℕ)
    (h0 : E 0 = one)
    (hp : ∀ i, 0 < i → i < n → p i < i)
    (hq : ∀ i, 0 < i → i < n → q i < gens.length)
    (hE : ∀ i, 0 < i → i < n → E i = mul (E (p i)) (gens.getD (q i) one)) :
    ∀ i, i < n → ∃ w : List ℕ, (∀ j ∈ w, j < gens.length) ∧
      E i = (w.map fun j => gens.getD j one).foldl mul one := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact ⟨[], by simp, by rw [h0]; rfl⟩
    · have hi0' : 0 < i := Nat.pos_of_ne_zero hi0
      have hpi : p i < i := hp i hi0' hi
      obtain ⟨w, hw, hweq⟩ := ih (p i) hpi (Nat.lt_trans hpi hi)
      refine ⟨w ++ [q i], ?_, ?_⟩
      · intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · exact hw j hj
        · rw [List.mem_singleton] at hj
          subst hj
          exact hq i hi0' hi
      · rw [List.map_append, List.map_singleton, List.foldl_append, ← hweq, hE i hi0' hi]
        rfl

theorem enum_reach {gens : List ℕ} {E : Array ℕ} {par : Array (ℕ × ℕ)}
    (h0 : E[0]! = Code.one)
    (hpar : ∀ i, i ≠ 0 → i < E.size →
      par[i]!.1 < i ∧ par[i]!.2 < gens.length ∧
        E[i]! = Code.mul (E[par[i]!.1]!) (gens[par[i]!.2]!)) :
    ∀ i, i < E.size → ∃ w : List ℕ, (∀ j ∈ w, j < gens.length) ∧
      E[i]! = (w.map fun j => gens[j]!).foldl Code.mul Code.one := by
  classical
  let F : ℕ → ℕ := fun i => E[i]!
  let p : ℕ → ℕ := fun i => par[i]!.1
  let q : ℕ → ℕ := fun i => par[i]!.2
  have hF0 : F 0 = Code.one := h0
  have hp : ∀ i, 0 < i → i < E.size → p i < i := by
    intro i hi0 hi
    exact (hpar i (Nat.ne_of_gt hi0) hi).1
  have hq : ∀ i, 0 < i → i < E.size → q i < gens.length := by
    intro i hi0 hi
    exact (hpar i (Nat.ne_of_gt hi0) hi).2.1
  have hstep : ∀ i, 0 < i → i < E.size →
      F i = Code.mul (F (p i)) (gens.getD (q i) Code.one) := by
    intro i hi0 hi
    have hpar_i := hpar i (Nat.ne_of_gt hi0) hi
    have hqi : q i < gens.length := hpar_i.2.1
    have hgd : gens.getD (q i) Code.one = gens[q i]! := by
      rw [List.getD_eq_getElem (l := gens) (d := Code.one) (n := q i) hqi,
        getElem!_eq_getElem_of_lt hqi]
    show E[i]! = Code.mul (E[p i]!) (gens.getD (q i) Code.one)
    rw [hgd]
    exact hpar_i.2.2
  have hmain := parent_reach (mul := Code.mul) (one := Code.one) (gens := gens) (E := F)
    (p := p) (q := q) (n := E.size) hF0 hp hq hstep
  intro i hi
  obtain ⟨w, hw, hweq⟩ := hmain i hi
  refine ⟨w, hw, ?_⟩
  have hmap : w.map (fun j => gens.getD j Code.one) = w.map (fun j => gens[j]!) := by
    apply List.map_congr_left
    intro j hj
    rw [List.getD_eq_getElem (l := gens) (d := Code.one) (n := j) (hw j hj),
      getElem!_eq_getElem_of_lt (hw j hj)]
  rw [← hmap]
  exact hweq

end CFSG.GF2Type.Smith1979W3.Cert690

end

