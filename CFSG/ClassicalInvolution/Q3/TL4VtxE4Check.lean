module

public import Certificates.Data.E4QuatCheck
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4C

open CFSG.ClassicalInvolution.Generic CFSG.Sporadic.Schreier

variable {n : ℕ}

theorem mem_closure_iff {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hc : closedL L i j = true) (hsub : ∀ x ∈ L, x ∈ Subgroup.closure ({i, j} : Set _))
    (x : Equiv.Perm (Fin n)) : x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L := by
  simp only [closedL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  refine ⟨fun hx => ?_, hsub x⟩
  induction hx using Subgroup.closure_induction_left with
  | one => exact hc.1
  | mul_left a ha y _ hy =>
    rcases ha with rfl | rfl
    · exact (hc.2 y hy).1.1.1
    · exact (hc.2 y hy).1.1.2
  | inv_mul_cancel a ha y _ hy =>
    rcases ha with rfl | rfl
    · exact (hc.2 y hy).1.2
    · exact (hc.2 y hy).2

theorem q8Elems_sub {r i j : Equiv.Perm (Fin n)} (hr : i * i = r) :
    ∀ x ∈ q8Elems r i j, x ∈ Subgroup.closure ({i, j} : Set _) := by
  have hi : i ∈ Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hj : j ∈ Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hrK : r ∈ Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) :=
    hr ▸ Subgroup.mul_mem _ hi hi
  intro x hx
  simp only [q8Elems, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hrK
  · exact hi
  · exact Subgroup.mul_mem _ hi hrK
  · exact hj
  · exact Subgroup.mul_mem _ hj hrK
  · exact Subgroup.mul_mem _ hi hj
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hi hj) hrK

theorem conjSub_eq_of_norms {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L) {h : Equiv.Perm (Fin n)}
    (hn : norms L i j h = true) :
    conjSub h (Subgroup.closure ({i, j} : Set _)) = Subgroup.closure ({i, j} : Set _) := by
  simp only [norms, Bool.and_eq_true, decide_eq_true_eq] at hn
  have hle : conjSub h (Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n)))) ≤
      Subgroup.closure ({i, j} : Set _) := by
    unfold conjSub
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact (hiff _).mpr hn.1
    · exact (hiff _).mpr hn.2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Vtx.natCard_conjSub])

theorem norms_of_conjSub_eq {L : List (Equiv.Perm (Fin n))} {i j : Equiv.Perm (Fin n)}
    (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L) {h : Equiv.Perm (Fin n)}
    (he : conjSub h (Subgroup.closure ({i, j} : Set _)) = Subgroup.closure ({i, j} : Set _)) :
    norms L i j h = true := by
  simp only [norms, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rw [← hiff, ← he]
    exact conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert _ _))
  · rw [← hiff, ← he]
    exact conj_mem_conjSub (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem getD_letters_of_mem {gens : List (Equiv.Perm (Fin n))} {x : Equiv.Perm (Fin n)}
    (hx : x ∈ gens) : ∃ l < (letters gens).length, (letters gens).getD l 1 = x ∧
      (letters gens).getD (l + gens.length) 1 = x⁻¹ ∧ l + gens.length < (letters gens).length := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hx
  refine ⟨l, by simp [letters]; omega, ?_, ?_, by simp [letters]; omega⟩
  · rw [letters, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hl]
  · rw [letters, List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_right (by omega)]
    simp

theorem exists_member_of_memberCheck {gens L : List (Equiv.Perm (Fin n))}
    {i j : Equiv.Perm (Fin n)} (hiff : ∀ x, x ∈ Subgroup.closure ({i, j} : Set _) ↔ x ∈ L)
    {ws : List (Equiv.Perm (Fin n))} {σ : List (List ℕ)}
    (hc : memberCheck gens L i j ws σ = true) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Subgroup.closure {x | x ∈ gens}) :
    ∃ k < ws.length, conjSub g (Subgroup.closure ({i, j} : Set _)) =
      conjSub (ws.getD k 1) (Subgroup.closure ({i, j} : Set _)) := by
  simp only [memberCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hc
  obtain ⟨⟨hlen, h0⟩, hc⟩ := hc
  set K := Subgroup.closure ({i, j} : Set (Equiv.Perm (Fin n))) with hK
  have step : ∀ k < ws.length, ∀ l < (letters gens).length, ∃ t < ws.length,
      conjSub ((letters gens).getD l 1 * ws.getD k 1) K = conjSub (ws.getD t 1) K := by
    intro k hk l hl
    obtain ⟨ht, hn⟩ := hc k hk l hl
    refine ⟨_, ht, ?_⟩
    have he := conjSub_eq_of_norms hiff hn
    calc conjSub ((letters gens).getD l 1 * ws.getD k 1) K =
        conjSub (ws.getD ((σ.getD k []).getD l 0) 1) (conjSub ((ws.getD
          ((σ.getD k []).getD l 0) 1)⁻¹ * (letters gens).getD l 1 * ws.getD k 1) K) := by
          rw [← conjSub_mul]
          congr 1
          group
      _ = _ := by rw [he]
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, hlen, by rw [h0]⟩
  | mul_left x hx y _ hy =>
    obtain ⟨k, hk, hke⟩ := hy
    obtain ⟨l, hl, hlx, -, -⟩ := getD_letters_of_mem hx
    obtain ⟨t, ht, hte⟩ := step k hk l hl
    refine ⟨t, ht, ?_⟩
    rw [conjSub_mul, hke, ← conjSub_mul, ← hlx, hte]
  | inv_mul_cancel x hx y _ hy =>
    obtain ⟨k, hk, hke⟩ := hy
    obtain ⟨l, -, -, hlx, hl⟩ := getD_letters_of_mem hx
    obtain ⟨t, ht, hte⟩ := step k hk _ hl
    refine ⟨t, ht, ?_⟩
    rw [conjSub_mul, hke, ← conjSub_mul, ← hlx, hte]

end CFSG.ClassicalInvolution.Q3.TL4.E4C
