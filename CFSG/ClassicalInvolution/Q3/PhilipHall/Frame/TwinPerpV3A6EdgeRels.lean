module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SEdge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
open scoped commutatorElement

theorem comm_eq_one_symm {G : Type*} [Group G] {x y : G} (h : ⁅x, y⁆ = 1) : ⁅y, x⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.2 (commutatorElement_eq_one_iff_commute.1 h).symm

theorem curtisRelations_comp {G : Type*} [Group G] {a b : ℕ → G} (h : CurtisRelations a b)
    (σ : ℕ → ℕ) (hr : ∀ i < 4, σ i < 4)
    (hn : ∀ p ∈ ([(0, 2), (0, 3), (2, 3)] : List (ℕ × ℕ)),
      (σ p.1, σ p.2) ∈ ([(0, 2), (0, 3), (2, 3)] : List (ℕ × ℕ)) ∨
        (σ p.2, σ p.1) ∈ ([(0, 2), (0, 3), (2, 3)] : List (ℕ × ℕ)))
    (ha : ∀ p ∈ ([(0, 1), (2, 1), (3, 1)] : List (ℕ × ℕ)),
      (σ p.1, σ p.2) ∈ ([(0, 1), (2, 1), (3, 1)] : List (ℕ × ℕ))) :
    CurtisRelations (fun i => a (σ i)) (fun i => b (σ i)) where
  rank_one i hi := h.rank_one (σ i) (hr i hi)
  non_adj p hp := by
    rcases hn p hp with hq | hq
    · exact h.non_adj _ hq
    · obtain ⟨h1, h2, h3, h4⟩ := h.non_adj _ hq
      exact ⟨comm_eq_one_symm h1, comm_eq_one_symm h3, comm_eq_one_symm h2, comm_eq_one_symm h4⟩
  adj p hp := h.adj _ (ha p hp)

@[expose] def edgeNode (k : Fin 3) (i : ℕ) : ℕ :=
  if i < 4 then (![![0, 1, 3, 2], ![2, 1, 0, 3], ![3, 1, 2, 0]] k) ⟨i % 4, Nat.mod_lt _ (by omega)⟩ else i

theorem getD_ofFn_eight {α : Type*} (f : Fin 8 → α) (d : α) {j : ℕ} (hj : j < 8) :
    (List.ofFn f).getD j d = f ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]

theorem getD_ofFn_ge {α : Type*} (f : Fin 8 → α) (d : α) {j : ℕ} (hj : 8 ≤ j) :
    (List.ofFn f).getD j d = d := by
  rw [List.getD_eq_default _ _ (by simpa using hj)]

theorem edgeSwap_node (k : Fin 3) (i : ℕ) (hi : i < 4) (t : ℕ) (ht : t < 2) :
    (ae6EdgeSwap k ⟨2 * i + t, by omega⟩).val = 2 * edgeNode k i + t := by
  unfold edgeNode
  rw [if_pos hi]
  interval_cases i <;> interval_cases t <;> fin_cases k <;> rfl

theorem edgeSwap_getD (k : Fin 3) (i t : ℕ) (ht : t < 2) :
    (List.ofFn fun j => curtisGen (ae6EdgeSwap k j)).getD (2 * i + t) 1 =
      (List.ofFn curtisGen).getD (2 * edgeNode k i + t) 1 := by
  by_cases hi : i < 4
  · rw [getD_ofFn_eight _ _ (by omega), getD_ofFn_eight _ _ (by
      have := edgeSwap_node k i hi t ht
      have h8 := (ae6EdgeSwap k ⟨2 * i + t, by omega⟩).isLt
      omega)]
    congr 1
    exact Fin.ext (edgeSwap_node k i hi t ht)
  · have he : edgeNode k i = i := by
      unfold edgeNode
      rw [if_neg hi]
    rw [he, getD_ofFn_ge _ _ (by omega), getD_ofFn_ge _ _ (by omega)]

theorem curtisRels_edgeSwap (k : Fin 3) :
    ∀ r ∈ curtisRels, curtisEval (List.ofFn fun i => curtisGen (ae6EdgeSwap k i)) r = 1 := by
  refine (curtisRels_iff _).2 ?_
  have h := curtisRelations_comp curtisRelations_curtisGen (edgeNode k) (fun i hi => by
      unfold edgeNode
      rw [if_pos hi]
      interval_cases i <;> fin_cases k <;> decide)
    (by fin_cases k <;> decide) (by fin_cases k <;> decide)
  have ea : (fun i => (List.ofFn fun j => curtisGen (ae6EdgeSwap k j)).getD (2 * i) 1) =
      fun i => (List.ofFn curtisGen).getD (2 * edgeNode k i) 1 := by
    funext i
    have := edgeSwap_getD k i 0 (by omega)
    simpa using this
  have eb : (fun i => (List.ofFn fun j => curtisGen (ae6EdgeSwap k j)).getD (2 * i + 1) 1) =
      fun i => (List.ofFn curtisGen).getD (2 * edgeNode k i + 1) 1 := by
    funext i
    exact edgeSwap_getD k i 1 (by omega)
  rw [ea, eb]
  exact h

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
