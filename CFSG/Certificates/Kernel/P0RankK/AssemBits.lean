module

public import CFSG.Certificates.Kernel.P0RankK.OrbForms
public import Mathlib.Algebra.Order.Ring.Nat

public section

namespace CFSG.KC.P0Orb

open MonsterB.P0Rank

theorem chunks_all {α : Type} (S : ℕ → List α → Bool) (P : ℕ → α → Prop)
    (hS : ∀ (rows : List α) (r₀ : ℕ), S r₀ rows = true → ∀ t (ht : t < rows.length),
      P (r₀ + t) rows[t])
    {rows : List α} {lo g n : ℕ} (hg : 0 < g)
    (hck : ∀ i < n, S (lo + g * i) ((rows.drop (g * i)).take g) = true)
    (hlen : rows.length ≤ g * n) : ∀ t (ht : t < rows.length), P (lo + t) rows[t] := by
  intro t ht
  have hi : t / g < n := by
    rw [Nat.div_lt_iff_lt_mul hg]
    calc t < rows.length := ht
      _ ≤ g * n := hlen
      _ = n * g := Nat.mul_comm g n
  have hu : t % g < g := Nat.mod_lt t hg
  have ht' : g * (t / g) + t % g = t := Nat.div_add_mod t g
  have hlt : t % g < ((rows.drop (g * (t / g))).take g).length := by
    rw [List.length_take, List.length_drop]
    omega
  have h := hS _ _ (hck (t / g) hi) (t % g) hlt
  rw [List.getElem_take, List.getElem_drop] at h
  have e1 : lo + g * (t / g) + t % g = lo + t := by omega
  rw [e1] at h
  have e2 : rows[g * (t / g) + t % g] = rows[t] := by
    congr 1
  rw [← e2]
  exact h

theorem repsOK_spec {AT RT BC BU : ℕ} : ∀ (rows : List Row) (r₀ : ℕ),
    repsOK AT RT BC BU r₀ rows = true → ∀ t (ht : t < rows.length),
      repOK AT RT BC BU (r₀ + t) rows[t] = true
  | [], _, _, t, ht => absurd ht (by simp)
  | row :: rows, r₀, h, t, ht => by
    rw [repsOK, Bool.and_eq_true] at h
    cases t with
    | zero => exact h.1
    | succ t =>
      have := repsOK_spec rows (r₀ + 1) h.2 t (by simpa using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

theorem bcOK_sound {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) :
    (∀ x < 2 ^ 16, ∀ y < 2 ^ 16, bet BC x y = betaN beta x y) ∧
      ∀ x < 2 ^ 16, qf BU x = qN beta x := by
  obtain ⟨hlen, hC, hU⟩ := p0b_bc_facts h
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [bet, p0b_pp BC x y hx hy, betaN]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    congr 1
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, hlen i hi']
    · intro n h1 h2
      rw [List.getElem_map, List.getElem_range, hC i hi' n (by simpa using h1),
        List.getD_eq_getElem _ _ h2]
  · have hA : qf BU x = p0bXS 16 (fun k => p0bXS 16 (fun j =>
        if x.testBit k then if x.testBit j then
          (if k < j then (beta.getD j []).getD k 0 else 0) else 0 else 0)) := by
      rw [qf, p0b_pp BU x x hx hx, p0b_colsAct_eq, List.length_map, List.length_range]
      refine p0bXS_congr fun k hk => ?_
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range,
        p0b_colsAct_eq, List.length_map, List.length_range, p0bXS_ite]
      refine p0bXS_congr fun j hj => ?_
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
        hU k hk j hj]
    have hB : qN beta x = p0bXS 16 (fun j => p0bXS 16 (fun k =>
        if x.testBit j then (if k < j then (if x.testBit k then (beta.getD j []).getD k 0 else 0)
          else 0) else 0)) := by
      rw [qN, p0b_foldl]
      refine p0bXS_congr fun j hj => ?_
      rw [p0b_colsAct_eq, List.length_take, hlen j hj, Nat.min_eq_left (by omega),
        ← p0bXS_lt _ 16 (by omega), p0bXS_ite]
      refine p0bXS_congr fun k hk => ?_
      by_cases hkj : k < j
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_take, hlen j hj]; omega),
          List.getElem_take, ← List.getD_eq_getElem _ 0]
      · simp [hkj]
    rw [hA, hB, p0bXS_swap]
    refine p0bXS_congr fun j _ => p0bXS_congr fun k _ => ?_
    split_ifs <;> rfl

end CFSG.KC.P0Orb

end
