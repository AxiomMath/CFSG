module

public import CFSG.Combinatorics.AperiodicCentralInvolutionSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

section Cycle

variable {V : Type*} {G : SimpleGraph V} {v : V} (C : G.Walk v v)

def cycVert (n : ℕ) : V :=
  C.getVert (n % 12)

theorem cycVert_add_twelve (n : ℕ) : cycVert C (n + 12) = cycVert C n := by
  simp [cycVert, Nat.add_mod_right]

theorem adj_cycVert (hl : C.length = 12) (n : ℕ) : G.Adj (cycVert C n) (cycVert C (n + 1)) := by
  unfold cycVert
  by_cases h : n % 12 = 11
  · have h12 := C.adj_getVert_succ (i := 11) (by omega)
    rw [show 11 + 1 = C.length by omega, SimpleGraph.Walk.getVert_length] at h12
    rw [h, show (n + 1) % 12 = 0 by omega, SimpleGraph.Walk.getVert_zero]
    exact h12
  · rw [show (n + 1) % 12 = n % 12 + 1 by omega]
    exact C.adj_getVert_succ (by omega)

theorem cycVert_inj (hC : C.IsCycle) (hl : C.length = 12) {m n : ℕ}
    (h : cycVert C m = cycVert C n) : m % 12 = n % 12 :=
  hC.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega) h

theorem exists_cycVert (hl : C.length = 12) {u : V} (hu : u ∈ C.support) :
    ∃ n < 12, cycVert C n = u := by
  obtain ⟨n, rfl, hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu
  by_cases h : n = 12
  · refine ⟨0, by norm_num, ?_⟩
    rw [cycVert, h, ← hl, SimpleGraph.Walk.getVert_length, Nat.zero_mod,
      SimpleGraph.Walk.getVert_zero]
  · exact ⟨n, by omega, by rw [cycVert, Nat.mod_eq_of_lt (by omega)]⟩

theorem col_cycVert_add_two (hl : C.length = 12) (col : G.Coloring Bool) (n : ℕ) :
    col (cycVert C (n + 2)) = col (cycVert C n) := by
  have h1 := col.valid (adj_cycVert C hl n)
  have h2 := col.valid (adj_cycVert C hl (n + 1))
  revert h1 h2
  cases col (cycVert C n) <;> cases col (cycVert C (n + 1)) <;> cases col (cycVert C (n + 1 + 1))
    <;> simp

theorem col_cycVert_mod_two (hl : C.length = 12) (col : G.Coloring Bool) (n : ℕ) :
    col (cycVert C n) = col (cycVert C (n % 2)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      rw [col_cycVert_add_two C hl, ih k (by omega), show (k + 2) % 2 = k % 2 by omega]

end Cycle

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)

include F in
theorem exists_hexagon_of_isCycle {v : V} {C : G.Walk v v} (hC : C.IsCycle)
    (hl : C.length = 12) :
    ∃ pt : ℕ → {v : V // col v = false}, (∀ t, pt t = pt (t % 6)) ∧
      (∀ t, (pointGraph G col).Adj (pt t) (pt (t + 1))) ∧
      (∀ t t', pt t = pt t' → t % 6 = t' % 6) ∧
      ∀ x : {v : V // col v = false}, (x : V) ∈ C.support ↔ ∃ t < 6, pt t = x := by
  obtain ⟨s, hs, hpar⟩ : ∃ s, s < 2 ∧ ∀ n, col (cycVert C n) = false ↔ n % 2 = s := by
    have h01 := col.valid (adj_cycVert C hl 0)
    rcases Bool.eq_false_or_eq_true (col (cycVert C 0)) with h0 | h0
    · refine ⟨1, by norm_num, fun n => ?_⟩
      rw [col_cycVert_mod_two C hl]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp_all
    · refine ⟨0, by norm_num, fun n => ?_⟩
      rw [col_cycVert_mod_two C hl]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp_all
  have hpt : ∀ t, col (cycVert C (s + 2 * (t % 6))) = false := fun t => (hpar _).mpr (by omega)
  let pt : ℕ → {v : V // col v = false} := fun t => ⟨cycVert C (s + 2 * (t % 6)), hpt t⟩
  have hcyc : ∀ {m n : ℕ}, m % 12 = n % 12 → cycVert C m = cycVert C n := fun h => by
    rw [cycVert, cycVert, h]
  refine ⟨pt, fun t => Subtype.ext (by simp [pt]), fun t => ?_, fun t t' h => ?_,
    fun x => ⟨fun hx => ?_, ?_⟩⟩
  ·
    have hm : (pt (t + 1) : V) = cycVert C (s + 2 * (t % 6) + 1 + 1) := hcyc (by omega)
    rw [point_adj_iff F.moore.conn col, hm]
    refine dist_eq_two_of_adj_adj F.moore.conn col (fun h => ?_) ((hpt t).trans
      ((hpar _).mpr (by omega)).symm) (adj_cycVert C hl _)
      (adj_cycVert C hl (s + 2 * (t % 6) + 1)).symm
    have := cycVert_inj C hC hl h
    omega
  · have := cycVert_inj C hC hl (congrArg Subtype.val h)
    omega
  · obtain ⟨n, hn, hnx⟩ := exists_cycVert C hl hx
    have hn2 : n % 2 = s := (hpar n).mp (by rw [hnx]; exact x.2)
    refine ⟨n / 2, by omega, Subtype.ext ?_⟩
    rw [← hnx]
    exact hcyc (by omega)
  · rintro ⟨t, -, rfl⟩
    exact C.getVert_mem_support _

include F hr haper in
theorem mem_of_five {q₀ q₁ q₂ q₃ q₄ q₅ : {v : V // col v = false}} (h₀ : q₀ ∈ oppSet G col w)
    (h₁ : q₁ ∈ oppSet G col w) (h₂ : q₂ ∈ oppSet G col w) (h₃ : q₃ ∈ oppSet G col w)
    (h₄ : q₄ ∈ oppSet G col w) (a01 : (pointGraph G col).Adj q₀ q₁)
    (a12 : (pointGraph G col).Adj q₁ q₂) (a23 : (pointGraph G col).Adj q₂ q₃)
    (a34 : (pointGraph G col).Adj q₃ q₄) (a45 : (pointGraph G col).Adj q₄ q₅)
    (a50 : (pointGraph G col).Adj q₅ q₀) (n02 : q₀ ≠ q₂) (n03 : q₀ ≠ q₃) (n13 : q₁ ≠ q₃) :
    q₅ ∈ oppSet G col w := by
  have hd := point_dist_eq_iff F.moore.conn col
  have hA := point_adj_iff F.moore.conn col
  have d30 : G.dist (q₃ : V) q₀ = 6 := (hd _ _ 3).mp
    (dist_eq_three_of_path F h₃ h₂ h₁ h₀ a23.symm a12.symm a01.symm n13.symm n02.symm)
  have d34 : G.dist (q₃ : V) q₄ = 2 := (hA _ _).mp a34
  have d45 : G.dist (q₄ : V) q₅ = 2 := (hA _ _).mp a45
  have d50 : G.dist (q₅ : V) q₀ = 2 := (hA _ _).mp a50
  have d40 : G.dist (q₄ : V) q₀ = 4 := by
    have h1 := F.moore.conn.dist_triangle (u := (q₃ : V)) (v := (q₄ : V)) (w := (q₀ : V))
    have h2 := F.moore.conn.dist_triangle (u := (q₄ : V)) (v := (q₅ : V)) (w := (q₀ : V))
    omega
  have hnd : [q₃, q₂, q₁, q₀].Nodup := by
    simp [a23.ne.symm, n13.symm, n03.symm, a12.ne.symm, n02.symm, a01.ne.symm]
  obtain ⟨α, β, δ', -, -, -, hαβ, hβδ, hcase⟩ :=
    path_dichotomy F hr haper ⟨h₃, h₂, h₁, h₀, a23.symm, a12.symm, a01.symm, hnd⟩
  obtain ⟨l, hl⟩ : ∃ l, c q₃ q₄ = l := ⟨_, rfl⟩
  have hq₄ : r l q₃ = q₄ := F.r_eq hr h₃ h₄ a34 hl
  have hmem : ∀ {y₁ y₂ : {v : V // col v = false}}, (y₁, y₂) ∈
      {m : {v : V // col v = false} × {v : V // col v = false} |
        q₃ ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧ m.2 ∈ oppSet G col w ∧
          q₀ ∈ oppSet G col w ∧ (pointGraph G col).Adj q₃ m.1 ∧
          (pointGraph G col).Adj m.1 m.2 ∧ (pointGraph G col).Adj m.2 q₀ ∧
          [q₃, m.1, m.2, q₀].Nodup} → y₁ = q₄ → q₅ ∈ oppSet G col w := by
    intro y₁ y₂ hm h1
    obtain ⟨-, -, hy₂, -, -, h12, h20, -⟩ := hm
    rw [h1] at h12
    rw [Subtype.ext (eq_of_mid F.moore d40 d45 d50 ((hA _ _).mp h12) ((hA _ _).mp h20))]
    exact hy₂
  rcases hcase with ⟨hαδ, hset⟩ | ⟨-, e, heα, heβ, hσ, hset⟩
  ·
    rw [hset] at hmem
    rcases fin_three_cases hαβ hβδ hαδ l with rfl | rfl | rfl
    · exact hmem (y₂ := r β (r l q₃)) (by simp) hq₄
    · exact hmem (y₂ := r δ' (r l q₃)) (by simp) hq₄
    · exact hmem (y₂ := r α (r l q₃)) (by simp) hq₄
  ·
    rw [hset] at hmem
    rcases fin_three_cases hαβ heβ.symm heα.symm l with rfl | rfl | rfl
    · exact hmem (y₂ := r β (r l q₃)) (by simp) hq₄
    · exfalso
      rw [hq₄] at hσ
      have h3 := dist_sigmaMap F hr haper h₄
      rw [← hσ] at h3
      have := (hd _ _ 3).mp h3
      omega
    · exact hmem (y₂ := r β (r l q₃)) (by simp) hq₄

end CFSG.Combinatorics.AperiodicOppositeComponents
