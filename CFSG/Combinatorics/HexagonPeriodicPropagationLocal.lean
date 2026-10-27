module

public import CFSG.Combinatorics.HexagonPeriodicPropagationSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath

namespace CFSG.Combinatorics.HexagonPeriodicPropagation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}

namespace IsFrame

variable (F : IsFrame G col w ℓ p z q c ε)
include F

theorem not_three {x : Fin 6 → {v : V // col v = false}} (hx : IsHex G col w x) {i : Fin 3}
    (a b d : Fin 6) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ha : c (x a) (x (a + 1)) = i)
    (hb : c (x b) (x (b + 1)) = i) (hd : c (x d) (x (d + 1)) = i) : False := by
  have h := six_cycle_colours F.moore col F.inj F.root F.line F.ne F.label F.data hx.1 hx.2.1
    hx.2.2 i
  have hsub : ({a, b, d} : Finset (Fin 6)) ⊆ univ.filter fun n => c (x n) (x (n + 1)) = i := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Finset.mem_filter]
    rcases hn with rfl | rfl | rfl
    exacts [⟨mem_univ _, ha⟩, ⟨mem_univ _, hb⟩, ⟨mem_univ _, hd⟩]
  have hle := Finset.card_le_card hsub
  rw [h, Finset.card_eq_three.mpr ⟨a, b, d, hab, had, hbd, rfl⟩] at hle
  omega

theorem eq_of_periodic {C D : Fin 6 → {v : V // col v = false}} (hC : IsHex G col w C)
    (hCp : IsPeriodic c C) (hD : IsHex G col w D) (h0 : D 0 = C 0) (h1 : D 1 = C 1)
    (h2 : D 2 = C 2) : D = C := by
  obtain ⟨α, β, γ, hαβ, hβγ, hαγ, hcol⟩ := hCp
  have e0 : c (C 0) (C 1) = α := hcol 0
  have e1 : c (C 1) (C 2) = β := hcol 1
  have e2 : c (C 2) (C 3) = γ := hcol 2
  have e3 : c (C 3) (C 4) = α := hcol 3
  have e4 : c (C 4) (C 5) = β := hcol 4
  have e5 : c (C 5) (C 0) = γ := hcol 5
  have mC := hC.2.1
  have mD := hD.2.1
  have aC := hC.2.2
  have aD := hD.2.2
  have nD : ∀ {a b : Fin 6}, a ≠ b → D a ≠ D b := fun h h' => h (hD.1 h')
  have nC : ∀ {a b : Fin 6}, a ≠ b → C a ≠ C b := fun h h' => h (hC.1 h')
  have c21 : c (C 2) (C 1) = β := (F.symm (mC 1) (mC 2) (aC 1)).trans e1
  have c32 : c (C 3) (C 2) = γ := (F.symm (mC 2) (mC 3) (aC 2)).trans e2
  have c05 : c (C 0) (C 5) = γ := (F.symm (mC 5) (mC 0) (aC 5)).trans e5
  have c54 : c (C 5) (C 4) = β := (F.symm (mC 4) (mC 5) (aC 4)).trans e4
  have a23 : (pointGraph G col).Adj (C 2) (D 3) := by
    rw [← h2]
    exact aD 2
  have a05 : (pointGraph G col).Adj (C 0) (D 5) := by
    rw [← h0]
    exact (aD 5).symm
  have c50 : c (D 5) (D 0) = c (C 0) (D 5) := by
    rw [h0]
    exact F.symm (mC 0) (mD 5) a05
  have d31 : D 3 ≠ C 1 := by
    rw [← h1]
    exact nD (by decide)
  have d51 : D 5 ≠ C 1 := by
    rw [← h1]
    exact nD (by decide)
  have hD3 : D 3 = C 3 ∨ c (C 2) (D 3) = α := by
    rcases fin_three_cases hαβ hβγ hαγ (c (C 2) (D 3)) with h | h | h
    · exact Or.inr h
    · exact absurd (F.unique (mC 2) (mD 3) (mC 1) a23 (aC 1).symm (h.trans c21.symm)) d31
    · exact Or.inl (F.unique (mC 2) (mD 3) (mC 3) a23 (aC 2) (h.trans e2.symm))
  have hD5 : D 5 = C 5 ∨ c (C 0) (D 5) = β := by
    rcases fin_three_cases hαβ hβγ hαγ (c (C 0) (D 5)) with h | h | h
    · exact absurd (F.unique (mC 0) (mD 5) (mC 1) a05 (aC 0) (h.trans e0.symm)) d51
    · exact Or.inr h
    · exact Or.inl (F.unique (mC 0) (mD 5) (mC 5) a05 (aC 5).symm (h.trans c05.symm))
  have hd1 : c (D 0) (D (0 + 1)) = α := by
    show c (D 0) (D 1) = α
    rw [h0, h1]
    exact e0
  have hd2 : c (D 1) (D (1 + 1)) = β := by
    show c (D 1) (D 2) = β
    rw [h1, h2]
    exact e1
  rcases hD3 with h3 | h3 <;> rcases hD5 with h5 | h5
  ·
    have a34 : (pointGraph G col).Adj (C 3) (D 4) := by
      rw [← h3]
      exact aD 3
    have a45 : (pointGraph G col).Adj (D 4) (C 5) := by
      rw [← h5]
      exact aD 4
    have h4 : D 4 = C 4 := by
      by_contra hne
      exact F.no_square (mC 3) (mC 4) (mC 5) (mD 4) (aC 3) (aC 4) a45.symm a34.symm
        (nC (by decide)) (Ne.symm hne)
    funext n
    fin_cases n
    exacts [h0, h1, h2, h3, h4, h5]
  ·
    exfalso
    have a34 : (pointGraph G col).Adj (C 3) (D 4) := by
      rw [← h3]
      exact aD 3
    rcases fin_three_cases hαβ hβγ hαγ (c (C 3) (D 4)) with h | h | h
    · have h4 : D 4 = C 4 := F.unique (mC 3) (mD 4) (mC 4) a34 (aC 3) (h.trans e3.symm)
      have a45 : (pointGraph G col).Adj (C 4) (D 5) := by
        rw [← h4]
        exact aD 4
      have h55 : C 5 ≠ D 5 := fun h' => hβγ (h5.symm.trans (by rw [← h']; exact c05))
      exact F.no_square (mC 0) (mC 5) (mC 4) (mD 5) (aC 5).symm (aC 4).symm a45 a05.symm
        (nC (by decide)) h55
    · exact F.not_three hD 1 3 5 (by decide) (by decide) (by decide) hd2
        (by show c (D 3) (D 4) = β; rw [h3]; exact h)
        (by show c (D 5) (D 0) = β; rw [c50]; exact h5)
    · exact nD (show (4 : Fin 6) ≠ 2 by decide)
        ((F.unique (mC 3) (mD 4) (mC 2) a34 (aC 2).symm (h.trans c32.symm)).trans h2.symm)
  ·
    exfalso
    have a45 : (pointGraph G col).Adj (C 5) (D 4) := by
      rw [← h5]
      exact (aD 4).symm
    rcases fin_three_cases hαβ hβγ hαγ (c (C 5) (D 4)) with h | h | h
    · have hc45 : c (D 4) (D (4 + 1)) = α := by
        show c (D 4) (D 5) = α
        rw [h5, F.symm (mC 5) (mD 4) a45]
        exact h
      exact F.not_three hD 0 2 4 (by decide) (by decide) (by decide) hd1
        (by show c (D 2) (D 3) = α; rw [h2]; exact h3) hc45
    · have h4 : D 4 = C 4 := F.unique (mC 5) (mD 4) (mC 4) a45 (aC 4).symm (h.trans c54.symm)
      have a34 : (pointGraph G col).Adj (C 4) (D 3) := by
        rw [← h4]
        exact (aD 3).symm
      have h33 : C 3 ≠ D 3 := fun h' => hαγ (h3.symm.trans (by rw [← h']; exact e2))
      exact F.no_square (mC 2) (mC 3) (mC 4) (mD 3) (aC 2) (aC 3) a34 a23.symm (nC (by decide))
        h33
    · exact nD (show (4 : Fin 6) ≠ 0 by decide)
        ((F.unique (mC 5) (mD 4) (mC 0) a45 (aC 5) (h.trans e5.symm)).trans h0.symm)
  ·
    exfalso
    have hc23 : c (D 2) (D (2 + 1)) = α := by
      show c (D 2) (D 3) = α
      rw [h2]
      exact h3
    have hc50 : c (D 5) (D (5 + 1)) = β := by
      show c (D 5) (D 0) = β
      rw [c50]
      exact h5
    have h3a : c (D 3) (D 4) ≠ α := fun h =>
      F.not_three hD 0 2 3 (by decide) (by decide) (by decide) hd1 hc23 h
    have h4a : c (D 4) (D 5) ≠ α := fun h =>
      F.not_three hD 0 2 4 (by decide) (by decide) (by decide) hd1 hc23 h
    have h3b : c (D 3) (D 4) ≠ β := fun h =>
      F.not_three hD 1 3 5 (by decide) (by decide) (by decide) hd2 h hc50
    have h4b : c (D 4) (D 5) ≠ β := fun h =>
      F.not_three hD 1 4 5 (by decide) (by decide) (by decide) hd2 h hc50
    have g3 : c (D 3) (D 4) = γ := by
      rcases fin_three_cases hαβ hβγ hαγ (c (D 3) (D 4)) with h | h | h
      exacts [absurd h h3a, absurd h h3b, h]
    have g4 : c (D 4) (D 5) = γ := by
      rcases fin_three_cases hαβ hβγ hαγ (c (D 4) (D 5)) with h | h | h
      exacts [absurd h h4a, absurd h h4b, h]
    have hsame : c (D 4) (D 3) = c (D 4) (D 5) := by
      rw [F.symm (mD 3) (mD 4) (aD 3), g3, g4]
    exact nD (show (3 : Fin 6) ≠ 5 by decide)
      (F.unique (mD 4) (mD 3) (mD 5) (aD 3).symm (aD 4) hsame)

theorem exists_periodic_third {C : Fin 6 → {v : V // col v = false}} (hC : IsHex G col w C)
    (hCp : IsPeriodic c C) {y : {v : V // col v = false}} (hy : (pointGraph G col).dist w y = 3)
    (h1y : (pointGraph G col).Adj (C 1) y) (hy0 : y ≠ C 0) (hy2 : y ≠ C 2) :
    ∃ E, IsHex G col w E ∧ IsPeriodic c E ∧ E 0 = C 0 ∧ E 1 = C 1 ∧ E 2 = y := by
  obtain ⟨α, β, γ, hαβ, hβγ, hαγ, hcol⟩ := id hCp
  have e0 : c (C 0) (C 1) = α := hcol 0
  have e1 : c (C 1) (C 2) = β := hcol 1
  have e5 : c (C 5) (C 0) = γ := hcol 5
  have mC := hC.2.1
  have aC := hC.2.2
  have nC : ∀ {a b : Fin 6}, a ≠ b → C a ≠ C b := fun h h' => h (hC.1 h')
  have c10 : c (C 1) (C 0) = α := (F.symm (mC 0) (mC 1) (aC 0)).trans e0
  have c05 : c (C 0) (C 5) = γ := (F.symm (mC 5) (mC 0) (aC 5)).trans e5
  have hcy : c (C 1) y = γ := by
    rcases fin_three_cases hαβ hβγ hαγ (c (C 1) y) with h | h | h
    · exact absurd (F.unique (mC 1) hy (mC 0) h1y (aC 0).symm (h.trans c10.symm)) hy0
    · exact absurd (F.unique (mC 1) hy (mC 2) h1y (aC 1) (h.trans e1.symm)) hy2
    · exact h
  have cy1 : c y (C 1) = γ := (F.symm (mC 1) hy h1y).trans hcy
  obtain ⟨e₃, m₃, ye₃, he₃⟩ := F.exists_colour hy β
  obtain ⟨e₄, m₄, e₃e₄, he₄⟩ := F.exists_colour m₃ α
  have n03 : C 0 ≠ e₃ := fun h => F.no_triangle (mC 0) (mC 1) hy (aC 0) h1y (by rw [h]; exact ye₃)
  have n13 : C 1 ≠ e₃ := fun h => hβγ (he₃.symm.trans (by rw [← h]; exact cy1))
  have n04 : C 0 ≠ e₄ := by
    intro h
    have h' : c (C 0) e₃ = α := by
      rw [h]
      exact (F.symm m₃ m₄ e₃e₄).trans he₄
    have h31 := F.unique (mC 0) m₃ (mC 1) (by rw [h]; exact e₃e₄.symm) (aC 0) (h'.trans e0.symm)
    exact n13 h31.symm
  have n14 : C 1 ≠ e₄ := fun h => F.no_triangle (mC 1) hy m₃ h1y ye₃ (by rw [h]; exact e₃e₄)
  have ny4 : y ≠ e₄ := fun h =>
    hαβ (he₄.symm.trans (by rw [← h]; exact (F.symm hy m₃ ye₃).trans he₃))
  have hnd : [C 0, C 1, y, e₃, e₄].Nodup := nodup_five (nC (by decide)) (Ne.symm hy0) n03 n04
    h1y.ne n13 n14 ye₃.ne ny4 e₃e₄.ne
  obtain ⟨u, ⟨mu, h0u, h4u⟩, -, hnd6, hcu⟩ := F.complete (i := α) (j := γ) (k := β) hαγ
    (Ne.symm hβγ) hαβ (mC 0) (mC 1) hy m₃ m₄ (aC 0) h1y ye₃ e₃e₄ hnd e0 hcy he₃ he₄
  set E : Fin 6 → {v : V // col v = false} := ![C 0, C 1, y, e₃, e₄, u] with hEdef
  have hE : IsHex G col w E := by
    refine ⟨List.nodup_ofFn.mp (by simpa [hEdef, List.ofFn_succ] using hnd6), fun n => ?_,
      fun n => ?_⟩
    · fin_cases n
      exacts [mC 0, mC 1, hy, m₃, m₄, mu]
    · fin_cases n
      exacts [aC 0, h1y, ye₃, e₃e₄, h4u, h0u.symm]
  rcases hcu with ⟨hc4, hc5⟩ | ⟨hc4, hc5⟩
  · refine ⟨E, hE, ⟨α, γ, β, hαγ, Ne.symm hβγ, hαβ, fun n => ?_⟩, rfl, rfl, rfl⟩
    fin_cases n
    exacts [e0, hcy, he₃, he₄, hc4, hc5]
  ·
    exfalso
    have hu5 : u = C 5 := F.unique (mC 0) mu (mC 5) h0u (aC 5).symm
      (((F.symm mu (mC 0) h0u.symm).trans hc5).trans c05.symm)
    have hU := F.eq_of_periodic (hC.rotate 5) (hCp.rotate 5) (hE.rotate 5)
      (show E (0 + 5) = C (0 + 5) from hu5) rfl rfl
    exact hy2 (congrFun hU 3)

theorem exists_periodic_of_mem {C : Fin 6 → {v : V // col v = false}} (hC : IsHex G col w C)
    (hCp : IsPeriodic c C) (m : Fin 6) {a d : {v : V // col v = false}}
    (ha : (pointGraph G col).dist w a = 3) (hd : (pointGraph G col).dist w d = 3)
    (hma : (pointGraph G col).Adj (C m) a) (hmd : (pointGraph G col).Adj (C m) d) (had : a ≠ d) :
    ∃ E, IsHex G col w E ∧ IsPeriodic c E ∧ E 0 = a ∧ E 1 = C m ∧ E 2 = d := by
  set C' : Fin 6 → {v : V // col v = false} := fun n => C (n + (m - 1)) with hC'def
  have hC' : IsHex G col w C' := hC.rotate (m - 1)
  have hC'p : IsPeriodic c C' := hCp.rotate (m - 1)
  have h1 : C' 1 = C m := by
    show C (1 + (m - 1)) = C m
    rw [show 1 + (m - 1) = m by abel]
  rw [← h1] at hma hmd ⊢
  set C'' : Fin 6 → {v : V // col v = false} := fun n => C' (2 - n) with hC''def
  have hC'' : IsHex G col w C'' := hC'.reflect 2
  have hC''p : IsPeriodic c C'' := F.periodic_reflect hC' hC'p 2
  obtain ⟨α, β, γ, hαβ, hβγ, hαγ, hcol⟩ := id hC'p
  have mC := hC'.2.1
  have aC := hC'.2.2
  have e0 : c (C' 0) (C' 1) = α := hcol 0
  have e1 : c (C' 1) (C' 2) = β := hcol 1
  have c10 : c (C' 1) (C' 0) = α := (F.symm (mC 0) (mC 1) (aC 0)).trans e0
  obtain ⟨y, hy, h1y, hcy⟩ := F.exists_colour (mC 1) γ
  have hy0 : y ≠ C' 0 := fun h => hαγ (c10.symm.trans (by rw [← h]; exact hcy))
  have hy2 : y ≠ C' 2 := fun h => hβγ (e1.symm.trans (by rw [← h]; exact hcy))
  have hnbr : ∀ {t : {v : V // col v = false}}, (pointGraph G col).dist w t = 3 →
      (pointGraph G col).Adj (C' 1) t → t = C' 0 ∨ t = C' 2 ∨ t = y := by
    intro t ht h1t
    rcases fin_three_cases hαβ hβγ hαγ (c (C' 1) t) with h | h | h
    · exact Or.inl (F.unique (mC 1) ht (mC 0) h1t (aC 0).symm (h.trans c10.symm))
    · exact Or.inr (Or.inl (F.unique (mC 1) ht (mC 2) h1t (aC 1) (h.trans e1.symm)))
    · exact Or.inr (Or.inr (F.unique (mC 1) ht hy h1t h1y (h.trans hcy.symm)))
  obtain ⟨E₁, hE₁, hE₁p, hE₁0, hE₁1, hE₁2⟩ := F.exists_periodic_third hC' hC'p hy h1y hy0 hy2
  obtain ⟨E₂, hE₂, hE₂p, hE₂0, hE₂1, hE₂2⟩ := F.exists_periodic_third hC'' hC''p hy h1y hy2 hy0
  have hE₁r := hE₁.reflect 2
  have hE₁rp := F.periodic_reflect hE₁ hE₁p 2
  have hE₂r := hE₂.reflect 2
  have hE₂rp := F.periodic_reflect hE₂ hE₂p 2
  rcases hnbr ha hma with rfl | rfl | rfl <;> rcases hnbr hd hmd with rfl | rfl | rfl
  · exact absurd rfl had
  · exact ⟨C', hC', hC'p, rfl, rfl, rfl⟩
  · exact ⟨E₁, hE₁, hE₁p, hE₁0, hE₁1, hE₁2⟩
  · exact ⟨C'', hC'', hC''p, rfl, rfl, rfl⟩
  · exact absurd rfl had
  · exact ⟨E₂, hE₂, hE₂p, hE₂0, hE₂1, hE₂2⟩
  · exact ⟨fun n => E₁ (2 - n), hE₁r, hE₁rp, hE₁2, hE₁1, hE₁0⟩
  · exact ⟨fun n => E₂ (2 - n), hE₂r, hE₂rp, hE₂2, hE₂1, hE₂0⟩
  · exact absurd rfl had

end IsFrame

omit [Fintype V] [DecidableRel G.Adj] in
theorem exists_normal {D : Fin 6 → {v : V // col v = false}} (hD : IsHex G col w D)
    {a b d : {v : V // col v = false}} (hab : s(a, b) ∈ hexEdges D) (hbd : s(b, d) ∈ hexEdges D)
    (had : a ≠ d) :
    ∃ D', IsHex G col w D' ∧ hexEdges D' = hexEdges D ∧ D' 0 = a ∧ D' 1 = b ∧ D' 2 = d := by
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hab
  obtain ⟨m', -, hm'⟩ := Finset.mem_image.mp hbd
  have e2 : ∀ t : Fin 6, 2 + t = t + 1 + 1 := by decide
  have e3 : ∀ t : Fin 6, t + 1 + 1 - 2 = t := by decide
  rcases Sym2.eq_iff.mp hm with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;>
    rcases Sym2.eq_iff.mp hm' with ⟨hb', hd⟩ | ⟨hd, hb'⟩
  ·
    have hm1 : m' = m + 1 := hD.1 (hb'.trans hb.symm)
    refine ⟨fun n => D (n + m), hD.rotate m, hexEdges_rotate D m, ?_, ?_, ?_⟩
    · show D (0 + m) = a
      rw [zero_add, ha]
    · show D (1 + m) = b
      rw [add_comm, hb]
    · show D (2 + m) = d
      rw [e2, ← hm1, hd]
  · have h : m' = m := add_right_cancel (hD.1 (hb'.trans hb.symm))
    exact absurd (ha.symm.trans ((congrArg D h).symm.trans hd)) had
  · have h : m' = m := hD.1 (hb'.trans hb.symm)
    exact absurd (ha.symm.trans ((congrArg (fun t => D (t + 1)) h).symm.trans hd)) had
  ·
    have hm1 : m' + 1 = m := hD.1 (hb'.trans hb.symm)
    refine ⟨fun n => D (m + 1 - n), hD.reflect (m + 1), hexEdges_reflect D (m + 1), ?_, ?_, ?_⟩
    · show D (m + 1 - 0) = a
      rw [sub_zero, ha]
    · show D (m + 1 - 1) = b
      rw [add_sub_cancel_right, hb]
    · show D (m + 1 - 2) = d
      rw [← hm1, e3, hd]

omit [Fintype V] [DecidableRel G.Adj] in
theorem exists_other_edge {D : Fin 6 → {v : V // col v = false}} (hD : IsHex G col w D)
    {a b : {v : V // col v = false}} (hab : s(a, b) ∈ hexEdges D) :
    ∃ t, (pointGraph G col).dist w t = 3 ∧ (pointGraph G col).Adj b t ∧
      s(b, t) ∈ hexEdges D ∧ t ≠ a := by
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hab
  have n2 : ∀ t : Fin 6, t + 1 + 1 ≠ t := by decide
  have n3 : ∀ t : Fin 6, t - 1 ≠ t + 1 := by decide
  rcases Sym2.eq_iff.mp hm with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · refine ⟨D (m + 1 + 1), hD.2.1 _, ?_, ?_, ?_⟩
    · rw [← hb]
      exact hD.2.2 (m + 1)
    · rw [← hb]
      exact Finset.mem_image_of_mem _ (mem_univ (m + 1))
    · rw [← ha]
      exact fun h => n2 m (hD.1 h)
  · have e : m - 1 + 1 = m := by abel
    refine ⟨D (m - 1), hD.2.1 _, ?_, ?_, ?_⟩
    · rw [← hb]
      have h := hD.2.2 (m - 1)
      rw [e] at h
      exact h.symm
    · rw [← hb, Sym2.eq_swap]
      have h := Finset.mem_image_of_mem (fun n => s(D n, D (n + 1))) (mem_univ (m - 1))
      simp only [e] at h
      exact h
    · rw [← ha]
      exact fun h => n3 m (hD.1 h)

end CFSG.Combinatorics.HexagonPeriodicPropagation
