module

public import CFSG.GH74.BNPair.Defs

public section

namespace CFSG.GH74.BNPair

variable {V : Type*}

theorem infix_two_cons_cons {a b u v : V} {l : List V} :
    [a, b] <:+: u :: v :: l ↔ (a = u ∧ b = v) ∨ [a, b] <:+: v :: l := by
  rw [List.infix_cons_iff]
  simp [List.prefix_cons_iff]

theorem prefix_two_cons {a b u : V} {l : List V} :
    [a, b] <+: u :: l ↔ a = u ∧ l.head? = some b := by
  constructor
  · rintro ⟨t, ht⟩
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
    obtain ⟨rfl, h2⟩ := ht
    rw [← h2]
    simp
  · rintro ⟨rfl, hl⟩
    cases l with
    | nil => simp at hl
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at hl
      subst hl
      exact ⟨l, rfl⟩

theorem prefix_three_cons_cons {a b c u v : V} {l : List V} :
    [a, b, c] <+: u :: v :: l ↔ a = u ∧ b = v ∧ l.head? = some c := by
  constructor
  · rintro ⟨t, ht⟩
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
    obtain ⟨rfl, rfl, h3⟩ := ht
    rw [← h3]
    simp
  · rintro ⟨rfl, rfl, hl⟩
    cases l with
    | nil => simp at hl
    | cons x l =>
      simp only [List.head?_cons, Option.some.injEq] at hl
      subst hl
      exact ⟨l, rfl⟩

theorem infix_three_cons_cons {a b c u v : V} {l : List V} :
    [a, b, c] <:+: u :: v :: l ↔ (a = u ∧ b = v ∧ l.head? = some c) ∨ [a, b, c] <:+: v :: l := by
  rw [List.infix_cons_iff, prefix_three_cons_cons]

theorem not_infix_two_singleton {a b u : V} : ¬ ([a, b] <:+: [u]) := by
  intro h
  have := h.length_le
  simp at this

theorem not_infix_three_singleton {a b c u : V} : ¬ ([a, b, c] <:+: [u]) := by
  intro h
  have := h.length_le
  simp at this

def NBPath (G : SimpleGraph V) : List V → Prop
  | [] => True
  | [_] => True
  | u :: v :: l => G.Adj u v ∧ (∀ w, l.head? = some w → w ≠ u) ∧ NBPath G (v :: l)

theorem isGLSPath_iff (G : SimpleGraph V) (l : List V) : IsGLSPath G l ↔ NBPath G l := by
  induction l with
  | nil => simp [IsGLSPath, NBPath]
  | cons u l ih =>
    cases l with
    | nil =>
      simp only [IsGLSPath, NBPath, iff_true]
      exact ⟨fun a b h => (not_infix_two_singleton h).elim,
        fun a b h => not_infix_three_singleton h⟩
    | cons v l =>
      have hih := ih
      unfold NBPath
      rw [← hih]
      unfold IsGLSPath
      simp only [infix_two_cons_cons, infix_three_cons_cons]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1 u v (Or.inl ⟨rfl, rfl⟩), ?_, fun a b hab => h1 a b (Or.inr hab),
          fun a b hab => h2 a b (Or.inr hab)⟩
        intro w hw hwu
        exact h2 u v (Or.inl ⟨rfl, rfl, by rw [hw, hwu]⟩)
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨?_, ?_⟩
        · rintro a b (⟨rfl, rfl⟩ | hab)
          · exact h1
          · exact h3 a b hab
        · rintro a b (⟨rfl, rfl, hw⟩ | hab)
          · exact h2 _ hw rfl
          · exact h4 a b hab

section PathAPI

variable {G : SimpleGraph V}

theorem IsGLSPath.nil : IsGLSPath G ([] : List V) := (isGLSPath_iff G _).2 trivial

theorem IsGLSPath.singleton (u : V) : IsGLSPath G [u] := (isGLSPath_iff G _).2 trivial

theorem isGLSPath_cons_cons {u v : V} {l : List V} :
    IsGLSPath G (u :: v :: l) ↔
      G.Adj u v ∧ (∀ w, l.head? = some w → w ≠ u) ∧ IsGLSPath G (v :: l) := by
  rw [isGLSPath_iff, isGLSPath_iff]
  rfl

theorem IsGLSPath.tail {u : V} {l : List V} (h : IsGLSPath G (u :: l)) : IsGLSPath G l := by
  cases l with
  | nil => exact IsGLSPath.nil
  | cons v l => exact (isGLSPath_cons_cons.1 h).2.2

theorem IsGLSPath.tail_of_cons {l : List V} (h : IsGLSPath G l) : IsGLSPath G l.tail := by
  cases l with
  | nil => exact IsGLSPath.nil
  | cons u l => exact h.tail

theorem IsGLSPath.of_infix {l l' : List V} (h : IsGLSPath G l) (hl : l' <:+: l) :
    IsGLSPath G l' :=
  ⟨fun a b hab => h.1 a b (hab.trans hl), fun a b hab => h.2 a b (hab.trans hl)⟩

theorem IsGLSPath.reverse {l : List V} (h : IsGLSPath G l) : IsGLSPath G l.reverse := by
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · have : [b, a] <:+: l := by
      have := List.reverse_infix.2 hab
      simpa using this
    exact (h.1 b a this).symm
  · have : [a, b, a] <:+: l := by
      have := List.reverse_infix.2 hab
      simpa using this
    exact h.2 a b this

theorem isGLSPath_concat {x y : V} {l : List V} :
    IsGLSPath G (l ++ [y, x]) ↔
      IsGLSPath G (l ++ [y]) ∧ G.Adj y x ∧ (∀ w, l.getLast? = some w → w ≠ x) := by
  constructor
  · intro h
    have h' : IsGLSPath G (x :: y :: l.reverse) := by simpa using h.reverse
    have := isGLSPath_cons_cons.1 h'
    refine ⟨?_, this.1.symm, ?_⟩
    · have := this.2.2.reverse
      simpa using this
    · intro w hw
      exact this.2.1 w (by rw [List.head?_reverse]; exact hw)
  · rintro ⟨h1, h2, h3⟩
    have h1' : IsGLSPath G (y :: l.reverse) := by simpa using h1.reverse
    have : IsGLSPath G (x :: y :: l.reverse) := by
      rw [isGLSPath_cons_cons]
      refine ⟨h2.symm, ?_, h1'⟩
      intro w hw
      exact h3 w (by rw [← List.head?_reverse]; exact hw)
    have := this.reverse
    simpa using this

theorem IsGLSPath.adj_getElem : ∀ {l : List V}, IsGLSPath G l → ∀ {i : ℕ} (hi : i + 1 < l.length),
    G.Adj (l[i]'(by omega)) (l[i + 1]'hi)
  | [], _, i, hi => by simp at hi
  | [_], _, i, hi => by simp at hi
  | a :: b :: t, hl, 0, _ => (isGLSPath_cons_cons.1 hl).1
  | a :: b :: t, hl, i + 1, hi => by
    have := IsGLSPath.adj_getElem (isGLSPath_cons_cons.1 hl).2.2 (i := i) (by simpa using hi)
    simpa using this

theorem IsGLSPath.adj_of_getElem?_eq {l : List V} (hl : IsGLSPath G l) {i : ℕ} {a b : V}
    (ha : l[i]? = some a) (hb : l[i + 1]? = some b) : G.Adj a b := by
  have hi : i + 1 < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have := hl.adj_getElem hi
  rw [List.getElem?_eq_getElem (by omega)] at ha
  rw [List.getElem?_eq_getElem hi] at hb
  simp only [Option.some.injEq] at ha hb
  rw [← ha, ← hb]
  exact this

theorem IsGLSPath.getElem_ne : ∀ {l : List V}, IsGLSPath G l → ∀ {i : ℕ} (hi : i + 2 < l.length),
    l[i]'(by omega) ≠ l[i + 2]'hi
  | [], _, i, hi => by simp at hi
  | [_], _, i, hi => by simp at hi
  | [_, _], _, i, hi => by simp at hi
  | a :: b :: c :: t, hl, 0, _ => by
    have := (isGLSPath_cons_cons.1 hl).2.1 c (by simp)
    simpa using this.symm
  | a :: b :: c :: t, hl, i + 1, hi => by
    have := IsGLSPath.getElem_ne (isGLSPath_cons_cons.1 hl).2.2 (i := i) (by simpa using hi)
    simpa using this

theorem IsGLSPath.two_neighbors {l : List V} (hl : IsGLSPath G l) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i + 1 < l.length) :
    ∃ y₁ ∈ l, ∃ y₂ ∈ l, y₁ ≠ y₂ ∧ G.Adj (l[i]'(by omega)) y₁ ∧ G.Adj (l[i]'(by omega)) y₂ := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  refine ⟨l[j]'(by omega), List.getElem_mem _, l[j + 2]'hi2, List.getElem_mem _, ?_, ?_, ?_⟩
  · exact hl.getElem_ne (i := j) hi2
  · exact (hl.adj_getElem (i := j) (by omega)).symm
  · exact hl.adj_getElem (i := j + 1) hi2

theorem IsGLSPath.dropLast {l : List V} (hl : IsGLSPath G l) : IsGLSPath G l.dropLast :=
  hl.of_infix (List.dropLast_prefix l).isInfix

theorem nbPath_map {g : Equiv.Perm V} (hg : ∀ v w, G.Adj (g v) (g w) ↔ G.Adj v w) :
    ∀ l : List V, NBPath G (l.map g) ↔ NBPath G l
  | [] => by simp [NBPath]
  | [_] => by simp [NBPath]
  | u :: v :: l => by
    have ih := nbPath_map hg (v :: l)
    simp only [List.map_cons] at ih
    simp only [List.map_cons, NBPath]
    rw [ih, hg]
    refine and_congr_right fun _ => and_congr_left fun _ => ?_
    constructor
    · intro h w hw
      have := h (g w) (by rw [List.head?_map, hw]; rfl)
      exact fun e => this (by rw [e])
    · intro h w hw
      rw [List.head?_map] at hw
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.1 hw
      exact fun e => h w' hw' (g.injective e)

theorem IsGLSPath.map {g : Equiv.Perm V} (hg : ∀ v w, G.Adj (g v) (g w) ↔ G.Adj v w) {l : List V}
    (hl : IsGLSPath G l) : IsGLSPath G (l.map g) := by
  rw [isGLSPath_iff] at hl ⊢
  exact (nbPath_map hg l).2 hl

theorem map_eq_self_iff_mem {g : V → V} {l : List V} (h : l.map g = l) : ∀ x ∈ l, g x = x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have := congrArg (fun m => m[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at this
  exact this

theorem getElem_mem_interiorVertices {l : List V} {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i + 1 < l.length) :
    l[i]'(by omega) ∈ interiorVertices l := by
  unfold interiorVertices
  rw [List.mem_iff_getElem]
  have hlt : i - 1 < l.tail.dropLast.length := by simp; omega
  refine ⟨i - 1, hlt, ?_⟩
  rw [List.getElem_dropLast, List.getElem_tail]
  congr 1
  omega


end PathAPI

section Walks

variable {G : SimpleGraph V}

theorem walk_adj_of_infix : ∀ {u v : V} (p : G.Walk u v) {a b : V},
    [a, b] <:+: p.support → G.Adj a b
  | _, _, .nil, a, b, h => by
    simp only [SimpleGraph.Walk.support_nil] at h
    have := h.length_le
    simp at this
  | _, _, .cons (v := w) hadj q, a, b, h => by
    rw [SimpleGraph.Walk.support_cons, List.infix_cons_iff] at h
    rcases h with h | h
    · rw [prefix_two_cons] at h
      obtain ⟨rfl, hb⟩ := h
      rw [← q.cons_tail_support] at hb
      simp only [List.head?_cons, Option.some.injEq] at hb
      rw [← hb]
      exact hadj
    · exact walk_adj_of_infix q h

theorem walk_isGLSPath_support {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    IsGLSPath G p.support := by
  refine ⟨fun a b h => walk_adj_of_infix p h, fun a b h => ?_⟩
  have hnd := hp.support_nodup
  have := hnd.sublist h.sublist
  simp at this

theorem exists_isGLSPath_of_reachable {u v : V} (h : G.Reachable u v) :
    ∃ l : List V, IsGLSPath G l ∧ l.head? = some u ∧ l.getLast? = some v ∧
      l.length = G.dist u v + 1 := by
  obtain ⟨p, hp, hlen⟩ := h.exists_path_of_dist
  refine ⟨p.support, walk_isGLSPath_support hp, ?_, ?_, ?_⟩
  · rw [← p.cons_tail_support]
    rfl
  · rw [List.getLast?_eq_some_getLast (by simp)]
    simp [SimpleGraph.Walk.getLast_support]
  · rw [SimpleGraph.Walk.length_support, hlen]

theorem exists_walk_of_isGLSPath : ∀ {l : List V}, IsGLSPath G l → ∀ {u v : V},
    l.head? = some u → l.getLast? = some v → ∃ p : G.Walk u v, p.length + 1 = l.length
  | [], _, u, v, hu, _ => by simp at hu
  | [x], _, u, v, hu, hv => by
    simp only [List.head?_cons, Option.some.injEq] at hu
    simp only [List.getLast?_singleton, Option.some.injEq] at hv
    subst hu
    subst hv
    exact ⟨.nil, by simp⟩
  | x :: y :: l, h, u, v, hu, hv => by
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    have h' := isGLSPath_cons_cons.1 h
    have hv' : (y :: l).getLast? = some v := by
      simpa [List.getLast?_cons_cons] using hv
    obtain ⟨q, hq⟩ := exists_walk_of_isGLSPath h'.2.2 (u := y) (v := v) rfl hv'
    exact ⟨.cons h'.1 q, by simp [hq]⟩

theorem reachable_dist_le_of_isGLSPath {l : List V} (h : IsGLSPath G l) {u v : V}
    (hu : l.head? = some u) (hv : l.getLast? = some v) :
    G.Reachable u v ∧ G.dist u v + 1 ≤ l.length := by
  obtain ⟨p, hp⟩ := exists_walk_of_isGLSPath h hu hv
  exact ⟨⟨p⟩, by have := SimpleGraph.dist_le p; omega⟩

end Walks

section Parity

variable {G : SimpleGraph V} {col : V → Bool} (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
include hcol

theorem col_eq_iff_even_length : ∀ {u v : V} (p : G.Walk u v), (col u = col v ↔ Even p.length)
  | _, _, .nil => by simp
  | u, v, .cons (v := w) hadj q => by
    have ih := col_eq_iff_even_length q
    have h1 := hcol u w hadj
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    cases hu : col u <;> cases hw : col w <;> cases hv : col v <;> simp_all

theorem col_eq_iff_even_dist {u v : V} (h : G.Reachable u v) :
    (col u = col v ↔ Even (G.dist u v)) := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  exact col_eq_iff_even_length hcol p

end Parity

theorem getLast?_eq_getElem?_of_length {l : List V} {m : ℕ} (hlen : l.length = m + 1) :
    l.getLast? = l[m]? := by
  rw [List.getLast?_eq_getElem?, hlen]
  rfl

theorem exists_append_of_getLast? {l : List V} {a : V} (h : l.getLast? = some a) :
    ∃ l', l = l' ++ [a] :=
  ⟨l.dropLast, (List.dropLast_append_getLast? a h).symm⟩

theorem IsGLSPath.exists_fun {G : SimpleGraph V} {l : List V} (hl : IsGLSPath G l) {u v : V}
    (hu : l.head? = some u) (hv : l.getLast? = some v) :
    ∃ (f : ℕ → V) (k : ℕ), l.length = k + 1 ∧ f 0 = u ∧ f k = v ∧
      (∀ i, i < k → G.Adj (f i) (f (i + 1))) ∧ (∀ i, i + 2 ≤ k → f i ≠ f (i + 2)) ∧
      (∀ i, i ≤ k → l[i]? = some (f i)) := by
  have hne : l ≠ [] := by
    rintro rfl
    simp at hu
  obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 :=
    ⟨l.length - 1, by have := List.length_pos_iff.2 hne; omega⟩
  refine ⟨fun i => l.getD i u, k, hk, ?_, ?_, ?_, ?_, ?_⟩
  · have : l[0]? = some u := by
      rw [← List.head?_eq_getElem?]; exact hu
    simp [List.getD_eq_getElem?_getD, this]
  · have h1 : l.getLast? = l[k]? := getLast?_eq_getElem?_of_length hk
    rw [h1] at hv
    simp [List.getD_eq_getElem?_getD, hv]
  · intro i hi
    have := hl.adj_getElem (i := i) (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega),
      List.getElem?_eq_getElem (show i + 1 < l.length by omega)] using this
  · intro i hi
    have := hl.getElem_ne (i := i) (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega),
      List.getElem?_eq_getElem (show i + 2 < l.length by omega)] using this
  · intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]

end CFSG.GH74.BNPair
