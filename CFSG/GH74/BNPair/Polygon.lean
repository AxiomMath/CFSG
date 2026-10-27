module

public import CFSG.GH74.BNPair.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

public section

namespace CFSG.GH74.BNPair

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

structure PolyHyp (G : SimpleGraph V) (n : ℕ) : Prop where
  three_le : 3 ≤ n
  nonempty : Nonempty V
  reach_dist : ∀ u v, G.Reachable u v ∧ G.dist u v ≤ n
  unique : ∀ {u v : V} {p q : List V}, IsGLSPath G p → IsGLSPath G q → p.head? = some u →
    q.head? = some u → p.getLast? = some v → q.getLast? = some v → p.length ≤ n →
      q.length ≤ n → p = q
  color : ∃ col : V → Bool, ∀ u v, G.Adj u v → col u ≠ col v
  valency : ∀ v, 3 ≤ (G.neighborSet v).encard

namespace PolyHyp

variable (h : PolyHyp G n)
include h

theorem connected : G.Connected :=
  haveI := h.nonempty
  ⟨fun u v => (h.reach_dist u v).1⟩

theorem dist_adj {a b : V} (hab : G.Adj a b) (x : V) :
    G.dist a x = G.dist b x + 1 ∨ G.dist b x = G.dist a x + 1 := by
  obtain ⟨col, hcol⟩ := h.color
  have hc := h.connected
  have t1 := hc.dist_triangle (u := a) (v := b) (w := x)
  have t2 := hc.dist_triangle (u := b) (v := a) (w := x)
  have hab1 : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hab
  have hba1 : G.dist b a = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hab.symm
  have e1 := col_eq_iff_even_dist hcol (h.reach_dist a x).1
  have e2 := col_eq_iff_even_dist hcol (h.reach_dist b x).1
  have hne := hcol a b hab
  have hpar : (Even (G.dist a x) ↔ ¬ Even (G.dist b x)) := by
    rw [← e1, ← e2]
    cases ha : col a <;> cases hb : col b <;> cases hx : col x <;> simp_all
  rw [Nat.even_iff, Nat.even_iff] at hpar
  omega

theorem exists_unique_path_of_dist_lt {u v : V} (hd : G.dist u v < n) :
    ∃ l : List V, IsGLSPath G l ∧ l.head? = some u ∧ l.getLast? = some v ∧ l.length ≤ n ∧
      ∀ l' : List V, IsGLSPath G l' → l'.head? = some u → l'.getLast? = some v →
        l'.length ≤ n → l' = l := by
  obtain ⟨l, hl, hlh, hll, hlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist u v).1
  exact ⟨l, hl, hlh, hll, by omega, fun l' hl' hh' hl'' hlen' => h.unique hl' hl hh' hlh hl'' hll
    hlen' (by omega)⟩

theorem dist_succ_of_adj {v v' v₁ : V} (hd : G.dist v v' = n) (hadj : G.Adj v v₁) :
    G.dist v₁ v' + 1 = n := by
  have h1 := (h.reach_dist v₁ v').2
  have := h.dist_adj hadj v'
  omega

theorem exists_path_through {v v' v₁ : V} (hd : G.dist v v' = n) (hadj : G.Adj v v₁) :
    ∃ l : List V, IsGLSPath G l ∧ l.head? = some v ∧ l.getLast? = some v' ∧
      l.length = n + 1 ∧ l[1]? = some v₁ := by
  have hd1 := h.dist_succ_of_adj hd hadj
  obtain ⟨q, hq, hqh, hql, hqlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist v₁ v').1
  cases q with
  | nil => simp at hqh
  | cons x q' =>
    simp only [List.head?_cons, Option.some.injEq] at hqh
    subst hqh
    refine ⟨v :: x :: q', ?_, rfl, ?_, ?_, rfl⟩
    · rw [isGLSPath_cons_cons]
      refine ⟨hadj, ?_, hq⟩
      intro w hw hwv
      cases q' with
      | nil => simp at hw
      | cons y q'' =>
        simp only [List.head?_cons, Option.some.injEq] at hw
        have hq' := hq.tail
        have hlast : (y :: q'').getLast? = some v' := by
          simpa [List.getLast?_cons_cons] using hql
        have := reachable_dist_le_of_isGLSPath hq' (u := y) (v := v') rfl hlast
        rw [hw, hwv] at this
        simp only [List.length_cons] at hqlen this
        omega
    · simpa [List.getLast?_cons_cons] using hql
    · simp only [List.length_cons] at hqlen ⊢
      omega

theorem path_through_unique {v v' v₁ : V} {l l' : List V}
    (hl : IsGLSPath G l) (hl' : IsGLSPath G l') (hh : l.head? = some v) (hh' : l'.head? = some v)
    (hla : l.getLast? = some v') (hla' : l'.getLast? = some v') (hlen : l.length = n + 1)
    (hlen' : l'.length = n + 1) (h1 : l[1]? = some v₁) (h1' : l'[1]? = some v₁) : l = l' := by
  cases l with
  | nil => simp at hh
  | cons a l₁ =>
    cases l' with
    | nil => simp at hh'
    | cons a' l₁' =>
      simp only [List.head?_cons, Option.some.injEq] at hh hh'
      subst hh
      subst hh'
      cases l₁ with
      | nil => simp at h1
      | cons b t =>
        cases l₁' with
        | nil => simp at h1'
        | cons b' t' =>
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1 h1'
          have hb : b = b' := h1.trans h1'.symm
          subst hb
          have := h.unique (u := b) (v := v') hl.tail hl'.tail rfl rfl
            (by simpa [List.getLast?_cons_cons] using hla)
            (by simpa [List.getLast?_cons_cons] using hla')
            (by simp only [List.length_cons] at hlen ⊢; omega)
            (by simp only [List.length_cons] at hlen' ⊢; omega)
          rw [this]

theorem exists_bijOn {v v' : V} (hd : G.dist v v' = n) :
    ∃ f : V → V, Set.BijOn f (G.neighborSet v) (G.neighborSet v') ∧
      ∀ l : List V, IsGLSPath G l → l.head? = some v → l.getLast? = some v' →
        l.length = n + 1 → ∀ a b : V, l[1]? = some a → l[n - 1]? = some b → f a = b := by
  classical
  have hd' : G.dist v' v = n := by rw [SimpleGraph.dist_comm]; exact hd
  have hn3 := h.three_le
  let PT : V → List V → Prop := fun a l => IsGLSPath G l ∧ l.head? = some v ∧
    l.getLast? = some v' ∧ l.length = n + 1 ∧ l[1]? = some a
  let f : V → V := fun a =>
    if hex : ∃ l, PT a l then (hex.choose)[n - 1]?.getD a else a
  have hsome : ∀ (m : List V), m.length = n + 1 → ∃ x, m[n - 1]? = some x := by
    intro m hm
    exact ⟨m[n - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have key : ∀ (l : List V) (a b : V), PT a l → l[n - 1]? = some b → f a = b := by
    intro l a b hl hb
    have hex : ∃ l, PT a l := ⟨l, hl⟩
    have hc := hex.choose_spec
    have := path_through_unique h hc.1 hl.1 hc.2.1 hl.2.1 hc.2.2.1 hl.2.2.1 hc.2.2.2.1
      hl.2.2.2.1 hc.2.2.2.2 hl.2.2.2.2
    simp only [f, hex, dite_true]
    rw [this, hb]
    rfl
  have hfa : ∀ (l : List V) (a : V), PT a l → l[n - 1]? = some (f a) := by
    intro l a hl
    obtain ⟨x, hx⟩ := hsome l hl.2.2.2.1
    rw [key l a x hl hx]
    exact hx
  refine ⟨f, ⟨?_, ?_, ?_⟩, fun l hl hh hla hlen a b ha hb => key l a b ⟨hl, hh, hla, hlen, ha⟩ hb⟩
  · intro a ha
    obtain ⟨l, hl⟩ := h.exists_path_through hd ha
    have e := hfa l a hl
    show G.Adj v' (f a)
    have hn : l[n]? = some v' := by
      rw [← getLast?_eq_getElem?_of_length hl.2.2.2.1]; exact hl.2.2.1
    have := hl.1.adj_of_getElem?_eq (i := n - 1) e (by rw [show n - 1 + 1 = n by omega]; exact hn)
    exact this.symm
  · intro a ha a' ha' hfaa'
    obtain ⟨l, hl⟩ := h.exists_path_through hd ha
    obtain ⟨l', hl'⟩ := h.exists_path_through hd ha'
    have e1 := hfa l a hl
    have e2 := hfa l' a' hl'
    have hrev := path_through_unique (v := v') (v' := v) (v₁ := f a) h hl.1.reverse hl'.1.reverse
      (by rw [List.head?_reverse]; exact hl.2.2.1) (by rw [List.head?_reverse]; exact hl'.2.2.1)
      (by rw [List.getLast?_reverse]; exact hl.2.1) (by rw [List.getLast?_reverse]; exact hl'.2.1)
      (by simpa using hl.2.2.2.1) (by simpa using hl'.2.2.2.1)
      (by
        rw [List.getElem?_reverse (by omega), show l.length - 1 - 1 = n - 1 by have := hl.2.2.2.1; omega]
        exact e1)
      (by
        rw [List.getElem?_reverse (by omega), show l'.length - 1 - 1 = n - 1 by
          have := hl'.2.2.2.1; omega]
        rw [hfaa']
        exact e2)
    have hll : l = l' := List.reverse_injective hrev
    have := hl.2.2.2.2
    rw [hll, hl'.2.2.2.2] at this
    exact (Option.some.inj this).symm
  · intro z hz
    have hz' : G.Adj v' z := hz
    obtain ⟨q, hq⟩ := h.exists_path_through hd' hz'
    have hl : IsGLSPath G q.reverse := hq.1.reverse
    have hlen : q.reverse.length = n + 1 := by simpa using hq.2.2.2.1
    obtain ⟨a, ha⟩ : ∃ a, q.reverse[1]? = some a :=
      ⟨q.reverse[1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hhead : q.reverse.head? = some v := by rw [List.head?_reverse]; exact hq.2.2.1
    have hlast : q.reverse.getLast? = some v' := by rw [List.getLast?_reverse]; exact hq.2.1
    have hz2 : q.reverse[n - 1]? = some z := by
      rw [List.getElem?_reverse (by have := hq.2.2.2.1; omega),
        show q.length - 1 - (n - 1) = 1 by have := hq.2.2.2.1; omega]
      exact hq.2.2.2.2
    have hva : G.Adj v a := by
      refine hl.adj_of_getElem?_eq (i := 0) ?_ ha
      rwa [List.head?_eq_getElem?] at hhead
    refine ⟨a, hva, ?_⟩
    exact key q.reverse a z ⟨hl, hhead, hlast, hlen, ha⟩ hz2

theorem dist_eq_of_path {v v' : V} {l : List V} (hl : IsGLSPath G l) (hh : l.head? = some v)
    (hla : l.getLast? = some v') (hlen : l.length = n + 1) : G.dist v v' = n := by
  have hn3 := h.three_le
  obtain ⟨l₁, rfl⟩ := exists_append_of_getLast? hla
  have hl₁len : l₁.length = n := by simpa using hlen
  have hne₁ : l₁ ≠ [] := by
    intro h0; rw [h0] at hl₁len; simp at hl₁len; omega
  obtain ⟨q, w, rfl⟩ : ∃ q w, l₁ = q ++ [w] :=
    ⟨l₁.dropLast, l₁.getLast hne₁, (List.dropLast_append_getLast hne₁).symm⟩
  have hqlen : q.length = n - 1 := by simp at hl₁len; omega
  have hp1 : IsGLSPath G (q ++ [w]) := hl.of_infix ⟨[], [v'], by simp⟩
  have hqne : q ≠ [] := by intro h0; rw [h0] at hqlen; simp at hqlen; omega
  have hhq : (q ++ [w]).head? = some v := by
    have : (q ++ [w] ++ [v']).head? = (q ++ [w]).head? := by
      cases q with
      | nil => exact absurd rfl hqne
      | cons a q' => simp
    rw [← this]; exact hh
  have hlast : (q ++ [w]).getLast? = some w := by simp
  have hadj : G.Adj w v' := hl.1 w v' ⟨q, [], by simp⟩
  have hdvw : G.dist v w = n - 1 := by
    obtain ⟨r, hr, hrh, hrl, hrlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist v w).1
    have hle := (reachable_dist_le_of_isGLSPath hp1 hhq hlast).2
    have hrle : r.length ≤ n := by simp at hle; omega
    have := h.unique hr hp1 hrh hhq hrl hlast hrle (by simp; omega)
    rw [this] at hrlen
    simp at hrlen
    omega
  have hdd := h.dist_adj hadj v
  have hc1 : G.dist w v = G.dist v w := SimpleGraph.dist_comm
  have hc2 : G.dist v' v = G.dist v v' := SimpleGraph.dist_comm
  have hle := (h.reach_dist v v').2
  by_contra hne
  have hd2 : G.dist v v' = n - 2 := by omega
  obtain ⟨s, hs, hsh, hsl, hslen⟩ := exists_isGLSPath_of_reachable (h.reach_dist v v').1
  obtain ⟨s', rfl⟩ := exists_append_of_getLast? hsl
  have hs'len : s'.length = n - 2 := by simp at hslen; omega
  have hp2 : IsGLSPath G (s' ++ [v', w]) := by
    rw [isGLSPath_concat]
    refine ⟨hs, hadj.symm, ?_⟩
    intro z hz hzw
    have hs'ne : s' ≠ [] := by intro h0; rw [h0] at hs'len; simp at hs'len; omega
    have hhs' : s'.head? = some v := by
      cases s' with
      | nil => exact absurd rfl hs'ne
      | cons a s'' => simpa using hsh
    have := reachable_dist_le_of_isGLSPath (hs.of_infix ⟨[], [v'], by simp⟩) hhs' (by rw [hz, hzw])
    omega
  have hhs : (s' ++ [v', w]).head? = some v := by
    have hs'ne : s' ≠ [] := by intro h0; rw [h0] at hs'len; simp at hs'len; omega
    cases s' with
    | nil => exact absurd rfl hs'ne
    | cons a s'' => simpa using hsh
  have hequal := h.unique hp2 hp1 hhs hhq (by simp) hlast (by simp; omega) (by simp; omega)
  have hqs : q = s' ++ [v'] := by
    have : (s' ++ [v']) ++ [w] = q ++ [w] := by simpa using hequal
    exact (List.append_cancel_right this).symm
  exact hl.2 v' w ⟨s', [], by rw [hqs]; simp⟩

theorem exists_geodesic_snoc {v y z : V} (hadj : G.Adj y z) (hd : G.dist v y + 1 = G.dist v z) :
    ∃ q : List V, IsGLSPath G (q ++ [y, z]) ∧ (q ++ [y, z]).head? = some v ∧
      (q ++ [y, z]).length = G.dist v z + 1 := by
  obtain ⟨r, hr, hrh, hrl, hrlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist v y).1
  obtain ⟨r', rfl⟩ := exists_append_of_getLast? hrl
  refine ⟨r', ?_, ?_, ?_⟩
  · rw [isGLSPath_concat]
    refine ⟨hr, hadj, ?_⟩
    intro w hw hwz
    have hr'h : r'.head? = some v := by
      cases r' with
      | nil => simp at hw
      | cons a r'' => simpa using hrh
    have hr' : IsGLSPath G r' := hr.of_infix ⟨[], [y], by simp⟩
    have := reachable_dist_le_of_isGLSPath hr' hr'h (by rw [hw, hwz])
    simp at hrlen
    omega
  · cases r' with
    | nil => simpa using hrh
    | cons a r'' => simpa using hrh
  · simp at hrlen ⊢
    omega

theorem exists_far (Z : Finset V) (hZ : Z.Nonempty)
    (hZ2 : ∀ z ∈ Z, ∃ y₁ ∈ Z, ∃ y₂ ∈ Z, y₁ ≠ y₂ ∧ G.Adj z y₁ ∧ G.Adj z y₂) (v : V) :
    ∃ z ∈ Z, G.dist v z = n := by
  obtain ⟨z₀, hz₀, hmax⟩ := Finset.exists_max_image Z (fun z => G.dist v z) hZ
  by_contra hne
  have hk : G.dist v z₀ < n :=
    lt_of_le_of_ne (h.reach_dist v z₀).2 (fun e => hne ⟨z₀, hz₀, e⟩)
  obtain ⟨y₁, hy₁, y₂, hy₂, hne12, hadj1, hadj2⟩ := hZ2 z₀ hz₀
  have hdist : ∀ y, y ∈ Z → G.Adj z₀ y → G.dist v y + 1 = G.dist v z₀ := by
    intro y hy hadj
    have h1 := h.dist_adj hadj v
    have h2 := hmax y hy
    have hc1 : G.dist z₀ v = G.dist v z₀ := SimpleGraph.dist_comm
    have hc2 : G.dist y v = G.dist v y := SimpleGraph.dist_comm
    omega
  have hd1 := hdist y₁ hy₁ hadj1
  have hd2 := hdist y₂ hy₂ hadj2
  obtain ⟨q₁, hq₁, hq₁h, hq₁len⟩ := h.exists_geodesic_snoc hadj1.symm hd1
  obtain ⟨q₂, hq₂, hq₂h, hq₂len⟩ := h.exists_geodesic_snoc hadj2.symm hd2
  have hequal := h.unique (u := v) (v := z₀) hq₁ hq₂ hq₁h hq₂h (by simp) (by simp) (by omega)
    (by omega)
  have : q₁ ++ [y₁] = q₂ ++ [y₂] := by
    have : (q₁ ++ [y₁]) ++ [z₀] = (q₂ ++ [y₂]) ++ [z₀] := by simpa using hequal
    exact List.append_cancel_right this
  have hl : (q₁ ++ [y₁]).getLast? = (q₂ ++ [y₂]).getLast? := by rw [this]
  simp at hl
  exact hne12 hl

theorem exists_far_cycle {a : V} (p : G.Walk a a) (hp : p.IsCycle) (v : V) :
    ∃ u ∈ p.support, G.dist v u = n := by
  classical
  have hmem : ∀ z ∈ p.support, ∃ y₁ ∈ p.support, ∃ y₂ ∈ p.support, y₁ ≠ y₂ ∧ G.Adj z y₁ ∧ G.Adj z y₂ := by
    intro z hz
    obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.1 (hp.ncard_neighborSet_toSubgraph_eq_two hz)
    have hx : x ∈ p.toSubgraph.neighborSet z := by rw [hset]; simp
    have hy : y ∈ p.toSubgraph.neighborSet z := by rw [hset]; simp
    have hx' : p.toSubgraph.Adj z x := hx
    have hy' : p.toSubgraph.Adj z y := hy
    exact ⟨x, (SimpleGraph.Walk.mem_verts_toSubgraph p).1 hx'.snd_mem, y,
      (SimpleGraph.Walk.mem_verts_toSubgraph p).1 hy'.snd_mem, hxy, p.toSubgraph.adj_sub hx',
      p.toSubgraph.adj_sub hy'⟩
  obtain ⟨z, hz, hd⟩ := h.exists_far p.support.toFinset ⟨a, by simp⟩
    (by intro z hz; simpa using hmem z (by simpa using hz)) v
  exact ⟨z, by simpa using hz, hd⟩

theorem transport {g : Equiv.Perm V} (hg : ∀ v w, G.Adj (g v) (g w) ↔ G.Adj v w) {u u' : V}
    (hd : G.dist u u' = n) (hu : g u = u) (hu' : g u' = u') :
    (∀ y, G.Adj u y → g y = y) ↔ (∀ z, G.Adj u' z → g z = z) := by
  obtain ⟨f, ⟨hmap, hinj, hsurj⟩, hf⟩ := h.exists_bijOn hd
  have hn3 := h.three_le
  have hequi : ∀ y, G.Adj u y → f (g y) = g (f y) := by
    intro y hy
    obtain ⟨l, hl, hlh, hll, hlen, hl1⟩ := h.exists_path_through hd hy
    have hlmap : IsGLSPath G (l.map g) := hl.map hg
    obtain ⟨b, hb⟩ : ∃ b, l[n - 1]? = some b :=
      ⟨l[n - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hfy : f y = b := hf l hl hlh hll hlen y b hl1 hb
    have := hf (l.map g) hlmap (by rw [List.head?_map, hlh, Option.map_some, hu])
      (by rw [List.getLast?_map, hll, Option.map_some, hu']) (by simpa using hlen) (g y) (g b)
      (by rw [List.getElem?_map, hl1]; rfl) (by rw [List.getElem?_map, hb]; rfl)
    rw [this, hfy]
  constructor
  · intro hfix z hz
    obtain ⟨y, hy, rfl⟩ := hsurj hz
    rw [← hequi y hy, hfix y hy]
  · intro hfix y hy
    have hgy : G.Adj u (g y) := by
      have := (hg u y).2 hy
      rwa [hu] at this
    have hfy : G.Adj u' (f y) := hmap hy
    have := hequi y hy
    rw [hfix (f y) hfy] at this
    exact hinj hgy hy this

theorem exists_fixed_far {π' : List V} (hπ' : IsGLSPath G π') (hlen' : π'.length = n + 2)
    {g : Equiv.Perm V} (hg : ∀ v w, G.Adj (g v) (g w) ↔ G.Adj v w) (hfix : ∀ v ∈ π', g v = v)
    (a : V) : ∃ z, g z = z ∧ G.dist a z = n := by
  classical
  have hn3 := h.three_le
  set v₀ : V := π'[0]'(by omega) with hv₀
  set v₁ : V := π'[1]'(by omega) with hv₁
  set vn : V := π'[n]'(by omega) with hvn
  set vn1 : V := π'[n + 1]'(by omega) with hvn1
  have hv₀h : π'.head? = some v₀ := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hvn1l : π'.getLast? = some vn1 := by
    rw [List.getLast?_eq_getElem?, show π'.length - 1 = n + 1 by omega,
      List.getElem?_eq_getElem (by omega)]
  have hπd : IsGLSPath G π'.dropLast := hπ'.dropLast
  have hπd_len : π'.dropLast.length = n + 1 := by simp [hlen']
  have hπd_head : π'.dropLast.head? = some v₀ := by
    rw [List.head?_dropLast]; simp [show 1 < π'.length by omega, hv₀h]
  have hπd_last : π'.dropLast.getLast? = some vn := by
    rw [List.getLast?_dropLast]
    simp [show ¬ π'.length ≤ 1 by omega]
    rw [show π'.length - 2 = n by omega, List.getElem?_eq_getElem (by omega)]
  have F1 : G.dist v₀ vn = n := h.dist_eq_of_path hπd hπd_head hπd_last hπd_len
  have hπt : IsGLSPath G π'.tail := hπ'.tail_of_cons
  have hπt_len : π'.tail.length = n + 1 := by simp [hlen']
  have hπt_head : π'.tail.head? = some v₁ := by
    rw [List.head?_tail, List.getElem?_eq_getElem (by omega)]
  have hπt_last : π'.tail.getLast? = some vn1 := by
    rw [List.getLast?_tail]
    simp [show π'.length ≠ 1 by omega, hvn1l]
  have F2 : G.dist v₁ vn1 = n := h.dist_eq_of_path hπt hπt_head hπt_last hπt_len
  have hadj : G.Adj vn vn1 := hπ'.adj_of_getElem?_eq (i := n)
    (by rw [List.getElem?_eq_getElem (by omega)]) (by rw [List.getElem?_eq_getElem (by omega)])
  have F3 : G.dist vn1 v₀ + 1 = n := by
    have h1 := h.dist_adj hadj v₀
    have hc : G.dist vn v₀ = n := by rw [SimpleGraph.dist_comm]; exact F1
    have h2 := (h.reach_dist vn1 v₀).2
    omega
  obtain ⟨γ, hγ, hγh, hγl, hγlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist vn1 v₀).1
  have hγlen' : γ.length = n := by omega
  have hmem0 : v₀ ∈ π' := List.getElem_mem _
  have hmemn1 : vn1 ∈ π' := List.getElem_mem _
  have hγg : γ.map g = γ := by
    have hmp : IsGLSPath G (γ.map g) := hγ.map hg
    exact h.unique (u := vn1) (v := v₀) hmp hγ
      (by rw [List.head?_map, hγh, Option.map_some, hfix vn1 hmemn1])
      hγh (by rw [List.getLast?_map, hγl, Option.map_some, hfix v₀ hmem0]) hγl
      (by simp [hγlen']) (by omega)
  have hγfix : ∀ x ∈ γ, g x = x := map_eq_self_iff_mem hγg
  set Z : Finset V := π'.toFinset ∪ γ.toFinset with hZ
  have hinZ : ∀ x, x ∈ π' ∨ x ∈ γ → x ∈ Z := by
    intro x hx
    rcases hx with hx | hx
    · exact Finset.mem_union_left _ (List.mem_toFinset.2 hx)
    · exact Finset.mem_union_right _ (List.mem_toFinset.2 hx)
  have hcase0 : ∃ y₁ ∈ Z, ∃ y₂ ∈ Z, y₁ ≠ y₂ ∧ G.Adj v₀ y₁ ∧ G.Adj v₀ y₂ := by
    obtain ⟨γ₁, hγ₁⟩ := exists_append_of_getLast? hγl
    have hγ₁len : γ₁.length = n - 1 := by simp [hγ₁] at hγlen'; omega
    have hγ₁ne : γ₁ ≠ [] := by intro h0; rw [h0] at hγ₁len; simp at hγ₁len; omega
    obtain ⟨γ₂, u, hγ₂⟩ : ∃ γ₂ u, γ₁ = γ₂ ++ [u] :=
      ⟨γ₁.dropLast, γ₁.getLast hγ₁ne, (List.dropLast_append_getLast hγ₁ne).symm⟩
    have hγeq : γ = γ₂ ++ [u, v₀] := by rw [hγ₁, hγ₂]; simp
    have hu_adj : G.Adj u v₀ := hγ.1 u v₀ ⟨γ₂, [], by rw [hγeq]; simp⟩
    have hv₁_adj : G.Adj v₀ v₁ := hπ'.adj_of_getElem?_eq (i := 0)
      (by rw [List.getElem?_eq_getElem (by omega)]) (by rw [List.getElem?_eq_getElem (by omega)])
    refine ⟨v₁, hinZ _ (Or.inl (List.getElem_mem _)), u,
      hinZ _ (Or.inr (by rw [hγeq]; simp)), ?_, hv₁_adj, hu_adj.symm⟩
    intro hvu
    have hpath : IsGLSPath G (γ₂ ++ [u]) := hγ.of_infix ⟨[], [v₀], by rw [hγeq]; simp⟩
    have hlen2 : (γ₂ ++ [u]).length = n - 1 := by simp [hγeq] at hγlen' ⊢; omega
    have hhead : (γ₂ ++ [u]).head? = some vn1 := by
      cases γ₂ with
      | nil => simp at hlen2; omega
      | cons x γ₃ => simpa [hγeq] using hγh
    have := reachable_dist_le_of_isGLSPath hpath hhead (v := u) (by simp)
    rw [← hvu] at this hlen2
    have hc : G.dist vn1 v₁ = n := by rw [SimpleGraph.dist_comm]; exact F2
    omega
  have hcasen1 : ∃ y₁ ∈ Z, ∃ y₂ ∈ Z, y₁ ≠ y₂ ∧ G.Adj vn1 y₁ ∧ G.Adj vn1 y₂ := by
    obtain ⟨x, γ', hγ'⟩ : ∃ x γ', γ = x :: γ' := by
      cases γ with
      | nil => simp at hγlen'; omega
      | cons x γ' => exact ⟨x, γ', rfl⟩
    obtain ⟨w, rest, hrest⟩ : ∃ w rest, γ' = w :: rest := by
      cases γ' with
      | nil => simp [hγ'] at hγlen'; omega
      | cons w rest => exact ⟨w, rest, rfl⟩
    have hx : x = vn1 := by
      rw [hγ'] at hγh
      simpa using hγh
    have hγ'' : γ = x :: w :: rest := by rw [hγ', hrest]
    have hadj1 : G.Adj x w := by
      have := (isGLSPath_cons_cons.1 (hγ'' ▸ hγ)).1
      exact this
    have hvn_adj : G.Adj vn1 vn := hadj.symm
    refine ⟨vn, hinZ _ (Or.inl (List.getElem_mem _)), w,
      hinZ _ (Or.inr (by rw [hγ'']; simp)), ?_, hvn_adj, hx ▸ hadj1⟩
    intro hvw
    have hpath : IsGLSPath G (w :: rest) := (hγ'' ▸ hγ).tail
    have hhead : (w :: rest).head? = some w := rfl
    have hlast : (w :: rest).getLast? = some v₀ := by
      rw [hγ''] at hγl
      simpa [List.getLast?_cons_cons] using hγl
    have := reachable_dist_le_of_isGLSPath hpath hhead hlast
    have hlen3 : (w :: rest).length = n - 1 := by rw [hγ''] at hγlen'; simp at hγlen' ⊢; omega
    rw [← hvw] at this hlen3
    have hc : G.dist vn v₀ = n := by rw [SimpleGraph.dist_comm]; exact F1
    omega
  have hZ2 : ∀ z ∈ Z, ∃ y₁ ∈ Z, ∃ y₂ ∈ Z, y₁ ≠ y₂ ∧ G.Adj z y₁ ∧ G.Adj z y₂ := by
    intro z hz
    rcases Finset.mem_union.1 hz with hzπ | hzγ
    · have hzπ' : z ∈ π' := List.mem_toFinset.1 hzπ
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hzπ'
      by_cases hi0 : i = 0
      · subst hi0; exact hcase0
      by_cases hin1 : i = n + 1
      · subst hin1; exact hcasen1
      · obtain ⟨y₁, hy₁, y₂, hy₂, hne, ha1, ha2⟩ := hπ'.two_neighbors (i := i) (by omega) (by omega)
        exact ⟨y₁, hinZ _ (Or.inl hy₁), y₂, hinZ _ (Or.inl hy₂), hne, ha1, ha2⟩
    · have hzγ' : z ∈ γ := List.mem_toFinset.1 hzγ
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hzγ'
      by_cases hj0 : j = 0
      · have hγ0 : γ[j]'hj = vn1 := by
          subst hj0
          have := hγh
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
          exact Option.some.inj this
        rw [hγ0]; exact hcasen1
      by_cases hjl : j = n - 1
      · have hγl' : γ[j]'hj = v₀ := by
          have := hγl
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
          have h2 := Option.some.inj this
          rw [← h2]
          congr 1
          omega
        rw [hγl']; exact hcase0
      · obtain ⟨y₁, hy₁, y₂, hy₂, hne, ha1, ha2⟩ := hγ.two_neighbors (i := j) (by omega) (by omega)
        exact ⟨y₁, hinZ _ (Or.inr hy₁), y₂, hinZ _ (Or.inr hy₂), hne, ha1, ha2⟩
  obtain ⟨z, hzZ, hd⟩ := h.exists_far Z ⟨v₀, hinZ v₀ (Or.inl hmem0)⟩ hZ2 a
  refine ⟨z, ?_, hd⟩
  rcases Finset.mem_union.1 hzZ with hz | hz
  · exact hfix z (List.mem_toFinset.1 hz)
  · exact hγfix z (List.mem_toFinset.1 hz)

theorem exists_path_through_far {a z y z' : V} (hd : G.dist a z = n) (hay : G.Adj a y)
    (hzz' : G.Adj z' z) (hyz' : G.dist y z' = n - 2) :
    ∃ l : List V, IsGLSPath G l ∧ l.head? = some a ∧ l.getLast? = some z ∧ l.length = n + 1 ∧
      l[1]? = some y ∧ l[n - 1]? = some z' := by
  have hn3 := h.three_le
  have hdaz' : n ≤ G.dist a z' + 1 := by
    have h1 := h.dist_adj hzz' a
    have h2 := (h.reach_dist z' a).2
    have hc1 : G.dist z a = n := by rw [SimpleGraph.dist_comm]; exact hd
    have hc2 : G.dist z' a = G.dist a z' := SimpleGraph.dist_comm
    omega
  have hdyz : n ≤ G.dist y z + 1 := by
    have h1 := h.dist_adj hay z
    omega
  obtain ⟨σ, hσ, hσh, hσl, hσlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist y z').1
  have hσlen' : σ.length = n - 1 := by omega
  obtain ⟨σ₁, rfl⟩ := exists_append_of_getLast? hσl
  have hσ₁len : σ₁.length = n - 2 := by simp at hσlen'; omega
  obtain ⟨ρ, rfl⟩ : ∃ ρ, σ₁ = y :: ρ := by
    cases σ₁ with
    | nil => simp at hσ₁len; omega
    | cons x ρ =>
      refine ⟨ρ, ?_⟩
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hσh
      rw [hσh]
  have hρlen : ρ.length = n - 3 := by simp at hσ₁len; omega
  have hstep1 : ∀ w, (ρ ++ [z']).head? = some w → w ≠ a := by
    intro w hw hwa
    have hpath : IsGLSPath G (ρ ++ [z']) := by
      have := hσ.tail
      simpa using this
    have := reachable_dist_le_of_isGLSPath hpath hw (v := z') (by simp)
    simp only [List.length_append, List.length_singleton] at this
    rw [hwa] at this
    omega
  have hstep2 : ∀ w, (y :: ρ).getLast? = some w → w ≠ z := by
    intro w hw hwz
    have hpath : IsGLSPath G (y :: ρ) := hσ.of_infix ⟨[], [z'], by simp⟩
    have := reachable_dist_le_of_isGLSPath hpath (u := y) (by simp) hw
    simp only [List.length_cons] at this
    rw [hwz] at this
    omega
  have hl_eq : a :: y :: (ρ ++ [z', z]) = (a :: y :: ρ ++ [z']) ++ [z] := by simp
  have hl_eq2 : a :: y :: (ρ ++ [z', z]) = (a :: y :: ρ) ++ [z', z] := by simp
  refine ⟨a :: y :: (ρ ++ [z', z]), ?_, by simp, by rw [hl_eq]; exact List.getLast?_concat ..,
    by simp [hρlen]; omega, by simp, ?_⟩
  · rw [isGLSPath_cons_cons]
    refine ⟨hay, ?_, ?_⟩
    · intro w hw
      apply hstep1 w
      cases ρ with
      | nil => simpa using hw
      | cons x r => simpa using hw
    · have : y :: (ρ ++ [z', z]) = (y :: ρ) ++ [z', z] := by simp
      rw [this, isGLSPath_concat]
      exact ⟨by simpa using hσ, hzz', hstep2⟩
  · rw [hl_eq2, List.getElem?_append_right (by simp; omega)]
    have : (a :: y :: ρ).length = n - 1 := by simp [hρlen]; omega
    rw [this, show n - 1 - (n - 1) = 0 by omega]
    rfl

theorem exists_adj_dist_lt {v w : V} (hvw : v ≠ w) :
    ∃ a, G.Adj v a ∧ G.dist a w + 1 = G.dist v w := by
  obtain ⟨l, hl, hlh, hll, hlen⟩ := exists_isGLSPath_of_reachable (h.reach_dist v w).1
  obtain ⟨a, t, rfl⟩ : ∃ a t, l = v :: a :: t := by
    cases l with
    | nil => simp at hlh
    | cons x l' =>
      simp only [List.head?_cons, Option.some.injEq] at hlh
      cases l' with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hll
        exact absurd (hlh.symm.trans hll) hvw
      | cons a t => exact ⟨a, t, by rw [hlh]⟩
  have hadj : G.Adj v a := (isGLSPath_cons_cons.1 hl).1
  refine ⟨a, hadj, ?_⟩
  have h1 := reachable_dist_le_of_isGLSPath (isGLSPath_cons_cons.1 hl).2.2 (u := a) rfl
    (by simpa [List.getLast?_cons_cons] using hll)
  have h2 := h.connected.dist_triangle (u := v) (v := a) (w := w)
  have h3 : G.dist v a = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj
  simp only [List.length_cons] at hlen h1
  omega

theorem eq_one_of_fix {π π' : List V} (hπ' : IsGLSPath G π')
    (hlen : π.length = n + 1) (hlen' : π'.length = n + 2) (hpre : π <+: π')
    {g : Equiv.Perm V} (hg : ∀ v w, G.Adj (g v) (g w) ↔ G.Adj v w) (hfix : ∀ v ∈ π', g v = v)
    (hfixΓ : ∀ v ∈ interiorVertices π, ∀ w, G.Adj v w → g w = w) : g = 1 := by
  classical
  have hn3 := h.three_le
  have hπ1 : π[1]'(by omega) = π'[1]'(by omega) := hpre.getElem (by omega)
  have hπ2 : π[2]'(by omega) = π'[2]'(by omega) := hpre.getElem (by omega)
  set v₁ : V := π'[1]'(by omega) with hv₁
  set v₂ : V := π'[2]'(by omega) with hv₂
  have hv₁fix : ∀ w, G.Adj v₁ w → g w = w := by
    have := hfixΓ (π[1]'(by omega)) (getElem_mem_interiorVertices (l := π) (i := 1) (by omega) (by omega))
    rwa [hπ1] at this
  have hv₂fix : ∀ w, G.Adj v₂ w → g w = w := by
    have := hfixΓ (π[2]'(by omega)) (getElem_mem_interiorVertices (l := π) (i := 2) (by omega) (by omega))
    rwa [hπ2] at this
  have hv₁mem : v₁ ∈ π' := List.getElem_mem _
  have hv₂mem : v₂ ∈ π' := List.getElem_mem _
  have hadj12 : G.Adj v₁ v₂ := hπ'.adj_of_getElem?_eq (i := 1)
    (by rw [List.getElem?_eq_getElem (by omega)]) (by rw [List.getElem?_eq_getElem (by omega)])
  let Fix : V → Prop := fun v => ∀ w, G.Adj v w → g w = w
  have hall : ∀ v, Fix v := by
    by_contra hcon
    push Not at hcon
    have hex : ∃ k, ∃ v, ¬ Fix v ∧ G.dist v v₁ = k := by
      obtain ⟨v, hv⟩ := hcon
      exact ⟨_, v, hv, rfl⟩
    obtain ⟨v, hv, hdv⟩ := Nat.find_spec hex
    have hmin : ∀ u, ¬ Fix u → Nat.find hex ≤ G.dist u v₁ := fun u hu =>
      Nat.find_min' hex ⟨u, hu, rfl⟩
    have hmin' : ∀ u, G.dist u v₁ < G.dist v v₁ → Fix u := by
      intro u hu
      by_contra hu'
      have := hmin u hu'
      omega
    obtain ⟨a, b, hva, hab, hFa, hFb, hbv, hga, hgb⟩ : ∃ a b, G.Adj v a ∧ G.Adj a b ∧ Fix a ∧
        Fix b ∧ b ≠ v ∧ g a = a ∧ g b = b := by
      by_cases hd1 : G.dist v v₁ = 1
      · have hadj : G.Adj v v₁ := SimpleGraph.dist_eq_one_iff_adj.1 hd1
        refine ⟨v₁, v₂, hadj, hadj12, hv₁fix, hv₂fix, ?_, hfix _ hv₁mem, hfix _ hv₂mem⟩
        intro hbv
        exact hv (hbv ▸ hv₂fix)
      · have hvv₁ : v ≠ v₁ := by
          intro hvv
          exact hv (hvv ▸ hv₁fix)
        have hd2 : 2 ≤ G.dist v v₁ := by
          have : G.dist v v₁ ≠ 0 := by
            intro h0
            exact hvv₁ (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.1 h0 |>.resolve_right
              (not_not.2 (h.reach_dist v v₁).1))
          omega
        obtain ⟨a, hva, hda⟩ := h.exists_adj_dist_lt hvv₁
        have hav₁ : a ≠ v₁ := by
          intro e; rw [e] at hda; simp at hda; omega
        obtain ⟨b, hab, hdb⟩ := h.exists_adj_dist_lt hav₁
        have hFa : Fix a := hmin' a (by omega)
        have hFb : Fix b := hmin' b (by omega)
        refine ⟨a, b, hva, hab, hFa, hFb, ?_, ?_, ?_⟩
        · intro hbv; rw [hbv] at hdb; omega
        · exact hFb a hab.symm
        · exact hFa b hab
    have hgv : g v = v := hFa v hva.symm
    obtain ⟨z, hgz, hdz⟩ := h.exists_fixed_far hπ' hlen' hg hfix a
    have hFz : Fix z := (h.transport hg hdz hga hgz).1 hFa
    obtain ⟨a', ha'adj, ha'v, ha'b⟩ : ∃ a', G.Adj a a' ∧ a' ≠ v ∧ a' ≠ b := by
      by_contra hcon
      push Not at hcon
      have hsub : G.neighborSet a ⊆ {v, b} := fun x hx => by
        by_cases hxv : x = v
        · left; exact hxv
        · right; exact hcon x hx hxv
      have h1 := Set.encard_le_encard hsub
      have h2 : ({v, b} : Set V).encard ≤ 2 := by
        calc ({v, b} : Set V).encard ≤ ({b} : Set V).encard + 1 := Set.encard_insert_le _ _
          _ = 2 := by simp; norm_num
      have h3 := le_trans (h.valency a) (le_trans h1 h2)
      norm_num at h3
    obtain ⟨f, ⟨hmap, hinj, hsurj⟩, hf⟩ := h.exists_bijOn hdz
    set z' : V := f a' with hz'
    have hz'adj : G.Adj z z' := hmap ha'adj
    have hgz' : g z' = z' := hFz z' hz'adj
    have hdaz' : G.dist a z' + 1 = n := by
      have h1 := h.dist_adj hz'adj.symm a
      have h2 := (h.reach_dist z' a).2
      have hc1 : G.dist z a = n := by rw [SimpleGraph.dist_comm]; exact hdz
      have hc2 : G.dist z' a = G.dist a z' := SimpleGraph.dist_comm
      omega
    have hfar : ∀ y, G.Adj a y → y ≠ a' → G.dist y z' = n := by
      intro y hy hya'
      have h1 := h.dist_adj hy z'
      have hc1 : G.dist a z' = G.dist z' a := SimpleGraph.dist_comm
      have h3 := (h.reach_dist y z').2
      by_contra hne
      have hd2 : G.dist y z' = n - 2 := by omega
      obtain ⟨l, hl, hlh, hll, hlen2, hl1, hln1⟩ :=
        h.exists_path_through_far hdz hy hz'adj.symm hd2
      have hfy : f y = z' := hf l hl hlh hll hlen2 y z' hl1 hln1
      exact hya' (hinj hy ha'adj hfy)
    have hdvz' : G.dist v z' = n := hfar v hva.symm (fun e => ha'v e.symm)
    have hdbz' : G.dist b z' = n := hfar b hab (fun e => ha'b e.symm)
    have hFz' : Fix z' := (h.transport hg hdbz' hgb hgz').1 hFb
    have hFv : Fix v := (h.transport hg hdvz' hgv hgz').2 hFz'
    exact hv hFv
  ext w
  obtain ⟨w', hw'⟩ : (G.neighborSet w).Nonempty := by
    have := h.valency w
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at this
    simp at this
  have := hall w' w hw'.symm
  simpa using this

end PolyHyp

end CFSG.GH74.BNPair
