module

public import CFSG.Certificates.Kernel.SporLatOmegaSound

public section

namespace CFSG.KC.SLOm

open CFSG.QuasithinUnique.Ch1.SporLat

section Run

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

theorem push_get_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt h]

theorem push_get_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

theorem push_get_of_eq {α : Type} [Inhabited α] {a : Array α} {x : α} {i : Nat} (h : i = a.size) :
    (a.push x)[i]! = x := by
  subst h
  exact push_get_eq

theorem modify_get {α : Type} [Inhabited α] {a : Array α} {l j : Nat} {f : α → α} :
    (a.modify l f)[j]! = if j = l ∧ l < a.size then f a[l]! else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.modify l f) j (by simpa using hj), Array.getElem_modify]
    by_cases e : l = j
    · subst e
      rw [if_pos rfl, if_pos ⟨rfl, hj⟩, getElem!_pos a l hj]
    · rw [if_neg e, if_neg (fun h => e h.1.symm), getElem!_pos a j hj]
  · rw [getElem!_neg (a.modify l f) j (by simpa using hj), getElem!_neg a j hj]
    rw [if_neg (fun (h : j = l ∧ l < a.size) => hj (h.1 ▸ h.2))]

theorem idxL_some {x : Lab} : ∀ {l : List Lab} {j : Nat}, idxL x l = some j →
    j < l.length ∧ l[j]! = x
  | [], _, h => by simp [idxL] at h
  | y :: l, j, h => by
    unfold idxL at h
    by_cases hx : x = y
    · rw [if_pos hx] at h
      cases h
      exact ⟨by simp, by simp [hx]⟩
    · rw [if_neg hx] at h
      cases e : idxL x l with
      | none => rw [e] at h; simp at h
      | some j' =>
        rw [e] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := idxL_some e
        exact ⟨by simp; omega, by simpa using h2⟩

theorem idxL_none {x : Lab} : ∀ {l : List Lab}, idxL x l = none → x ∉ l
  | [], _ => by simp
  | y :: l, h => by
    unfold idxL at h
    by_cases hx : x = y
    · rw [if_pos hx] at h
      simp at h
    · rw [if_neg hx] at h
      cases e : idxL x l with
      | some j => rw [e] at h; simp at h
      | none =>
        intro hm
        rcases List.mem_cons.1 hm with hm | hm
        · exact hx hm
        · exact idxL_none e hm

theorem arr_get_of_list {a : Array Lab} {j : Nat} {x : Lab} (h : a.toList[j]! = x)
    (hj : j < a.size) : a[j]! = x := by
  rw [getElem!_pos a j hj]
  rw [getElem!_pos a.toList j (by simpa using hj)] at h
  simpa using h

variable (actF : Nat → Lab → Lab) (m : Nat) (Δ : Lab) (Lset : List Lab)

def Inv (s : St4 Lab) (i l₀ : Nat) : Prop :=
  0 < s.1.size ∧ s.1[0]! = Δ ∧ i ≤ s.1.size ∧ s.1.toList.Nodup ∧ (∀ x ∈ s.1.toList, x ∈ Lset) ∧
  s.2.1.size = s.1.size ∧ s.2.2.1.size = s.1.size ∧
  (∀ k < s.1.size, 0 < k → s.2.1[k]! < k ∧ s.2.2.1[k]! < m ∧
    s.1[k]! = actF s.2.2.1[k]! s.1[s.2.1[k]!]! ∧
    (s.2.1[k]! < i ∨ (s.2.1[k]! = i ∧ s.2.2.1[k]! < l₀)) ∧
    (s.2.2.2[s.2.2.1[k]!]!)[s.2.1[k]!]! = k) ∧
  s.2.2.2.size = m ∧
  ∀ l < m, (s.2.2.2[l]!).size = (if l < l₀ then i + 1 else i) ∧
    ∀ k < (s.2.2.2[l]!).size, (s.2.2.2[l]!)[k]! < s.1.size ∧
      s.1[(s.2.2.2[l]!)[k]!]! = actF l s.1[k]!

@[expose] def Final (O : OmegaData Lab) : Prop :=
  0 < O.lbl.size ∧ O.lbl[0]! = Δ ∧ O.lbl.toList.Nodup ∧ (∀ x ∈ O.lbl.toList, x ∈ Lset) ∧
  (∀ l < m, ∀ k < O.lbl.size, (O.pn[l]!)[k]! < O.lbl.size ∧
    O.lbl[(O.pn[l]!)[k]!]! = actF l O.lbl[k]!) ∧
  ∀ k < O.lbl.size, 0 < k → O.par[k]! < k ∧ O.via[k]! < m ∧ (O.pn[O.via[k]!]!)[O.par[k]!]! = k

variable {actF m Δ Lset}

theorem inv_step {s : St4 Lab} {i l₀ : Nat} {L : Lab} (h : Inv actF m Δ Lset s i l₀)
    (hl : l₀ < m) (hi : i < s.1.size) (hL : s.1[i]! = L) (hcl : actF l₀ L ∈ Lset) :
    Inv actF m Δ Lset (omStep actF L i s l₀) i (l₀ + 1) ∧ (omStep actF L i s l₀).1[i]! = L ∧
      s.1.size ≤ (omStep actF L i s l₀).1.size := by
  obtain ⟨h0, hΔ, hile, hnd, hin, hpar, hvia, htree, hpn, hrow⟩ := h
  obtain ⟨hrl, hrow0⟩ := hrow l₀ hl
  rw [if_neg (by omega)] at hrl
  unfold omStep
  cases hj : idxL (actF l₀ L) s.1.toList with
  | some j =>
    unfold Inv
    try dsimp only
    obtain ⟨hjl, hjx⟩ := idxL_some hj
    have hjs : j < s.1.size := by simpa using hjl
    have hjx' : s.1[j]! = actF l₀ L := arr_get_of_list hjx hjs
    refine ⟨⟨h0, hΔ, hile, hnd, hin, hpar, hvia, fun k hk hk0 => ?_, by simpa using hpn,
      fun l hl' => ?_⟩, hL, le_refl _⟩
    · obtain ⟨t1, t2, t3, t4, t5⟩ := htree k hk hk0
      refine ⟨t1, t2, t3, by omega, ?_⟩
      try dsimp only
      rw [modify_get]
      by_cases e : s.2.2.1[k]! = l₀
      · rw [if_pos ⟨e, by omega⟩, ← e]
        have hpi : s.2.1[k]! < (s.2.2.2[s.2.2.1[k]!]!).size := by
          rw [e, hrl]
          omega
        rw [push_get_lt hpi]
        exact t5
      · rw [if_neg (fun h => e h.1)]
        exact t5
    · try dsimp only
      rw [modify_get]
      by_cases e : l = l₀
      · subst e
        rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
        refine ⟨by simp [hrl], fun k hk => ?_⟩
        rw [Array.size_push, hrl] at hk
        by_cases hk' : k < i
        · rw [push_get_lt (by omega)]
          exact hrow0 k (by omega)
        · have : k = i := by omega
          subst this
          rw [push_get_of_eq hrl.symm, hjx', hL]
          exact ⟨hjs, rfl⟩
      · rw [if_neg (fun h => e h.1)]
        obtain ⟨r1, r2⟩ := hrow l hl'
        refine ⟨?_, r2⟩
        rw [r1]
        by_cases hl0 : l < l₀
        · rw [if_pos hl0, if_pos (by omega)]
        · rw [if_neg hl0, if_neg (by omega)]
  | none =>
    unfold Inv
    try dsimp only
    have hM : actF l₀ L ∉ s.1.toList := idxL_none hj
    refine ⟨⟨by simp, ?_, by simp; omega, ?_, ?_, by simp [hpar], by simp [hvia], ?_,
      by simpa using hpn, fun l hl' => ?_⟩, ?_, by simp⟩
    · try dsimp only
      rw [push_get_lt h0]
      exact hΔ
    · try dsimp only
      rw [Array.toList_push]
      exact List.nodup_append.2 ⟨hnd, List.nodup_singleton _, by
        intro a ha b hb e
        rw [List.mem_singleton] at hb
        subst hb e
        exact hM ha⟩
    · try dsimp only
      intro x hx
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hin x hx
      · exact hcl
    · try dsimp only
      intro k hk hk0
      rw [Array.size_push] at hk
      by_cases hks : k < s.1.size
      · obtain ⟨t1, t2, t3, t4, t5⟩ := htree k hks hk0
        rw [push_get_lt (by omega : k < s.2.1.size), push_get_lt (by omega : k < s.2.2.1.size),
          push_get_lt hks, push_get_lt (by omega : s.2.1[k]! < s.1.size)]
        refine ⟨t1, t2, t3, by omega, ?_⟩
        rw [modify_get]
        by_cases e : s.2.2.1[k]! = l₀
        · rw [if_pos ⟨e, by omega⟩, ← e]
          have hpi : s.2.1[k]! < (s.2.2.2[s.2.2.1[k]!]!).size := by
            rw [e, hrl]
            rcases t4 with t4 | t4
            · exact t4
            · omega
          rw [push_get_lt hpi]
          exact t5
        · rw [if_neg (fun h => e h.1)]
          exact t5
      · have hk' : k = s.1.size := by omega
        subst hk'
        rw [push_get_of_eq hpar.symm, push_get_of_eq hvia.symm, push_get_eq, push_get_lt hi, hL]
        refine ⟨hi, hl, rfl, Or.inr ⟨rfl, by omega⟩, ?_⟩
        rw [modify_get, if_pos ⟨rfl, by omega⟩, push_get_of_eq hrl.symm]
    · try dsimp only
      rw [modify_get]
      by_cases e : l = l₀
      · subst e
        rw [if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
        refine ⟨by simp [hrl], fun k hk => ?_⟩
        rw [Array.size_push, hrl] at hk
        by_cases hk' : k < i
        · rw [push_get_lt (by omega)]
          obtain ⟨r1, r2⟩ := hrow0 k (by omega)
          refine ⟨by simp; omega, ?_⟩
          rw [push_get_lt r1, push_get_lt (by omega)]
          exact r2
        · have : k = i := by omega
          subst this
          rw [push_get_of_eq hrl.symm, push_get_eq, push_get_lt hi, hL]
          exact ⟨by simp, rfl⟩
      · rw [if_neg (fun h => e h.1)]
        obtain ⟨r1, r2⟩ := hrow l hl'
        refine ⟨?_, fun k hk => ?_⟩
        · rw [r1]
          by_cases hl0 : l < l₀
          · rw [if_pos hl0, if_pos (by omega)]
          · rw [if_neg hl0, if_neg (by omega)]
        · obtain ⟨q1, q2⟩ := r2 k hk
          have hki : k < s.1.size := by
            rw [r1] at hk
            split_ifs at hk <;> omega
          refine ⟨by simp; omega, ?_⟩
          rw [push_get_lt q1, push_get_lt hki]
          exact q2
    · try dsimp only
      rw [push_get_lt hi]
      exact hL

theorem inv_fold {L : Lab} {i : Nat} (hclL : ∀ l < m, actF l L ∈ Lset) :
    ∀ (k l₀ : Nat) (s : St4 Lab), l₀ + k = m → Inv actF m Δ Lset s i l₀ → i < s.1.size →
      s.1[i]! = L →
      Inv actF m Δ Lset ((List.range' l₀ k).foldl (omStep actF L i) s) i m ∧
        i < ((List.range' l₀ k).foldl (omStep actF L i) s).1.size
  | 0, l₀, s, hk, h, hi, _ => by
    have : l₀ = m := by omega
    subst this
    exact ⟨h, hi⟩
  | k + 1, l₀, s, hk, h, hi, hL => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨h', hL', hsz⟩ := inv_step h (by omega) hi hL (hclL l₀ (by omega))
    exact inv_fold hclL k (l₀ + 1) _ (by omega) h' (by omega) hL'

theorem inv_next {s : St4 Lab} {i : Nat} (h : Inv actF m Δ Lset s i m) (hi : i < s.1.size) :
    Inv actF m Δ Lset s (i + 1) 0 := by
  obtain ⟨h0, hΔ, hile, hnd, hin, hpar, hvia, htree, hpn, hrow⟩ := h
  refine ⟨h0, hΔ, by omega, hnd, hin, hpar, hvia, fun k hk hk0 => ?_, hpn, fun l hl => ?_⟩
  · obtain ⟨t1, t2, t3, t4, t5⟩ := htree k hk hk0
    exact ⟨t1, t2, t3, Or.inl (by omega), t5⟩
  · obtain ⟨r1, r2⟩ := hrow l hl
    rw [if_pos hl] at r1
    exact ⟨by rw [r1]; simp, r2⟩

theorem size_le_of_inv {s : St4 Lab} {i l₀ : Nat} (h : Inv actF m Δ Lset s i l₀) :
    s.1.size ≤ Lset.length := by
  have hsub : s.1.toList.Subperm Lset := List.subperm_of_subset h.2.2.2.1 h.2.2.2.2.1
  simpa using hsub.length_le

theorem omRun_spec {cap : Nat} (hclose : ∀ l < m, ∀ x ∈ Lset, actF l x ∈ Lset)
    (hcap : Lset.length ≤ cap) :
    ∀ (f : Nat) (s : St4 Lab) (i : Nat), Inv actF m Δ Lset s i 0 → Lset.length + 1 ≤ f + i →
      ∃ R, omRun actF m cap f s i = some R ∧ R.2 = true ∧ Final actF m Δ Lset R.1
  | 0, s, i, h, hf => by
    have := size_le_of_inv h
    have := h.2.2.1
    omega
  | f + 1, s, i, h, hf => by
    have hsz := size_le_of_inv h
    unfold omRun
    by_cases hi : i < s.1.size
    · rw [if_pos (by simp [hi]; omega)]
      have hLs : s.1[i]! ∈ Lset := h.2.2.2.2.1 _ (getElem!_mem hi)
      obtain ⟨h', hi'⟩ := inv_fold (fun l hl => hclose l hl _ hLs) m 0 s (by omega) h hi rfl
      exact omRun_spec hclose hcap f _ (i + 1) (inv_next h' hi') (by omega)
    · rw [if_neg (by simp [hi])]
      have hie : i = s.1.size := by have := h.2.2.1; omega
      obtain ⟨h0, hΔ, -, hnd, hin, -, -, htree, -, hrow⟩ := h
      refine ⟨_, rfl, by simp [hie], h0, hΔ, hnd, hin, fun l hl k hk => ?_, fun k hk hk0 => ?_⟩
      · obtain ⟨r1, r2⟩ := hrow l hl
        rw [if_neg (by omega)] at r1
        exact r2 k (by rw [r1, hie]; exact hk)
      · obtain ⟨t1, t2, -, -, t5⟩ := htree k hk hk0
        exact ⟨t1, t2, t5⟩

theorem omTwin_spec {cap fuel : Nat} (hΔ : Δ ∈ Lset)
    (hclose : ∀ l < m, ∀ x ∈ Lset, actF l x ∈ Lset) (hcap : Lset.length ≤ cap)
    (hfuel : Lset.length < fuel) :
    ∃ R, omTwin actF m Δ cap fuel = some R ∧ R.2 = true ∧ Final actF m Δ Lset R.1 := by
  refine omRun_spec hclose hcap fuel _ 0 ?_ (by omega)
  refine ⟨by simp, by simp, by simp, by simp, by simpa using hΔ, by simp, by simp,
    fun k hk hk0 => by simp at hk; omega, by simp, fun l hl => ⟨?_, fun k hk => ?_⟩⟩
  · rw [if_neg (by omega)]
    simp [getElem!_pos (Array.replicate m (#[] : Array Nat)) l (by simpa using hl)]
  · simp [getElem!_pos (Array.replicate m (#[] : Array Nat)) l (by simpa using hl)] at hk

end Run

end CFSG.KC.SLOm

end
