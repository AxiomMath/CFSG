module

public import Certificates.Data.Kernel.KeyTreeChunks
import Mathlib.Data.Finset.Card

public section

namespace CFSG.KC.KeyTree

def KT.ents : KT → List (Nat × Nat)
  | .leaf => []
  | .node l k v r => l.ents ++ (k, v) :: r.ents

theorem band_true {a b : Bool}
    (h : (Bool.rec (motive := fun _ => Bool) false b a : Bool) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h (by simp)
  · exact ⟨rfl, h⟩

theorem KT.find_ents : ∀ (t : KT) {x v : Nat}, t.find x = v + 1 → (x, v) ∈ t.ents
  | .leaf, _, _, h => absurd h (by simp [KT.find])
  | .node l k w r, x, v, h => by
    have e : (KT.node l k w r).find x = nIf(Nat.blt x k, l.find x, nIf(Nat.beq x k,
        Nat.succ w, r.find x)) := rfl
    rw [e] at h
    simp only [KT.ents, List.mem_append, List.mem_cons, Prod.mk.injEq]
    cases hb : Nat.blt x k
    · rw [hb] at h
      cases hc : Nat.beq x k
      · rw [hc] at h
        exact Or.inr (Or.inr (KT.find_ents r h))
      · rw [hc] at h
        exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true hc, (Nat.succ.inj h).symm⟩)
    · rw [hb] at h
      exact Or.inl (KT.find_ents l h)

theorem KT.size_eq : ∀ t : KT, t.size = t.ents.length
  | .leaf => rfl
  | .node l k v r => by
    change Nat.succ (Nat.add l.size r.size) = _
    rw [KT.size_eq l, KT.size_eq r]
    simp only [KT.ents, List.length_append, List.length_cons, Nat.add_eq]
    omega

theorem nthC_eq : ∀ (cs : List (List Nat)) (c : Nat), nthC cs c = cs.getD c []
  | [], _ => by
    change [] = _
    simp
  | _ :: _, 0 => rfl
  | _ :: cs, c + 1 => by
    rw [List.getD_cons_succ]
    exact nthC_eq cs c

theorem getD_eq {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem lenC_eq : ∀ cs : List (List Nat), lenC cs = cs.length
  | [] => rfl
  | _ :: cs => by
    change Nat.succ (lenC cs) = _
    rw [lenC_eq cs]
    rfl

theorem nxs_eq (l : List Nat) :
    (if isConsL l = true then [headL l] else []) = l.head?.toList := by
  cases l <;> rfl

theorem le_of_head {L : List Nat} {m : Nat} (hp : L.Pairwise (· < ·))
    (hh : ∀ z ∈ L.head?, m ≤ z) : ∀ y ∈ L, m ≤ y := by
  cases L with
  | nil => simp
  | cons z zs =>
    intro y hy
    have hz : m ≤ z := hh z (by simp)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hz
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt hz (List.rel_of_pairwise_cons hp hy))

theorem chunkGo_sound {t : KT} {hasNx : Bool} {nx e : Nat} : ∀ (l : List Nat) (pos lo : Nat),
    chunkGo t hasNx nx e l pos lo = true →
    (∀ j (h : j < l.length), t.find l[j] = pos + j + 1) ∧ pos + l.length = e ∧
    (l ++ (if hasNx = true then [nx] else [])).Pairwise (· < ·) ∧
    ∀ y ∈ (l ++ (if hasNx = true then [nx] else [])).head?, lo ≤ y
  | [], pos, lo, h => by
    change bAnd(Nat.beq pos e, bIf(hasNx, Nat.ble lo nx, true)) = true at h
    have h' := band_true h
    refine ⟨fun j h => absurd h (Nat.not_lt_zero _), by simpa using Nat.eq_of_beq_eq_true h'.1,
      ?_, ?_⟩
    · cases hasNx <;> simp
    · cases hasNx
      · simp
      · have hl : lo ≤ nx := Nat.le_of_ble_eq_true h'.2
        simpa using hl
  | k :: l, pos, lo, h => by
    change bAnd(Nat.ble lo k, bAnd(Nat.beq (KT.find k t) (Nat.succ pos),
      strictKB (Nat.succ pos) (fun p => chunkGo t hasNx nx e l p (Nat.succ k)))) = true at h
    have h1 := band_true h
    have h2 := band_true h1.2
    have hlo : lo ≤ k := Nat.le_of_ble_eq_true h1.1
    have hf : t.find k = pos + 1 := Nat.eq_of_beq_eq_true h2.1
    have hr : chunkGo t hasNx nx e l (pos + 1) (k + 1) = true := h2.2
    obtain ⟨ih1, ih2, ih3, ih4⟩ := chunkGo_sound l (pos + 1) (k + 1) hr
    refine ⟨?_, by simp only [List.length_cons]; omega, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero => simpa using hf
      | succ j =>
        have := ih1 j (by simpa using hj)
        simp only [List.getElem_cons_succ]
        rw [this]
        omega
    · rw [List.cons_append, List.pairwise_cons]
      exact ⟨fun y hy => le_of_head ih3 ih4 y hy, ih3⟩
    · intro y hy
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      exact hy ▸ hlo

theorem chunkOK_sound {t : KT} {sz N : Nat} {cs : List (List Nat)} {c : Nat} (hc : c < cs.length)
    (h : t.chunkOK sz N cs c = true) :
    (∀ j (h : j < cs[c].length), t.find cs[c][j] = sz * c + j + 1) ∧
    sz * c + cs[c].length = (if c + 1 < cs.length then sz * (c + 1) else N) ∧
    (cs[c] ++ (cs.getD (c + 1) []).head?.toList).Pairwise (· < ·) := by
  unfold KT.chunkOK at h
  rw [nthC_eq, nthC_eq, lenC_eq] at h
  obtain ⟨h1, h2, h3, -⟩ := chunkGo_sound _ _ _ h
  rw [getD_eq hc, nxs_eq] at h3
  rw [getD_eq hc] at h1 h2
  simp only [Nat.mul_eq] at h1 h2
  refine ⟨fun j hj => h1 j hj, ?_, h3⟩
  rw [h2]
  cases hb : Nat.blt (Nat.succ c) cs.length
  · have : ¬ c + 1 < cs.length := fun h' => by
      have h'' : Nat.blt (c + 1) cs.length = true := by simpa using h'
      rw [hb] at h''
      exact Bool.false_ne_true h''
    rw [if_neg this]
  · have : c + 1 < cs.length := by simpa using hb
    rw [if_pos this]

theorem flatten_facts {t : KT} {sz N : Nat} : ∀ (cs : List (List Nat)) (base : Nat), cs ≠ [] →
    (∀ c (hc : c < cs.length),
      (∀ j (h : j < cs[c].length), t.find cs[c][j] = base + sz * c + j + 1) ∧
      base + sz * c + cs[c].length = (if c + 1 < cs.length then base + sz * (c + 1) else N)) →
    (∀ i (h : i < cs.flatten.length), t.find cs.flatten[i] = base + i + 1) ∧
    base + cs.flatten.length = N
  | [], _, hne, _ => absurd rfl hne
  | [ch], base, _, h => by
    obtain ⟨h1, h2⟩ := h 0 (by simp)
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    refine ⟨fun i hi => by simpa using h1 i hi, by simpa using h2⟩
  | ch :: ch' :: rest, base, _, h => by
    obtain ⟨h1, h2⟩ := h 0 (by simp)
    have hlen : ch.length = sz := by simpa using h2
    obtain ⟨ih1, ih2⟩ := flatten_facts (t := t) (sz := sz) (N := N) (ch' :: rest) (base + sz)
      (by simp) (fun c hc => by
      obtain ⟨g1, g2⟩ := h (c + 1) (by simp at hc ⊢; omega)
      have e1 : sz * (c + 1) = sz * c + sz := Nat.mul_succ sz c
      have e2 : sz * (c + 1 + 1) = sz * c + sz + sz := by rw [Nat.mul_succ, e1]
      refine ⟨fun j hj => ?_, ?_⟩
      · have := g1 j hj
        simp only [List.getElem_cons_succ] at this
        rw [this]
        omega
      · simp only [List.getElem_cons_succ, List.length_cons] at g2 ⊢
        have hcond : c + 1 + 1 < rest.length + 1 + 1 ↔ c + 1 < rest.length + 1 := by omega
        by_cases hq : c + 1 < rest.length + 1
        · rw [if_pos hq]
          rw [if_pos (hcond.2 hq)] at g2
          omega
        · rw [if_neg hq]
          rw [if_neg (fun h' => hq (hcond.1 h'))] at g2
          omega)
    rw [List.flatten_cons]
    refine ⟨fun i hi => ?_, by rw [List.length_append]; omega⟩
    by_cases hi' : i < ch.length
    · rw [List.getElem_append_left hi']
      simpa using h1 i hi'
    · rw [List.getElem_append_right (by omega)]
      rw [ih1 _ (by rw [List.length_append] at hi; omega)]
      omega

theorem flatten_pairwise : ∀ (cs : List (List Nat)),
    (∀ c (hc : c < cs.length), (c + 1 < cs.length → cs[c] ≠ []) ∧
      (cs[c] ++ (cs.getD (c + 1) []).head?.toList).Pairwise (· < ·)) →
    cs.flatten.Pairwise (· < ·)
  | [], _ => by simp
  | ch :: rest, h => by
    have h0 := (h 0 (by simp)).2
    have ih := flatten_pairwise rest (fun c hc => by
      obtain ⟨g1, g2⟩ := h (c + 1) (by simp; omega)
      exact ⟨fun hc' => g1 (by simp; omega), by simpa using g2⟩)
    rw [List.flatten_cons, List.pairwise_append]
    refine ⟨(List.pairwise_append.mp h0).1, ih, fun a ha b hb => ?_⟩
    cases rest with
    | nil => simp at hb
    | cons ch1 rest' =>
      cases ch1 with
      | nil =>
        cases rest' with
        | nil => simp at hb
        | cons _ _ => exact absurd rfl ((h 1 (by simp)).1 (by simp))
      | cons y ys =>
        have hay : a < y := by
          have := (List.pairwise_append.mp h0).2.2 a ha y
          simpa using this
        rw [List.flatten_cons, List.cons_append] at hb ih
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hay
        · exact Nat.lt_trans hay (List.rel_of_pairwise_cons ih hb)

theorem KT.chunks_sound {t : KT} {sz N : Nat} {cs : List (List Nat)} (hne : cs ≠ [])
    (hsz : 0 < sz) (h : ∀ c < cs.length, t.chunkOK sz N cs c = true) (hs : t.size = N) :
    cs.flatten.Pairwise (· < ·) ∧ cs.flatten.length = N ∧
    (∀ i (hi : i < cs.flatten.length), t.find cs.flatten[i] = i + 1) ∧
    ∀ x v, t.find x = v + 1 → ∃ hv : v < cs.flatten.length, cs.flatten[v] = x := by
  have hc := fun c hc => chunkOK_sound hc (h c hc)
  obtain ⟨f1, f2⟩ := flatten_facts (t := t) (sz := sz) (N := N) cs 0 hne (fun c hc' => by
    obtain ⟨g1, g2, -⟩ := hc c hc'
    exact ⟨fun j hj => by simpa using g1 j hj, by simpa using g2⟩)
  have hp : cs.flatten.Pairwise (· < ·) := flatten_pairwise cs (fun c hc' => by
    obtain ⟨-, g2, g3⟩ := hc c hc'
    refine ⟨fun hlt hnil => ?_, g3⟩
    rw [if_pos hlt, hnil] at g2
    simp [Nat.mul_succ] at g2
    omega)
  simp only [Nat.zero_add] at f1 f2
  refine ⟨hp, f2, f1, fun x v hv => ?_⟩
  set K := cs.flatten
  let L := (List.range K.length).map fun i => (K.getD i 0, i)
  have hnd : L.Nodup :=
    List.Nodup.map (fun i j hij => congrArg Prod.snd hij) List.nodup_range
  have hsub : L ⊆ t.ents := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
    have hi' := List.mem_range.mp hi
    apply KT.find_ents
    rw [getD_eq hi']
    exact f1 i hi'
  have hfs : L.toFinset = t.ents.toFinset :=
    Finset.eq_of_subset_of_card_le (fun z hz => List.mem_toFinset.2 (hsub (List.mem_toFinset.1 hz)))
      (by
        rw [List.toFinset_card_of_nodup hnd, List.length_map, List.length_range, f2, ← hs,
          KT.size_eq]
        exact List.toFinset_card_le _)
  have hmem : (x, v) ∈ L := by
    rw [← List.mem_toFinset, hfs, List.mem_toFinset]
    exact KT.find_ents t hv
  obtain ⟨i, hi, hiz⟩ := List.mem_map.mp hmem
  have hi' := List.mem_range.mp hi
  obtain ⟨h1, rfl⟩ := Prod.mk.inj hiz
  exact ⟨hi', by rw [← h1, getD_eq hi']⟩

theorem KT.idx_eq {t : KT} {N : Nat} {K : List Nat}
    (hf : ∀ i (hi : i < K.length), t.find K[i] = i + 1)
    (hs : ∀ x v, t.find x = v + 1 → ∃ hv : v < K.length, K[v] = x) (x : Nat) :
    (∀ i (hi : i < K.length), K[i] = x → KT.idx N x t = i) ∧
    ((∀ i (hi : i < K.length), K[i] ≠ x) → KT.idx N x t = N) := by
  have e : KT.idx N x t = nIf(Nat.beq (KT.find x t) 0, N, Nat.pred (KT.find x t)) := rfl
  refine ⟨fun i hi hx => ?_, fun hn => ?_⟩
  · rw [e, ← hx, hf i hi]
    rfl
  · rw [e]
    cases hx : KT.find x t with
    | zero => rfl
    | succ v =>
      obtain ⟨hv, hk⟩ := hs x v hx
      exact absurd hk (hn v hv)

end CFSG.KC.KeyTree

end
