module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Invo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cert

public section

namespace CFSG.KC.LQT.M24Snd

open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.A5.Kc3Cert

variable {n : ℕ}

@[expose] def conjF (g0 g1 g2 g3 : RN n) (x : RN n) : List (RN n) :=
  [g0 * x * g2, g1 * x * g3, g2 * x * g0, g3 * x * g1]

private theorem aux_hashc_mem_ofList (seeds : List (RN n)) (x : RN n) :
    x ∈ Std.HashSet.ofList seeds ↔ x ∈ seeds :=
  Std.HashSet.mem_ofList.trans List.contains_iff

private theorem aux_hashc_inner (l : List (RN n)) (acc : Std.HashSet (RN n) × List (RN n)) :
    (∀ z, z ∈ (l.foldl (fun acc y => if acc.1.contains y then acc else
        (acc.1.insert y, y :: acc.2)) acc).1 ↔ z ∈ acc.1 ∨ z ∈ l) ∧
    (∀ z, z ∈ (l.foldl (fun acc y => if acc.1.contains y then acc else
        (acc.1.insert y, y :: acc.2)) acc).2 ↔ z ∈ acc.2 ∨ (z ∉ acc.1 ∧ z ∈ l)) := by
  induction l generalizing acc with
  | nil => exact ⟨fun z => by simp, fun z => by simp⟩
  | cons y l ih =>
    simp only [List.foldl_cons]
    by_cases hc : acc.1.contains y = true
    · rw [if_pos hc]
      have hy : y ∈ acc.1 := Std.HashSet.contains_iff_mem.mp hc
      obtain ⟨h1, h2⟩ := ih acc
      refine ⟨fun z => (h1 z).trans ?_, fun z => (h2 z).trans ?_⟩
      · constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem y h)
        · rintro (h | h)
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inl hy
            · exact Or.inr h
      · constructor
        · rintro (h | ⟨hn, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨hn, List.mem_cons_of_mem y h⟩
        · rintro (h | ⟨hn, h⟩)
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h
            · exact absurd hy hn
            · exact Or.inr ⟨hn, h⟩
    · rw [if_neg hc]
      have hA : y ∉ acc.1 := fun h => hc (Std.HashSet.contains_iff_mem.mpr h)
      obtain ⟨h1, h2⟩ := ih (acc.1.insert y, y :: acc.2)
      dsimp only at h1 h2
      refine ⟨fun z => (h1 z).trans ?_, fun z => (h2 z).trans ?_⟩
      · rw [Std.HashSet.mem_insert, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl (beq_iff_eq.mp h).symm)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl (beq_iff_eq.mpr h.symm))
          · exact Or.inr h
      · constructor
        · rintro (h | ⟨hn, h⟩)
          · rcases List.mem_cons.mp h with hzy | hz2
            · exact Or.inr ⟨by rw [hzy]; exact hA, by rw [hzy]; exact List.mem_cons_self⟩
            · exact Or.inl hz2
          · exact Or.inr ⟨fun hz => hn (Std.HashSet.mem_insert.mpr (Or.inr hz)),
              List.mem_cons_of_mem y h⟩
        · rintro (h | ⟨hn, h⟩)
          · exact Or.inl (List.mem_cons_of_mem y h)
          · by_cases hzy : z = y
            · exact Or.inl (by rw [hzy]; exact List.mem_cons_self)
            · refine Or.inr ⟨fun hz => ?_, (List.mem_cons.mp h).resolve_left hzy⟩
              rcases Std.HashSet.mem_insert.mp hz with hb | hz'
              · exact hzy (beq_iff_eq.mp hb).symm
              · exact hn hz'

private theorem aux_hashc_exists_cons (P : RN n → Prop) (x : RN n) (l : List (RN n)) :
    (∃ x' ∈ x :: l, P x') ↔ P x ∨ ∃ x' ∈ l, P x' := by
  constructor
  · rintro ⟨x', hx', hp⟩
    rcases List.mem_cons.mp hx' with rfl | hl
    · exact Or.inl hp
    · exact Or.inr ⟨x', hl, hp⟩
  · rintro (hp | ⟨x', hl, hp⟩)
    · exact ⟨x, List.mem_cons_self, hp⟩
    · exact ⟨x', List.mem_cons_of_mem x hl, hp⟩

private theorem aux_hashc_outer (g0 g1 g2 g3 : RN n) (l : List (RN n))
    (acc : Std.HashSet (RN n) × List (RN n)) :
    (∀ z, z ∈ (l.foldl (fun acc x => (conjF g0 g1 g2 g3 x).foldl (fun acc y =>
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) acc).1 ↔
      z ∈ acc.1 ∨ ∃ x ∈ l, z ∈ conjF g0 g1 g2 g3 x) ∧
    (∀ z, z ∈ (l.foldl (fun acc x => (conjF g0 g1 g2 g3 x).foldl (fun acc y =>
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) acc).2 ↔
      z ∈ acc.2 ∨ (z ∉ acc.1 ∧ ∃ x ∈ l, z ∈ conjF g0 g1 g2 g3 x)) := by
  induction l generalizing acc with
  | nil => exact ⟨fun z => by simp, fun z => by simp⟩
  | cons x rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := aux_hashc_inner (conjF g0 g1 g2 g3 x) acc
    obtain ⟨h3, h4⟩ := ih ((conjF g0 g1 g2 g3 x).foldl (fun acc y =>
        if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc)
    refine ⟨fun z => (h3 z).trans ?_, fun z => (h4 z).trans ?_⟩
    · rw [h1 z, aux_hashc_exists_cons]
      tauto
    · rw [h2 z, h1 z, aux_hashc_exists_cons]
      tauto

theorem conjStep_spec (g0 g1 g2 g3 : RN n) (st : Std.HashSet (RN n) × List (RN n)) :
    (∀ y, y ∈ (conjStep g0 g1 g2 g3 st).1 ↔ y ∈ st.1 ∨ ∃ x ∈ st.2, y ∈ conjF g0 g1 g2 g3 x) ∧
      ∀ y, y ∈ (conjStep g0 g1 g2 g3 st).2 ↔
        y ∉ st.1 ∧ ∃ x ∈ st.2, y ∈ conjF g0 g1 g2 g3 x := by
  obtain ⟨h1, h2⟩ := aux_hashc_outer g0 g1 g2 g3 st.2 (st.1, [])
  refine ⟨fun y => h1 y, fun y => (h2 y).trans ?_⟩
  simp

theorem conjStep_iter_inv (g0 g1 g2 g3 : RN n) (seeds : Set (RN n)) (k : ℕ)
    (st : Std.HashSet (RN n) × List (RN n))
    (h : BfsInv (conjF g0 g1 g2 g3) seeds k {x | x ∈ st.1} {x | x ∈ st.2}) (r : ℕ) :
    BfsInv (conjF g0 g1 g2 g3) seeds (k + r) {x | x ∈ (Nat.iterate (conjStep g0 g1 g2 g3) r st).1}
      {x | x ∈ (Nat.iterate (conjStep g0 g1 g2 g3) r st).2} := by
  induction r generalizing k st with
  | zero => exact h
  | succ r ih =>
    have hs := conjStep_spec g0 g1 g2 g3 st
    have h' : BfsInv (conjF g0 g1 g2 g3) seeds (k + 1) {x | x ∈ (conjStep g0 g1 g2 g3 st).1}
        {x | x ∈ (conjStep g0 g1 g2 g3 st).2} :=
      BfsInv.step h (fun y => hs.1 y) (fun y hy hS => (hs.2 y).2 ⟨hS, hy⟩)
        (fun y hy => ((hs.2 y).1 hy).2)
    have key := ih (k + 1) (conjStep g0 g1 g2 g3 st) h'
    rw [show k + 1 + r = k + (r + 1) by omega] at key
    exact key

theorem mem_conjBfs_iff (g0 g1 g2 g3 : RN n) (seeds : List (RN n)) (r : ℕ) (x : RN n) :
    x ∈ conjBfs g0 g1 g2 g3 seeds r ↔ x ∈ ball (conjF g0 g1 g2 g3) {y | y ∈ seeds} r := by
  have hball : ∀ z, z ∈ ball (conjF g0 g1 g2 g3) {y | y ∈ seeds} 0 ↔ z ∈ seeds := by
    intro z
    have hi : BfsInv (conjF g0 g1 g2 g3) {y | y ∈ seeds} 0 {y | y ∈ seeds} {y | y ∈ seeds} :=
      BfsInv.init
    exact ⟨fun hz => hi.sup z hz, fun hz => hi.sub z hz⟩
  have h0 : BfsInv (conjF g0 g1 g2 g3) {y | y ∈ seeds} 0
      {z | z ∈ (Std.HashSet.ofList seeds, seeds).1} {z | z ∈ (Std.HashSet.ofList seeds, seeds).2} :=
    ⟨fun z hz => (hball z).mpr ((aux_hashc_mem_ofList seeds z).mp hz),
      fun z hz => (aux_hashc_mem_ofList seeds z).mpr ((hball z).mp hz),
      fun z hz _ => (hball z).mp hz,
      fun z hz => (aux_hashc_mem_ofList seeds z).mpr hz⟩
  have hI := conjStep_iter_inv g0 g1 g2 g3 {y | y ∈ seeds} 0 (Std.HashSet.ofList seeds, seeds) h0 r
  rw [Nat.zero_add] at hI
  unfold conjBfs
  exact ⟨fun hx => hI.sub x hx, fun hx => hI.sup x hx⟩

end CFSG.KC.LQT.M24Snd

end
