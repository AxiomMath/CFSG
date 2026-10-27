module

public import CFSG.Certificates.Kernel.LocalQTM24Snd.Sort

public section

namespace CFSG.KC.LQT.M24Snd

open CFSG.KC.LQT.M24

private theorem aux_isetl_nilK_iff (l : List ℕ) : nilK l = true ↔ l = [] := by
  cases l <;> simp [nilK]

theorem inclK_spec (xs ys : List ℕ) (h : inclK xs ys = true) : ∀ x ∈ xs, x ∈ ys := by
  intro x hx
  rcases diffS_cover xs ys x hx with hy | hd
  · exact hy
  · unfold inclK at h
    have hn := (aux_isetl_nilK_iff _).mp h
    rw [hn] at hd
    simp at hd

theorem allZ_zip {α β : Type} {l : List α} {m : List β} {f : α → β → Bool}
    (h : allZ l m f = true) : l.length = m.length ∧ ∀ p ∈ l.zip m, f p.1 p.2 = true := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => exact ⟨rfl, by simp⟩
    | cons y m' => simp [allZ] at h
  | cons x l ih =>
    cases m with
    | nil => simp [allZ] at h
    | cons y m' =>
      have h' : CFSG.KC.Ord.andB (f x y) (allZ l m' f) = true := h
      obtain ⟨h1, h2⟩ := CFSG.KC.LQT.P.andB_iff.mp h'
      obtain ⟨hl, hr⟩ := ih h2
      refine ⟨by simp [hl], ?_⟩
      intro p hp
      rw [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact h1
      · exact hr p hp

theorem isetIn_spec (S IL : List ℕ) (h : isetIn S IL = true) :
    ∀ s ∈ S, Nat.shiftLeft s 5 ∈ IL := by
  intro s hs
  unfold isetIn at h
  have h2 : inclK (List.map (fun s => Nat.shiftLeft s 5) S) IL = true :=
    (CFSG.KC.LQT.P.andB_iff.mp h).2
  have hm : Nat.shiftLeft s 5 ∈ List.map (fun s => Nat.shiftLeft s 5) S :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  exact inclK_spec _ _ h2 _ hm

theorem isetClo_spec (n g0 g1 g2 g3 : ℕ) (IL ch : List ℕ)
    (h : isetClo n g0 g1 g2 g3 IL ch = true) :
    ∀ e ∈ ch, ∀ y ∈ cimgK n g0 g1 g2 g3 (codeE e), y ∈ IL.map codeE := by
  intro e he y hy
  unfold isetClo at h
  rw [forceN_eq] at h
  apply inclK_spec _ _ h
  apply (CFSG.KC.LQT.Pairs.mem_dedupS _ _).mpr
  apply (CFSG.KC.LQT.Pairs.sortN_perm _).mem_iff.mpr
  apply List.mem_flatten.mpr
  exact ⟨cimgK n g0 g1 g2 g3 (codeE e), List.mem_map.mpr ⟨e, he, rfl⟩, hy⟩

theorem isetReach_spec (n g0 g1 g2 g3 : ℕ) (S : List ℕ) (r : ℕ) (IL ch hs : List ℕ)
    (h : isetReach n g0 g1 g2 g3 S r IL ch hs = true) :
    ∀ e ∈ ch, ∃ hh : ℕ,
      (Nat.land e 31 = 0 ∧ codeE e ∈ S) ∨
      (Nat.land e 31 ≠ 0 ∧ Nat.land e 31 ≤ r ∧
        cimgAt n g0 g1 g2 g3 (Nat.land hh 3) (Nat.shiftRight hh 2) = codeE e ∧
        Nat.add (Nat.shiftLeft (Nat.shiftRight hh 2) 5) (Nat.sub (Nat.land e 31) 1) ∈ IL) := by
  intro e he
  unfold isetReach at h
  obtain ⟨hz, hi⟩ := CFSG.KC.LQT.P.andB_iff.mp h
  obtain ⟨hlen, hf⟩ := allZ_zip hz
  obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp he
  have hiH : i < hs.length := by omega
  have hpair : (ch[i], hs[i]) ∈ ch.zip hs := by
    have hz' : i < (ch.zip hs).length := by rw [List.length_zip]; omega
    have hm := List.getElem_mem hz'
    rwa [List.getElem_zip] at hm
  have hf' := hf _ hpair
  cases hb : Nat.beq (Nat.land ch[i] 31) 0 with
  | true =>
    simp only [hb] at hf'
    exact ⟨hs[i], Or.inl ⟨Nat.eq_of_beq_eq_true hb, (CFSG.KC.LQT.S.memL_iff _ _).mp hf'⟩⟩
  | false =>
    simp only [hb] at hf'
    obtain ⟨hble, hbeq⟩ := CFSG.KC.LQT.P.andB_iff.mp hf'
    have hp : parK ch[i] hs[i] =
        [Nat.add (Nat.shiftLeft (Nat.shiftRight hs[i] 2) 5) (Nat.sub (Nat.land ch[i] 31) 1)] := by
      simp only [parK, hb]
    have hmemP : parK ch[i] hs[i] ∈ List.zipWith parK ch hs := by
      have hz2 : i < (List.zipWith parK ch hs).length := by rw [List.length_zipWith]; omega
      have hm := List.getElem_mem hz2
      rwa [List.getElem_zipWith] at hm
    have hx : Nat.add (Nat.shiftLeft (Nat.shiftRight hs[i] 2) 5) (Nat.sub (Nat.land ch[i] 31) 1) ∈
        CFSG.KC.LQT.Syl.sortN (List.flatten (List.zipWith parK ch hs)) := by
      apply (CFSG.KC.LQT.Pairs.sortN_perm _).mem_iff.mpr
      apply List.mem_flatten.mpr
      exact ⟨parK ch[i] hs[i], hmemP, by rw [hp]; exact List.mem_singleton_self _⟩
    exact ⟨hs[i], Or.inr ⟨Nat.ne_of_beq_eq_false hb, Nat.le_of_ble_eq_true hble,
      Nat.eq_of_beq_eq_true hbeq, inclK_spec _ _ hi _ hx⟩⟩

theorem isetY_spec (n X : ℕ) (Els : List (List ℕ)) (ch : List ℕ) (h : isetY n X Els ch = true) :
    ∀ e ∈ ch, ycK n (List.map (CFSG.KC.LQT.P.pow n X) [0, 1, 2, 3, 4, 5]) Els (codeE e) = true := by
  unfold isetY at h
  rw [forceN_eq] at h
  exact (CFSG.KC.LQT.P.allL_iff _ _).mp h

theorem mem_flatten_getD {chs : List (List ℕ)} {e : ℕ} (h : e ∈ chs.flatten) :
    ∃ j < chs.length, e ∈ chs.getD j [] := by
  obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hl
  refine ⟨j, hj, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact hel

theorem iset_entries (n g0 g1 g2 g3 : ℕ) (S : List ℕ) (r X : ℕ) (Els : List (List ℕ))
    (chs hss : List (List ℕ)) (hin : isetIn S chs.flatten = true)
    (hlen : chs.length = hss.length)
    (hch : ∀ j < chs.length, isetChunk n g0 g1 g2 g3 S r X Els chs.flatten (chs.getD j [])
      (hss.getD j []) = true) :
    (∀ s ∈ S, Nat.shiftLeft s 5 ∈ chs.flatten) ∧
    (∀ e ∈ chs.flatten, ∀ y ∈ cimgK n g0 g1 g2 g3 (codeE e), y ∈ chs.flatten.map codeE) ∧
    (∀ e ∈ chs.flatten, ∃ hh : ℕ,
      (Nat.land e 31 = 0 ∧ codeE e ∈ S) ∨
      (Nat.land e 31 ≠ 0 ∧ Nat.land e 31 ≤ r ∧
        cimgAt n g0 g1 g2 g3 (Nat.land hh 3) (Nat.shiftRight hh 2) = codeE e ∧
        Nat.add (Nat.shiftLeft (Nat.shiftRight hh 2) 5) (Nat.sub (Nat.land e 31) 1) ∈
          chs.flatten)) ∧
    (∀ e ∈ chs.flatten,
      ycK n (List.map (CFSG.KC.LQT.P.pow n X) [0, 1, 2, 3, 4, 5]) Els (codeE e) = true) := by
  have hdec : ∀ j < chs.length, isetClo n g0 g1 g2 g3 chs.flatten (chs.getD j []) = true ∧
      isetReach n g0 g1 g2 g3 S r chs.flatten (chs.getD j []) (hss.getD j []) = true ∧
      isetY n X Els (chs.getD j []) = true := by
    intro j hj
    have hc := hch j hj
    unfold isetChunk at hc
    obtain ⟨h1, h2⟩ := CFSG.KC.LQT.P.andB_iff.mp hc
    obtain ⟨h2a, h2b⟩ := CFSG.KC.LQT.P.andB_iff.mp h2
    exact ⟨h1, h2a, h2b⟩
  refine ⟨isetIn_spec S chs.flatten hin, ?_, ?_, ?_⟩
  · intro e he y hy
    obtain ⟨j, hj, hej⟩ := mem_flatten_getD he
    exact isetClo_spec n g0 g1 g2 g3 chs.flatten (chs.getD j []) (hdec j hj).1 e hej y hy
  · intro e he
    obtain ⟨j, hj, hej⟩ := mem_flatten_getD he
    exact isetReach_spec n g0 g1 g2 g3 S r chs.flatten (chs.getD j []) (hss.getD j [])
      (hdec j hj).2.1 e hej
  · intro e he
    obtain ⟨j, hj, hej⟩ := mem_flatten_getD he
    exact isetY_spec n X Els (chs.getD j []) (hdec j hj).2.2 e hej

end CFSG.KC.LQT.M24Snd

end
