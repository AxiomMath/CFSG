module

public import CFSG.Certificates.Kernel.BSeed.Sound

namespace CFSG.KC.BSeed

open CFSG.Blueprint.NativeSporadic

def seedBit (r j : Nat) : Nat := if r.testBit j then 1 else 0

theorem dropWhile_hdr (H T : List Char) (hH : ∀ c ∈ H, c ≠ '\n') :
    (H ++ '\n' :: T).dropWhile (· != '\n') = '\n' :: T := by
  induction H with
  | nil => simp
  | cons c H ih =>
    have hc : (c != '\n') = true := bne_iff_ne.2 (hH c List.mem_cons_self)
    rw [List.cons_append, List.dropWhile_cons]
    simp only [hc, ↓reduceIte]
    exact ih fun c' h => hH c' (List.mem_cons_of_mem _ h)

theorem hdr_ne (d : Nat) :
    ∀ c ∈ (" 1     2  " ++ toString d ++ "  " ++ toString d).toList, c ≠ '\n' := by
  have hd : ∀ c ∈ (toString d).toList, c ≠ '\n' := by
    intro c hc h
    rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
    have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    subst h
    exact absurd this (by decide)
  intro c hc
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with ((h | h) | h) | h
  · rintro rfl
    exact absurd h (by decide +kernel)
  · exact hd c h
  · rintro rfl
    exact absurd h (by decide +kernel)
  · exact hd c h

theorem row_entries (d r : Nat) :
    (((List.range d).flatMap (fun j => (if j ≠ 0 ∧ j % 80 = 0 then ['\n'] else []) ++
        [if r.testBit j then '1' else '0']) ++ ['\n']).filter fun c => !asciiWhitespace c).map
      (fun c => if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0) =
      (List.range d).map (seedBit r) := by
  rw [List.filter_append, List.filter_flatMap, List.map_append, List.map_flatMap]
  have e : (['\n'].filter fun c => !asciiWhitespace c) = [] := by decide
  rw [e, List.map_nil, List.append_nil, ← List.flatMap_singleton' (List.map _ _),
    List.flatMap_map]
  congr 1
  funext j
  rw [List.filter_append]
  have e1 : ((if j ≠ 0 ∧ j % 80 = 0 then ['\n'] else []).filter fun c => !asciiWhitespace c) = [] := by
    split <;> decide
  rw [e1, List.nil_append, seedBit]
  cases r.testBit j <;> decide

theorem flat_getElem? (d : Nat) (f : Nat → Nat → Nat) : ∀ (rows : List Nat) (i j : Nat),
    i < rows.length → j < d →
      (rows.flatMap fun r => (List.range d).map (f r))[i * d + j]? = some (f (rows.getD i 0) j)
  | [], i, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | r :: rows, 0, j, _, hj => by
    rw [List.flatMap_cons, Nat.zero_mul, Nat.zero_add,
      List.getElem?_append_left (by simpa using hj)]
    simp [hj]
  | r :: rows, i + 1, j, hi, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by simp; nlinarith)]
    have : i * d + j = (i + 1) * d + j - ((List.range d).map (f r)).length := by
      simp only [List.length_map, List.length_range]
      rw [Nat.add_mul]
      omega
    rw [← this, flat_getElem? d f rows i j (by simpa using hi) hj]
    simp

public section

theorem decode_render (d : Nat) (rows : List Nat) (hl : rows.length = d) :
    decode 2 d 1 (render d rows) = rowsMat d fun i => rows.getD i 0 := by
  have e : (render d rows).toList = (" 1     2  " ++ toString d ++ "  " ++ toString d).toList ++
      '\n' :: rows.flatMap fun r => (List.range d).flatMap (fun j =>
        (if j ≠ 0 ∧ j % 80 = 0 then ['\n'] else []) ++ [if r.testBit j then '1' else '0']) ++ ['\n'] := by
    rw [render, String.toList_append, String.toList_append, String.toList_ofList, List.append_assoc,
      String.toList_ofList, List.singleton_append]
  funext i j
  unfold decode
  simp only [↓reduceIte]
  rw [e, dropWhile_hdr _ _ (hdr_ne d), List.drop_one, List.tail_cons, List.filter_flatMap,
    List.map_flatMap]
  simp only [row_entries]
  rw [flat_getElem? d seedBit rows i.val j.val (hl ▸ i.isLt) j.isLt, Option.getD_some, rowsMat, seedBit]
  split <;> simp

@[expose] def rowsListOK (R : Nat → Nat) : List Nat → Nat → Nat → Bool
  | [], i, n => Nat.beq i n
  | r :: l, i, n => Nat.beq r (R i) && rowsListOK R l (i + 1) n

theorem rowsListOK_spec {R : Nat → Nat} : ∀ {l : List Nat} {i n : Nat}, rowsListOK R l i n = true →
    l.length + i = n ∧ ∀ k < l.length, l.getD k 0 = R (i + k)
  | [], i, n, h => ⟨by simpa [rowsListOK] using Nat.eq_of_beq_eq_true h, fun _ hk => absurd hk (by simp)⟩
  | r :: l, i, n, h => by
    rw [rowsListOK, Bool.and_eq_true] at h
    obtain ⟨hl, hk⟩ := rowsListOK_spec h.2
    refine ⟨by simp only [List.length_cons]; omega, fun k hk' => ?_⟩
    rcases k with _ | k
    · simpa using Nat.eq_of_beq_eq_true h.1
    · rw [List.getD_cons_succ, hk k (by simpa using hk')]
      congr 1
      omega

end

end CFSG.KC.BSeed
