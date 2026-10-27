module

public import Certificates.Data.Kernel.RouteP.TextSplit
public import Batteries.Data.String.Lemmas
import all Init.Data.String.Legacy

public section

namespace CFSG.KS.RouteP

open String CFSG.KC.RouteP

theorem utf8Size_ascii {c : Char} (h : c.toNat < 128) : c.utf8Size = 1 :=
  Char.utf8Size_eq_one_iff.2 (by
    rw [UInt32.le_iff_toNat_le]
    change c.toNat ≤ 127
    omega)

theorem utf8Len_ascii : ∀ {l : List Char}, (∀ c ∈ l, c.toNat < 128) → utf8Len l = l.length
  | [], _ => rfl
  | c :: l, h => by
    rw [utf8Len_cons, utf8Len_ascii (fun d hd => h d (List.mem_cons_of_mem c hd)),
      utf8Size_ascii (h c List.mem_cons_self), List.length_cons]

section

variable {cs : List Char} (hc : ∀ c ∈ cs, c.toNat < 128)
include hc

theorem len_take (k : Nat) : utf8Len (cs.take k) = min k cs.length := by
  rw [utf8Len_ascii (fun c h => hc c (List.mem_of_mem_take h)), List.length_take]

theorem get_asc {k : Nat} (hk : k ≤ cs.length) :
    Pos.Raw.get (ofList cs) ⟨k⟩ = (cs.drop k).headD default := by
  have e := get_of_valid (cs.take k) (cs.drop k)
  rw [List.take_append_drop, len_take hc, Nat.min_eq_left hk] at e
  exact e

theorem next_asc {k : Nat} (hk : k < cs.length) : Pos.Raw.next (ofList cs) ⟨k⟩ = ⟨k + 1⟩ := by
  obtain ⟨c, rest, hd⟩ : ∃ c rest, cs.drop k = c :: rest := by
    cases h : cs.drop k with
    | nil => simp at h; omega
    | cons c rest => exact ⟨c, rest, rfl⟩
  have e := next_of_valid (cs.take k) c rest
  rw [← hd, List.take_append_drop, len_take hc, Nat.min_eq_left (by omega)] at e
  rw [e, utf8Size_ascii (hc c (by
    have : c ∈ cs.drop k := by rw [hd]; exact List.mem_cons_self
    exact List.mem_of_mem_drop this))]

theorem atEnd_asc (k : Nat) : Pos.Raw.atEnd (ofList cs) ⟨k⟩ = decide (cs.length ≤ k) := by
  apply Bool.eq_iff_iff.mpr
  rw [atEnd_iff, rawEndPos_ofList, utf8Len_ascii hc, decide_eq_true_iff]
  exact Pos.Raw.mk_le_mk

theorem extract_asc {b e : Nat} (hb : b ≤ e) (he : e ≤ cs.length) :
    Pos.Raw.extract (ofList cs) ⟨b⟩ ⟨e⟩ = ofList ((cs.drop b).take (e - b)) := by
  have x := extract_of_valid (cs.take b) ((cs.drop b).take (e - b)) ((cs.drop b).drop (e - b))
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop, len_take hc,
    Nat.min_eq_left (by omega)] at x
  have hm : utf8Len ((cs.drop b).take (e - b)) = e - b := by
    rw [utf8Len_ascii (fun c h => hc c (List.mem_of_mem_drop (List.mem_of_mem_take h))),
      List.length_take, List.length_drop]
    omega
  rw [hm, Nat.add_sub_cancel' hb] at x
  exact x

end

theorem headD_drop : ∀ {l : List Char} {k : Nat}, k < l.length →
    (l.drop k).headD default = l.getD k 'a'
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | c :: l, 0, _ => rfl
  | c :: l, k + 1, hk => by
    rw [List.drop_succ_cons, List.getD_cons_succ]
    exact headD_drop (by simp at hk; omega)

theorem mu_lt {A B m : Nat} (h : B + 1 ≤ A) : B * (m + 1) + m < A * (m + 1) := by
  have := Nat.mul_le_mul_right (m + 1) h
  rw [Nat.succ_mul] at this
  omega

theorem splitOnAux_asc {cs sep : List Char} (hc : ∀ c ∈ cs, c.toNat < 128)
    (hs : ∀ c ∈ sep, c.toNat < 128) (hm : 0 < sep.length) :
    ∀ (f b i j : Nat) (r : List (List Char)), j < sep.length → j ≤ i → b ≤ i - j →
      i ≤ cs.length →
      (cs.length + 1 - (i - j)) * (sep.length + 1) + (sep.length - j) < f →
      splitOnAux (ofList cs) (ofList sep) ⟨b⟩ ⟨i⟩ ⟨j⟩ (r.map ofList) =
        (splitSL cs sep cs.length f b i j r).map ofList
  | 0, _, _, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, b, i, j, r, hj, hji, hb, hi, hf => by
    rw [splitOnAux, splitSL]
    rw [atEnd_asc hc]
    by_cases hn : cs.length ≤ i
    · have hie : i = cs.length := by omega
      simp only [hn, decide_true, if_true]
      rw [extract_asc hc (by omega) hi]
      simp
    · simp only [hn, decide_false, Bool.false_eq_true, if_false]
      rw [get_asc hc (by omega), get_asc hs (by omega), headD_drop (by omega),
        headD_drop (by omega)]
      by_cases heq : (cs.getD i 'a' == sep.getD j 'a') = true
      · simp only [heq, if_true]
        rw [next_asc hc (by omega), next_asc hs (by omega), atEnd_asc hs]
        by_cases hend : sep.length ≤ j + 1
        · simp only [hend, decide_true, if_true]
          have hu : (⟨i + 1⟩ : Pos.Raw).unoffsetBy ⟨j + 1⟩ = ⟨i - j⟩ := by
            apply Pos.Raw.ext
            rw [Pos.Raw.byteIdx_unoffsetBy]
            change i + 1 - (j + 1) = i - j
            omega
          rw [hu, extract_asc hc hb (by omega)]
          have := splitOnAux_asc hc hs hm f (i + 1) (i + 1) 0 (((cs.drop b).take (i - j - b)) :: r)
            hm (by omega) (by omega) (by omega) (by
              have h1 := mu_lt (m := sep.length) (A := cs.length + 1 - (i - j))
                (B := cs.length + 1 - (i + 1 - 0)) (by omega)
              omega)
          rw [List.map_cons] at this
          have e0 : (0 : Pos.Raw) = ⟨0⟩ := rfl
          rw [e0, this]
        · simp only [hend, decide_false, Bool.false_eq_true, if_false]
          exact splitOnAux_asc hc hs hm f b (i + 1) (j + 1) r (by omega) (by omega) (by omega)
            (by omega) (by
              have : (i + 1) - (j + 1) = i - j := by omega
              rw [this]
              omega)
      · simp only [heq, Bool.false_eq_true, if_false]
        have hu : ((⟨i⟩ : Pos.Raw).unoffsetBy ⟨j⟩) = ⟨i - j⟩ := by
          apply Pos.Raw.ext
          rw [Pos.Raw.byteIdx_unoffsetBy]
        rw [hu, next_asc hc (by omega)]
        have e0 : (0 : Pos.Raw) = ⟨0⟩ := rfl
        rw [e0]
        exact splitOnAux_asc hc hs hm f b (i - j + 1) 0 r hm (by omega) (by omega) (by omega)
          (by
            have h1 := mu_lt (m := sep.length) (A := cs.length + 1 - (i - j))
              (B := cs.length + 1 - (i - j + 1 - 0)) (by omega)
            omega)

theorem splitOn_ofList_sep {cs sep : List Char} (hc : ∀ c ∈ cs, c.toNat < 128)
    (hs : ∀ c ∈ sep, c.toNat < 128) (hm : 0 < sep.length) :
    (String.ofList cs).splitOn (String.ofList sep) = (splitSepL cs sep).map String.ofList := by
  have hne : (String.ofList sep == "") = false := by
    rw [beq_eq_false_iff_ne, ne_eq, ← toList_inj, toList_ofList]
    cases sep with
    | nil => simp at hm
    | cons c s => simp
  unfold String.splitOn
  rw [hne]
  simp only [Bool.false_eq_true, if_false]
  have := splitOnAux_asc hc hs hm ((cs.length + 2) * (sep.length + 1) + 1) 0 0 0 [] hm (Nat.le_refl 0)
    (by omega) (by omega) (by
      have h1 := mu_lt (m := sep.length) (A := cs.length + 2) (B := cs.length + 1 - (0 - 0))
        (by omega)
      omega)
  exact this

end CFSG.KS.RouteP
