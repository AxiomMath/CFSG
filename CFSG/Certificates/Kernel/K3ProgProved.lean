module

public import CFSG.Certificates.Kernel.K3Defs
import CFSG.Certificates.Kernel.Common.StrSplit
import all Init.Data.String.Slice
import all Init.Data.String.Search

namespace CFSG.KC.K3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

namespace ProgP

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bA {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem bI {c t e : Bool} : Bool.rec (motive := fun _ => Bool) e t c = true ↔
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

variable (K : K3C)

theorem run0 (ch : Char) (rest : List Char) (t i v dg : Nat) :
    K.progRun (ch :: rest) t 0 i v dg =
      bAnd(Nat.blt t K.N, bAnd(Nat.beq (K3C.opOf ch.toNat) (K.OP t), K.progRun rest t 1 0 0 0)) := by
  unfold K3C.progRun
  dsimp only
  rw [sB]
  rfl

theorem run1 (ch : Char) (rest : List Char) (t i v dg : Nat) :
    K.progRun (ch :: rest) t 1 i v dg = bAnd(Nat.beq ch.toNat 32, K.progRun rest t 2 0 0 0) := by
  unfold K3C.progRun
  dsimp only
  rw [sB]
  rfl

theorem run2 (ch : Char) (rest : List Char) (t i v dg : Nat) :
    K.progRun (ch :: rest) t 2 i v dg =
      bIf(Nat.blt (CFSG.KC.SurjK.digV ch.toNat) 10,
        K.progRun rest t 2 i (Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV ch.toNat)) 1,
      bIf(Nat.beq ch.toNat 32, bAnd(Nat.beq dg 1, bAnd(Nat.beq v (K.arg t i),
        bAnd(Nat.blt (Nat.succ i) (K.nargs t), K.progRun rest t 2 (Nat.succ i) 0 0))),
      bIf(Nat.beq ch.toNat 10, bAnd(Nat.beq dg 1, bAnd(Nat.beq v (K.arg t i),
        bAnd(Nat.beq (Nat.succ i) (K.nargs t), K.progRun rest (Nat.succ t) 0 0 0 0))),
        false))) := by
  unfold K3C.progRun
  dsimp only
  rw [sB]
  rfl

theorem runNil (t ph i v dg : Nat) :
    K.progRun [] t ph i v dg = bAnd(Nat.beq ph 0, Nat.beq t K.N) := rfl

theorem digV_spec {c : Nat} (h : CFSG.KC.SurjK.digV c < 10) :
    48 ≤ c ∧ c ≤ 57 ∧ CFSG.KC.SurjK.digV c = c - 48 := by
  unfold CFSG.KC.SurjK.digV at h ⊢
  by_cases h1 : 48 ≤ c
  · have e1 : Nat.ble 48 c = true := Nat.ble_eq.mpr h1
    by_cases h2 : c ≤ 57
    · have e2 : Nat.ble c 57 = true := Nat.ble_eq.mpr h2
      rw [e1, e2]
      exact ⟨h1, h2, rfl⟩
    · have e2 : Nat.ble c 57 = false := by
        cases e : Nat.ble c 57
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true e) h2
      rw [e1, e2] at h
      exact absurd (h : 10 < 10) (Nat.lt_irrefl 10)
  · have e1 : Nat.ble 48 c = false := by
      cases e : Nat.ble 48 c
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true e) h1
    rw [e1] at h
    exact absurd (h : 10 < 10) (Nat.lt_irrefl 10)

theorem ff {b : Bool} (hb : b = false) (h : b = true) : False := by
  rw [hb] at h
  cases h

theorem char_of {ch : Char} {k : Nat} (c : Char) (hc : c.toNat = k) (h : ch.toNat = k) : ch = c :=
  Char.toNat_inj.1 (h.trans hc.symm)

theorem argRun (t : Nat) : ∀ (cs : List Char) (i v dg : Nat), K.progRun cs t 2 i v dg = true →
    ∃ ds rest, (∀ c ∈ ds, c.isDigit = true) ∧ (dg = 1 ∨ ds ≠ []) ∧
      ds.foldl (fun n c => n * 10 + (c.toNat - 48)) v = K.arg t i ∧
      ((cs = ds ++ ' ' :: rest ∧ i + 1 < K.nargs t ∧ K.progRun rest t 2 (i + 1) 0 0 = true) ∨
        (cs = ds ++ '\n' :: rest ∧ i + 1 = K.nargs t ∧ K.progRun rest (t + 1) 0 0 0 0 = true))
  | [], i, v, dg, h => (ff rfl h).elim
  | ch :: rest, i, v, dg, h => by
    rw [run2] at h
    rcases bI.1 h with ⟨hd, h'⟩ | ⟨-, h'⟩
    · obtain ⟨ds, rest', hdig, -, hf, hcase⟩ := argRun t rest i _ 1 h'
      have hs := digV_spec (Nat.blt_eq.mp hd)
      have h0 : '0'.toNat = 48 := rfl
      have h9 : '9'.toNat = 57 := rfl
      refine ⟨ch :: ds, rest', ?_, Or.inr (List.cons_ne_nil _ _), ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact Char.isDigit_iff_toNat.2 ⟨h0 ▸ hs.1, h9 ▸ hs.2.1⟩
        · exact hdig c hc
      · have e : Nat.add (Nat.mul v 10) (CFSG.KC.SurjK.digV ch.toNat) = v * 10 + (ch.toNat - 48) := by
          rw [hs.2.2]
          rfl
        rw [e] at hf
        exact hf
      · rcases hcase with ⟨e, h1, h2⟩ | ⟨e, h1, h2⟩
        · exact Or.inl ⟨by rw [e]; rfl, h1, h2⟩
        · exact Or.inr ⟨by rw [e]; rfl, h1, h2⟩
    · rcases bI.1 h' with ⟨hsp, h''⟩ | ⟨-, h''⟩
      · obtain ⟨hdg, h3⟩ := bA.1 h''
        obtain ⟨hv, h4⟩ := bA.1 h3
        obtain ⟨hn, hr⟩ := bA.1 h4
        refine ⟨[], rest, by simp, Or.inl (Nat.eq_of_beq_eq_true hdg),
          (Nat.eq_of_beq_eq_true hv), Or.inl ⟨?_, Nat.blt_eq.mp hn, hr⟩⟩
        rw [char_of ' ' rfl (Nat.eq_of_beq_eq_true hsp)]
        rfl
      · rcases bI.1 h'' with ⟨hnl, h3⟩ | ⟨-, h3⟩
        · obtain ⟨hdg, h4⟩ := bA.1 h3
          obtain ⟨hv, h5⟩ := bA.1 h4
          obtain ⟨hn, hr⟩ := bA.1 h5
          refine ⟨[], rest, by simp, Or.inl (Nat.eq_of_beq_eq_true hdg),
            (Nat.eq_of_beq_eq_true hv), Or.inr ⟨?_, Nat.eq_of_beq_eq_true hn, hr⟩⟩
          rw [char_of '\n' rfl (Nat.eq_of_beq_eq_true hnl)]
          rfl
        · exact absurd h3 (by decide)

theorem toNat?_ofList {ds : List Char} (hne : ds ≠ []) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (String.ofList ds).toNat? = some (CFSG.KC.Str.decVal ds) := by
  open String in
  simp only [String.toNat?, Slice.toNat?, Slice.isNat]
  open String in
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, copy_toSlice, toList_ofList]
  rw [CFSG.KC.Str.forIn_yield (y := ((none : Option Bool), true)) ds]
  · simp only [hne, ↓reduceIte]
    split
    · congr 1
      exact CFSG.KC.Str.foldl_congr _ _ ds 0 fun x hx n => by
        simp [CFSG.KC.Str.ne_underscore (hd x hx)]
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [CFSG.KC.Str.ne_underscore (hd c hc), hd c hc]
    rfl

theorem num_of {ds : List Char} (hne : ds ≠ []) (hd : ∀ c ∈ ds, c.isDigit = true) :
    ((String.ofList ds).toNat?).getD 0 = CFSG.KC.Str.decVal ds := by
  rw [toNat?_ofList hne hd]
  rfl

theorem sp_not_mem {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) : ' ' ∉ ds := fun h =>
  absurd (hd ' ' h) (by decide)

theorem nl_not_mem {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) : '\n' ∉ ds := fun h =>
  absurd (hd '\n' h) (by decide)

theorem splitSp (s : List Char) :
    (String.ofList s).splitOn " " = (s.splitOn ' ').map String.ofList := by
  have e : (" " : String) = String.singleton ' ' := by decide
  rw [e, CFSG.KC.Str.splitOn_ofList]

theorem nargs_eq (t : Nat) : K.nargs t = if K.OP t = 2 then 2 else 3 := by
  unfold K3C.nargs
  cases h : Nat.beq (K.OP t) 2
  · have hne : K.OP t ≠ 2 := fun e => by
      rw [e] at h
      exact absurd h (by decide)
    simp [hne]
  · simp [Nat.eq_of_beq_eq_true h]

theorem opOf_spec {c : Nat} {o : Nat} (h : K3C.opOf c = o) (ho : o < 3) :
    (o = 0 ∧ c = 109) ∨ (o = 1 ∧ c = 112) ∨ (o = 2 ∧ c = 118) := by
  unfold K3C.opOf at h
  cases h1 : Nat.beq c 109
  · cases h2 : Nat.beq c 112
    · cases h3 : Nat.beq c 118
      · rw [h1, h2, h3] at h
        change 3 = o at h
        omega
      · rw [h1, h2, h3] at h
        exact Or.inr (Or.inr ⟨h.symm, Nat.eq_of_beq_eq_true h3⟩)
    · rw [h1, h2] at h
      exact Or.inr (Or.inl ⟨h.symm, Nat.eq_of_beq_eq_true h2⟩)
  · rw [h1] at h
    exact Or.inl ⟨h.symm, Nat.eq_of_beq_eq_true h1⟩

open CFSG.EvenSmallLie.Child3.SelK3 CFSG.Sporadic.Th.Native in
theorem lineRun (t : Nat) (ch : Char) (rest : List Char)
    (h : K.progRun (ch :: rest) t 0 0 0 0 = true) (hop : K.OP t < 3) :
    t < K.N ∧ ∃ l rest', ch :: rest = l ++ '\n' :: rest' ∧ '\n' ∉ l ∧
      parseInstr (String.ofList l) = some (instrOf K t) ∧
      K.progRun rest' (t + 1) 0 0 0 0 = true := by
  rw [run0] at h
  obtain ⟨hN, h1⟩ := bA.1 h
  obtain ⟨hopc, h2⟩ := bA.1 h1
  refine ⟨Nat.blt_eq.mp hN, ?_⟩
  obtain _ | ⟨c1, rest1⟩ := rest
  · exact (ff rfl h2).elim
  rw [run1] at h2
  obtain ⟨hsp, h3⟩ := bA.1 h2
  have hc1 : c1 = ' ' := char_of ' ' rfl (Nat.eq_of_beq_eq_true hsp)
  subst hc1
  have hna := nargs_eq K t
  have hop' := opOf_spec (Nat.eq_of_beq_eq_true hopc) hop
  obtain ⟨ds0, r0, hd0, hne0, hf0, hc0⟩ := argRun K t rest1 0 0 0 h3
  have hne0 : ds0 ≠ [] := hne0.resolve_left (by decide)
  obtain ⟨e0, h4⟩ : rest1 = ds0 ++ ' ' :: r0 ∧ K.progRun r0 t 2 (0 + 1) 0 0 = true := by
    rcases hc0 with ⟨e0, -, h4⟩ | ⟨-, e, -⟩
    · exact ⟨e0, h4⟩
    · split at hna <;> omega
  obtain ⟨ds1, r1, hd1, hne1, hf1, hc1⟩ := argRun K t r0 1 0 0 h4
  have hne1 : ds1 ≠ [] := hne1.resolve_left (by decide)
  have hcn : ch.toNat = 109 ∨ ch.toNat = 112 ∨ ch.toNat = 118 := by
    rcases hop' with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  have hch : ch ≠ ' ' ∧ ch ≠ '\n' := by
    constructor
    · intro hc
      rw [hc] at hcn
      exact absurd hcn (by decide)
    · intro hc
      rw [hc] at hcn
      exact absurd hcn (by decide)
  have hsc : ' ' ∉ [ch] := by simpa using hch.1.symm
  rcases hc1 with ⟨e1, hlt, h5⟩ | ⟨e1, hn2, h5⟩
  ·
    have h3n : K.OP t ≠ 2 := by
      intro e
      simp only [e, ↓reduceIte] at hna
      omega
    obtain ⟨ds2, r2, hd2, hne2, hf2, hc2⟩ := argRun K t r1 2 0 0 h5
    have hne2 : ds2 ≠ [] := hne2.resolve_left (by decide)
    rcases hc2 with ⟨-, e, -⟩ | ⟨e2, -, h6⟩
    · simp only [h3n, ↓reduceIte] at hna
      omega
    refine ⟨ch :: ' ' :: (ds0 ++ ' ' :: (ds1 ++ ' ' :: ds2)), r2, ?_, ?_, ?_, h6⟩
    · rw [e0, e1, e2]
      simp
    · simp [hch.2.symm, nl_not_mem hd0, nl_not_mem hd1, nl_not_mem hd2]
    · have hs : (ch :: ' ' :: (ds0 ++ ' ' :: (ds1 ++ ' ' :: ds2))).splitOn ' ' = [[ch], ds0, ds1, ds2] := by
        rw [show ch :: ' ' :: (ds0 ++ ' ' :: (ds1 ++ ' ' :: ds2)) =
          [ch] ++ ' ' :: (ds0 ++ ' ' :: (ds1 ++ ' ' :: ds2)) from rfl,
          List.splitOn_append_cons_self_of_not_mem hsc,
          List.splitOn_append_cons_self_of_not_mem (sp_not_mem hd0),
          List.splitOn_append_cons_self_of_not_mem (sp_not_mem hd1),
          List.splitOn_eq_singleton (sp_not_mem hd2)]
      unfold parseInstr
      rw [splitSp, hs]
      have v0 := num_of hne0 hd0
      have v1 := num_of hne1 hd1
      have v2 := num_of hne2 hd2
      unfold CFSG.KC.Str.decVal at v0 v1 v2
      rw [hf0] at v0
      rw [hf1] at v1
      rw [hf2] at v2
      rcases hop' with ⟨ho, e⟩ | ⟨ho, e⟩ | ⟨ho, e⟩
      · rw [char_of 'm' rfl e]
        simp only [List.map_cons, List.map_nil]
        rw [v0, v1, v2]
        simp only [instrOf, ho, ↓reduceIte]
        rfl
      · rw [char_of 'p' rfl e]
        simp only [List.map_cons, List.map_nil]
        rw [v0, v1, v2]
        simp only [instrOf, ho, ↓reduceIte]
        rfl
      · exact absurd ho h3n
  ·
    have h2n : K.OP t = 2 := by
      refine Classical.byContradiction fun hne => ?_
      simp only [hne, ↓reduceIte] at hna
      omega
    refine ⟨ch :: ' ' :: (ds0 ++ ' ' :: ds1), r1, ?_, ?_, ?_, ?_⟩
    · rw [e0, e1]
      simp
    · simp [hch.2.symm, nl_not_mem hd0, nl_not_mem hd1]
    · have hs : (ch :: ' ' :: (ds0 ++ ' ' :: ds1)).splitOn ' ' = [[ch], ds0, ds1] := by
        rw [show ch :: ' ' :: (ds0 ++ ' ' :: ds1) = [ch] ++ ' ' :: (ds0 ++ ' ' :: ds1) from rfl,
          List.splitOn_append_cons_self_of_not_mem hsc,
          List.splitOn_append_cons_self_of_not_mem (sp_not_mem hd0),
          List.splitOn_eq_singleton (sp_not_mem hd1)]
      unfold parseInstr
      rw [splitSp, hs]
      have v0 := num_of hne0 hd0
      have v1 := num_of hne1 hd1
      unfold CFSG.KC.Str.decVal at v0 v1
      rw [hf0] at v0
      rw [hf1] at v1
      rcases hop' with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨-, e⟩
      · omega
      · omega
      · rw [char_of 'v' rfl e]
        simp only [List.map_cons, List.map_nil]
        rw [v0, v1]
        simp only [instrOf, h2n]
        rfl
    · exact h5

open CFSG.EvenSmallLie.Child3.SelK3 in
theorem progMain (hop : ∀ t < K.N, K.OP t < 3) : ∀ (k : Nat) (cs : List Char) (t : Nat),
    cs.length ≤ k → K.progRun cs t 0 0 0 0 = true →
    t ≤ K.N ∧ ((cs.splitOn '\n').map String.ofList).filterMap parseInstr =
      (List.range' t (K.N - t)).map (instrOf K) := by
  intro k
  induction k with
  | zero =>
    intro cs t hl h
    obtain rfl : cs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    have h1 : Nat.beq t K.N = true := h
    have e : t = K.N := Nat.eq_of_beq_eq_true h1
    subst e
    refine ⟨Nat.le_refl _, ?_⟩
    rw [Nat.sub_self, List.range'_zero, List.splitOn_nil]
    have hp : parseInstr (String.ofList []) = none := by
      unfold parseInstr
      rw [splitSp, List.splitOn_nil]
      rfl
    simp [hp]
  | succ k ih =>
    intro cs t hl h
    obtain _ | ⟨ch, rest⟩ := cs
    · exact ih [] t (Nat.zero_le _) h
    by_cases ht : t < K.N
    · obtain ⟨-, l, rest', e, hl', hp, hr⟩ := lineRun K t ch rest h (hop t ht)
      have hlen : rest'.length ≤ k := by
        have := congrArg List.length e
        simp at this hl
        omega
      obtain ⟨-, ih'⟩ := ih rest' (t + 1) hlen hr
      refine ⟨Nat.le_of_lt ht, ?_⟩
      rw [e, List.splitOn_append_cons_self_of_not_mem hl', List.map_cons, List.filterMap_cons, hp,
        ih', show K.N - t = (K.N - (t + 1)) + 1 by omega, List.range'_succ]
      rfl
    · rw [run0] at h
      exact absurd (Nat.blt_eq.mp (bA.1 h).1) ht

end ProgP

open CFSG.EvenSmallLie.Child3.SelK3 ProgP in
public theorem progK_sound_proved {K : K3C} {cs : List Char} (h : K.progK cs = true)
    (hs : ∀ t < K.N, K.stepK t = true) :
    parseProg (String.ofList cs) = (List.range K.N).map (instrOf K) := by
  have hop : ∀ t < K.N, K.OP t < 3 := by
    intro t ht
    have h1 := hs t ht
    unfold K3C.stepK at h1
    rw [sB] at h1
    exact Nat.blt_eq.mp (bA.1 (bA.1 h1).2).1
  have e : ("\n" : String) = String.singleton '\n' := by decide
  unfold parseProg
  rw [e, CFSG.KC.Str.splitOn_ofList, List.range_eq_range']
  have := (progMain K hop cs.length cs 0 (Nat.le_refl _) h).2
  rw [Nat.sub_zero] at this
  exact this

end CFSG.KC.K3
