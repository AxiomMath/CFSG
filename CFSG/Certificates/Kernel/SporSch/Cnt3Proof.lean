module

public import Certificates.Data.Kernel.SporSch.PairCl
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.RawAgree
import CFSG.Certificates.Kernel.SporSch.TabSum
import CFSG.Sporadic.Schreier.PairWords
public import Certificates.Data.CFSGNative.PairSchreier.Core
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KS.SporSch.Cnt3P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
  CFSG.KS.SporSch

variable {n : Nat}

@[expose] def WAg (n : Nat) (W W' : List (Array Nat)) : Prop :=
  ∀ p < n, evR W p = evR W' p ∧ evR W p < n

theorem WAg.append {A A' B B' : List (Array Nat)} (hA : WAg n A A') (hB : WAg n B B') :
    WAg n (A ++ B) (A' ++ B') := fun p hp => by
  rw [evR_append, evR_append, ← (hA p hp).1]
  exact hB _ (hA p hp).2

theorem evPow_ag {W W' : List (Array Nat)} (h : WAg n W W') :
    ∀ e, ∀ p < n, evPow W e p = evPow W' e p ∧ evPow W e p < n
  | 0, p, hp => ⟨rfl, hp⟩
  | e + 1, p, hp => by
    obtain ⟨h1, h2⟩ := evPow_ag h e p hp
    rw [evPow, evPow, ← h1]
    exact h _ h2

theorem fixB_ag {W W' : List (Array Nat)} (h : WAg n W W') {bs : List Nat}
    (hbs : ∀ b ∈ bs, b < n) (e : Nat) :
    PairNative.fixB bs W e = PairNative.fixB bs W' e := by
  rw [Bool.eq_iff_iff, PairNative.fixB, PairNative.fixB, List.all_eq_true, List.all_eq_true]
  exact forall₂_congr fun b hb => by rw [(evPow_ag h e b (hbs b hb)).1]

theorem ordB_ag {W W' : List (Array Nat)} (h : WAg n W W') {bs : List Nat}
    (hbs : ∀ b ∈ bs, b < n) (m : Nat) :
    PairNative.ordB bs W m = PairNative.ordB bs W' m := by
  unfold PairNative.ordB
  simp only [fixB_ag h hbs]

theorem patW_cons (x y : List (Array Nat)) (b : Bool) (pat : List Bool) :
    patW x y (b :: pat) = patW x y pat ++ (if b then y else x) := by
  simp [patW, List.map_append, List.flatten_append]

theorem patW_ag {x y y' : List (Array Nat)} (hx : WAg n x x) (hy : WAg n y y') :
    ∀ pat, WAg n (patW x y pat) (patW x y' pat)
  | [] => fun p hp => ⟨rfl, hp⟩
  | b :: pat => by
    rw [patW_cons, patW_cons]
    refine (patW_ag hx hy pat).append ?_
    cases b
    · exact hx
    · exact hy

theorem condsOK_ag {x y y' : List (Array Nat)} (hx : WAg n x x) (hy : WAg n y y')
    {bs : List Nat} (hbs : ∀ b ∈ bs, b < n) (conds : List (List Bool × Nat)) :
    PairNative.condsOK bs x y conds = PairNative.condsOK bs x y' conds := by
  have e : ∀ c : List Bool × Nat, PairNative.ordB bs (patW x y c.1) c.2 =
      PairNative.ordB bs (patW x y' c.1) c.2 := fun c => ordB_ag (patW_ag hx hy c.1) hbs c.2
  unfold PairNative.condsOK
  simp only [e]

@[expose] def RangeL (n w : Nat) (Ws : List Nat) : Prop :=
  ∀ W ∈ Ws, ∀ q < n, pg w (mask w) W q < n

theorem bAnd_and (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem rangeL_of_canonL {w : Nat} : ∀ {Ws : List Nat}, canonL n w Ws = true → RangeL n w Ws
  | [], _, W, hW => by simp at hW
  | V :: Ws, h, W, hW => by
    change bAnd(CFSG.KS.Prim.canonK n w (mask w) (Nat.mul n w) V, canonL n w Ws) = true at h
    rw [bAnd_iff] at h
    rcases List.mem_cons.1 hW with rfl | hW
    · intro q hq
      have := (Raw.Orb.allN_iff.1 (CFSG.KS.Raw.range_of_canonK h.1)) q hq
      simpa using this
    · exact rangeL_of_canonL h.2 W hW

theorem evRK_eq {w : Nat} : ∀ {Ws : List Nat}, RangeL n w Ws →
    ∀ p < n, evRK w Ws p = evR (Ws.map (Raw.unpack n w)) p ∧ evRK w Ws p < n
  | [], _, p, hp => ⟨rfl, hp⟩
  | W :: Ws, hW, p, hp => by
    have h1 := hW W List.mem_cons_self p hp
    have ih := evRK_eq (Ws := Ws) (fun V hV => hW V (List.mem_cons_of_mem _ hV)) _ h1
    change strictN (pg w (mask w) W p) (evRK w Ws) = _ ∧
      strictN (pg w (mask w) W p) (evRK w Ws) < n
    rw [strictN_val]
    refine ⟨?_, ih.2⟩
    rw [ih.1, List.map_cons]
    change _ = evR (Ws.map (Raw.unpack n w)) ((Raw.unpack n w W)[p]!)
    rw [Raw.Orb.unpack_get hp]

theorem rangeL_ag {w : Nat} {Ws : List Nat} (hW : RangeL n w Ws) :
    WAg n (Ws.map (Raw.unpack n w)) (Ws.map (Raw.unpack n w)) := fun p hp =>
  ⟨rfl, (evRK_eq hW p hp).1 ▸ (evRK_eq hW p hp).2⟩

theorem evPowK_eq {w : Nat} {Ws : List Nat} (hW : RangeL n w Ws) :
    ∀ e, ∀ p < n, evPowK w Ws e p = evPow (Ws.map (Raw.unpack n w)) e p ∧ evPowK w Ws e p < n
  | 0, p, hp => ⟨rfl, hp⟩
  | e + 1, p, hp => by
    have ih := evPowK_eq hW e p hp
    change strictN (evPowK w Ws e p) (evRK w Ws) = _ ∧ strictN (evPowK w Ws e p) (evRK w Ws) < n
    rw [strictN_val, evPow, ← ih.1]
    exact evRK_eq hW _ ih.2

theorem fixBK_eq {w : Nat} {Ws : List Nat} (hW : RangeL n w Ws) (e : Nat) :
    ∀ {bs : List Nat}, (∀ b ∈ bs, b < n) →
      fixBK w bs Ws e = PairNative.fixB bs (Ws.map (Raw.unpack n w)) e
  | [], _ => rfl
  | b :: bs, h => by
    change bAnd(Nat.beq (evPowK w Ws e b) b, fixBK w bs Ws e) = _
    rw [bAnd_and, fixBK_eq hW e (fun c hc => h c (List.mem_cons_of_mem b hc)),
      (evPowK_eq hW e b (h b List.mem_cons_self)).1]
    simp only [PairNative.fixB, List.all_cons]
    congr 1

theorem blt_false_iff {a b : Nat} : Nat.blt a b = false ↔ ¬a < b := by
  rw [Bool.eq_false_iff, Ne, Nat.blt_eq]

theorem beq_false_iff {a b : Nat} : Nat.beq a b = false ↔ ¬a = b := by
  rw [Bool.eq_false_iff, Ne, Nat.beq_eq]

theorem ordB0_eq {w m : Nat} {bs Ws : List Nat} (hW : RangeL n w Ws) (hbs : ∀ b ∈ bs, b < n) :
    ordB0 w bs Ws m = PairNative.ordB bs (Ws.map (Raw.unpack n w)) m := by
  unfold ordB0 PairNative.ordB
  rw [bAnd_and, fixBK_eq hW m hbs]
  congr 1
  have key : ∀ d, (bIf(bAnd(Nat.blt (nat_lit 1) d, Nat.beq (Nat.mod m d) (nat_lit 0)),
      bIf(fixBK w bs Ws (Nat.div m d), false, true), true) = true) ↔
      (1 < d → m % d = 0 → PairNative.fixB bs (Ws.map (Raw.unpack n w)) (m / d) = false) := by
    intro d
    rw [fixBK_eq hW _ hbs]
    change (Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool) true false
        (PairNative.fixB bs (Ws.map (Raw.unpack n w)) (m / d)))
      (Bool.rec (motive := fun _ => Bool) false (Nat.beq (m % d) 0) (Nat.blt 1 d)) = true) ↔ _
    cases h1 : Nat.blt 1 d <;> cases h2 : Nat.beq (m % d) 0 <;>
      cases h3 : PairNative.fixB bs (Ws.map (Raw.unpack n w)) (m / d) <;>
      simp only [blt_false_iff, beq_false_iff, Nat.blt_eq, Nat.beq_eq] at h1 h2 <;>
      simp [h1, h2]
  rw [Bool.eq_iff_iff, Raw.Orb.allN_iff, List.all_eq_true]
  simp only [key, CFSG.Sporadic.Schreier.Native.divParts, List.mem_map, List.mem_filter,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro h e ⟨d, ⟨hd, h1, h2⟩, rfl⟩
    exact h d hd h1 h2
  · intro h d hd h1 h2
    exact h _ ⟨d, ⟨hd, h1, h2⟩, rfl⟩

theorem appK_eq (a b : List Nat) : cnt3.appK a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    change x :: cnt3.appK a b = _
    rw [ih]
    rfl

theorem patWK_cons (XP YP : List Nat) (b : Bool) (pat : List Bool) :
    cnt3.patWK XP YP (b :: pat) = cnt3.patWK XP YP pat ++ (if b then YP else XP) := by
  change cnt3.appK (cnt3.patWK XP YP pat) (Bool.rec (motive := fun _ => List Nat) XP YP b) = _
  rw [appK_eq]
  cases b <;> rfl

theorem patWK_map (w : Nat) (XP YP : List Nat) :
    ∀ pat, (cnt3.patWK XP YP pat).map (Raw.unpack n w) =
      patW (XP.map (Raw.unpack n w)) (YP.map (Raw.unpack n w)) pat
  | [] => rfl
  | b :: pat => by
    rw [patWK_cons, patW_cons, List.map_append, patWK_map w XP YP pat]
    cases b <;> rfl

theorem patWK_range {w : Nat} {XP YP : List Nat} (hX : RangeL n w XP) (hY : RangeL n w YP) :
    ∀ pat, RangeL n w (cnt3.patWK XP YP pat)
  | [] => fun W hW => by simp [cnt3.patWK] at hW
  | b :: pat => fun W hW => by
    rw [patWK_cons, List.mem_append] at hW
    rcases hW with hW | hW
    · exact patWK_range hX hY pat W hW
    · cases b
      · exact hX W hW
      · exact hY W hW

theorem condsK_eq {w : Nat} {bs XP YP : List Nat} (hX : RangeL n w XP) (hY : RangeL n w YP)
    (hbs : ∀ b ∈ bs, b < n) : ∀ conds : List (List Bool × Nat),
      cnt3.condsK w bs XP YP conds =
        PairNative.condsOK bs (XP.map (Raw.unpack n w)) (YP.map (Raw.unpack n w)) conds
  | [] => rfl
  | (pat, o) :: conds => by
    change bAnd(ordB0 w bs (cnt3.patWK XP YP pat) o, cnt3.condsK w bs XP YP conds) = _
    rw [bAnd_and, condsK_eq hX hY hbs conds, ordB0_eq (patWK_range hX hY pat) hbs, patWK_map]
    simp only [PairNative.condsOK, List.all_cons]

theorem sum_flatMap_map {α β : Type} (l : List α) (F : α → List β) (g : β → Nat) :
    ((l.flatMap F).map g).sum = (l.map fun a => ((F a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem ofFn_range {α : Type} (m : Nat) (f : Nat → α) :
    List.ofFn (n := m) (fun k : Fin m => f k.val) = (List.range m).map f := by
  apply List.ext_getElem <;> simp

theorem levelArr_toList (L : Array Level) (i : Nat) :
    (levelArr L i).toList = (List.range L[i]!.pts.size).map fun k => L[i]!.tr[k]! := by
  rw [levelArr, Array.toList_ofFn]
  exact ofFn_range _ (fun k => L[i]!.tr[k]!)

theorem blockOf_one (A : Array (Array Nat)) :
    (blockOf n [A]).toList = A.toList.map fun t => compA n t (idA n) := by
  rw [toList_blockOf_cons]
  induction A.toList with
  | nil => rfl
  | cons t l ih =>
    rw [List.flatMap_cons, List.map_cons, ← ih]
    rfl

theorem countW_blocks (f : List (Array Nat) → Bool) (L : Array Level) :
    PairNative.countW f (blocksOf n L [[0], [1, 2]]) [] =
      ∑ k0 ∈ Finset.range L[0]!.pts.size, ∑ k1 ∈ Finset.range L[1]!.pts.size,
        ∑ k2 ∈ Finset.range L[2]!.pts.size,
          if f [compA n L[1]!.tr[k1]! (compA n L[2]!.tr[k2]! (idA n)),
            compA n L[0]!.tr[k0]! (idA n)] = true then 1 else 0 := by
  simp only [blocksOf, List.map_cons, List.map_nil]
  rw [PairNative.countW, foldl_array_add_eq_sum, blockOf_one, levelArr_toList, List.map_map,
    List.map_map, Tab.lsum]
  refine Finset.sum_congr rfl fun k0 _ => ?_
  rw [Function.comp_apply, Function.comp_apply, PairNative.countW, foldl_array_add_eq_sum,
    toList_blockOf_cons, levelArr_toList, sum_flatMap_map, List.map_map, Tab.lsum]
  refine Finset.sum_congr rfl fun k1 _ => ?_
  rw [Function.comp_apply, blockOf_one, levelArr_toList, List.map_map, List.map_map, List.map_map,
    Tab.lsum]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  rfl

@[expose] noncomputable def vv (n w : Nat) (LR TR : Nat → Nat) (bs : List Nat) (m : Nat)
    (XP : List Nat) (conds : List (List Bool × Nat)) (k0 k1 k2 : Nat) : Nat :=
  nIf(ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
      trK n (Nat.mul n w) LR TR 0 k0] m,
    nIf(cnt3.condsK w bs XP [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
      trK n (Nat.mul n w) LR TR 0 k0] conds, 1048577, 1), 0)

theorem step_eq (o c : Bool) (s : Nat) :
    Bool.rec (motive := fun _ => Nat) s
        (Bool.rec (motive := fun _ => Nat) (Nat.succ s) (Nat.add s 1048577) c) o =
      s + Bool.rec (motive := fun _ => Nat) 0 (Bool.rec (motive := fun _ => Nat) 1 1048577 c) o := by
  cases o <;> cases c <;> rfl

theorem cnt3_eq (n w : Nat) (LR TR : Nat → Nat) (bs : List Nat) (m : Nat) (XP : List Nat)
    (conds : List (List Bool × Nat)) (k0 : Nat) :
    cnt3 n w LR TR bs m XP conds k0 = ∑ k1 ∈ Finset.range (rcnt (LR 1)),
      ∑ k2 ∈ Finset.range (rcnt (LR 2)), vv n w LR TR bs m XP conds k0 k1 k2 := by
  unfold cnt3
  simp only [strictN_val]
  refine (Tab.foldUp_add (fun k1 => ∑ k2 ∈ Finset.range (rcnt (LR 2)),
    vv n w LR TR bs m XP conds k0 k1 k2) (fun k1 _ s => ?_) 0).trans (Nat.zero_add _)
  exact Tab.foldUp_add (fun k2 => vv n w LR TR bs m XP conds k0 k1 k2)
    (fun k2 _ s => step_eq _ _ s) s

theorem vv_split (n w : Nat) (LR TR : Nat → Nat) (bs : List Nat) (m : Nat) (XP : List Nat)
    (conds : List (List Bool × Nat)) (k0 k1 k2 : Nat) :
    vv n w LR TR bs m XP conds k0 k1 k2 =
      (if ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
        trK n (Nat.mul n w) LR TR 0 k0] m = true then 1 else 0) +
      1048576 * (if (ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
        trK n (Nat.mul n w) LR TR 0 k0] m && cnt3.condsK w bs XP
          [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
            trK n (Nat.mul n w) LR TR 0 k0] conds) = true then 1 else 0) := by
  unfold vv
  cases ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
    trK n (Nat.mul n w) LR TR 0 k0] m <;>
  cases cnt3.condsK w bs XP [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
    trK n (Nat.mul n w) LR TR 0 k0] conds <;> rfl

section Chain

variable {w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat}
  (hb : Binds n w PS kS 3 BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP)
include hb hl

theorem base_lt3 : ∀ t < 3, base[t]! < n := fun t ht => by
  obtain ⟨-, -, hR, -⟩ := Raw.Orb.levelK_facts (hl t ht)
  rw [hb.2.2.2.2.2.2 t ht, ← hR.root]
  exact (hR.pt 0 hR.c_pos).1

include hp

theorem lev_agree {i : Nat} (hi : i < 3) :
    (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), ∀ x < n, ((rawLevels n S base)[i]!.tr[k]!)[x]! =
        pg w (mask w) (trK n (Nat.mul n w) LR TR i k) x ∧
          pg w (mask w) (trK n (Nat.mul n w) LR TR i k) x < n := by
  obtain ⟨A, hP⟩ := Raw.Orb.agree_levelK hb hp (base_lt3 hb hl) hi (hl i hi)
  refine ⟨A.cnt.symm, fun k hk x hx => ?_⟩
  have h1 := (A.tr k (A.cnt ▸ hk)).1 ⟨x, hx⟩
  have h2 := (hP k hk).1 ⟨x, hx⟩
  change pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x = _ at h2
  change _ = pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x ∧
    pg w (mask w) (TR (roff n (n * w) (LR i) + k)) x < n
  rw [h2]
  exact ⟨h1, Fin.isLt _⟩

theorem word_ag {k0 k1 k2 : Nat} (h0 : k0 < rcnt (LR 0)) (h1 : k1 < rcnt (LR 1))
    (h2 : k2 < rcnt (LR 2)) :
    WAg n [compA n (rawLevels n S base)[1]!.tr[k1]! (compA n (rawLevels n S base)[2]!.tr[k2]!
        (idA n)), compA n (rawLevels n S base)[0]!.tr[k0]! (idA n)]
      ([trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
        trK n (Nat.mul n w) LR TR 0 k0].map (Raw.unpack n w)) := fun p hpn => by
  have a0 := (lev_agree hb hp hl (i := 0) (by norm_num)).2 k0 h0
  have a1 := (lev_agree hb hp hl (i := 1) (by norm_num)).2 k1 h1
  have a2 := (lev_agree hb hp hl (i := 2) (by norm_num)).2 k2 h2
  have q2 := a2 p hpn
  have q1 := a1 _ q2.2
  have q0 := a0 _ q1.2
  change (compA n (rawLevels n S base)[0]!.tr[k0]! (idA n))[(compA n (rawLevels n S base)[1]!.tr[k1]!
      (compA n (rawLevels n S base)[2]!.tr[k2]! (idA n)))[p]!]! =
      (Raw.unpack n w (trK n (Nat.mul n w) LR TR 0 k0))[(Raw.unpack n w
        (trK n (Nat.mul n w) LR TR 1 k1))[(Raw.unpack n w (trK n (Nat.mul n w) LR TR 2 k2))[p]!]!]! ∧
    (compA n (rawLevels n S base)[0]!.tr[k0]! (idA n))[(compA n (rawLevels n S base)[1]!.tr[k1]!
      (compA n (rawLevels n S base)[2]!.tr[k2]! (idA n)))[p]!]! < n
  have hq1 := q2.2
  have hq0 := q1.2
  rw [compA_get hpn, compA_get hpn, idA_get hpn, q2.1, q1.1, compA_get hq0, idA_get hq0, q0.1,
    Raw.Orb.unpack_get hpn, Raw.Orb.unpack_get hq1, Raw.Orb.unpack_get hq0]
  exact ⟨rfl, q0.2⟩

end Chain

end CFSG.KS.SporSch.Cnt3P

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.PairNative

theorem cnt3_proved {n w kS BP m : Nat} {PS PSI LR TR TRI CS : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs XP : List Nat} {conds : List (List Bool × Nat)}
    (hb : Binds n w PS kS 3 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 3 BP) (hbs : base.toList = bs)
    (hX : canonL n w XP = true) (hsz : rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (h : ∀ k0 < rcnt (LR 0), cnt3 n w LR TR bs m XP conds k0 = CS k0) :
    countW (fun y => ordB bs y m) (blocksOf n (rawLevels n S base) [[0], [1, 2]]) [] =
        sumN (rcnt (LR 0)) (fun k0 => Nat.mod (CS k0) 1048576) ∧
      countW (fun y => ordB bs y m && condsOK bs (XP.map (unpack n w)) y conds)
          (blocksOf n (rawLevels n S base) [[0], [1, 2]]) [] =
        sumN (rcnt (LR 0)) (fun k0 => Nat.div (CS k0) 1048576) := by
  have hbsl : ∀ b ∈ bs, b < n := by
    intro b hb'
    rw [← hbs, Array.mem_toList_iff] at hb'
    obtain ⟨t, ht, rfl⟩ := Array.mem_iff_getElem.1 hb'
    have ht3 : t < 3 := by rw [← hb.2.2.2.2.2.1]; exact ht
    have := Cnt3P.base_lt3 hb hl t ht3
    rwa [getElem!_pos base t ht] at this
  have hs := fun i (hi : i < 3) => (Cnt3P.lev_agree hb hp hl hi).1
  have hXr := Cnt3P.rangeL_of_canonL hX
  have hK : ∀ {k0 k1 k2 : Nat}, k0 < rcnt (LR 0) → k1 < rcnt (LR 1) → k2 < rcnt (LR 2) →
      Cnt3P.RangeL n w [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
        trK n (Nat.mul n w) LR TR 0 k0] := by
    intro k0 k1 k2 h0 h1 h2 W hW q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl | rfl
    · exact ((Cnt3P.lev_agree hb hp hl (i := 2) (by norm_num)).2 k2 h2 q hq).2
    · exact ((Cnt3P.lev_agree hb hp hl (i := 1) (by norm_num)).2 k1 h1 q hq).2
    · exact ((Cnt3P.lev_agree hb hp hl (i := 0) (by norm_num)).2 k0 h0 q hq).2
  have hA : ∀ k0 < rcnt (LR 0), (∑ k1 ∈ Finset.range (rcnt (LR 1)),
      ∑ k2 ∈ Finset.range (rcnt (LR 2)),
        if ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
          trK n (Nat.mul n w) LR TR 0 k0] m = true then 1 else 0) < 1048576 := by
    intro k0 _
    have hle : (∑ k1 ∈ Finset.range (rcnt (LR 1)), ∑ k2 ∈ Finset.range (rcnt (LR 2)),
        if ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
          trK n (Nat.mul n w) LR TR 0 k0] m = true then 1 else 0) ≤
        ∑ k1 ∈ Finset.range (rcnt (LR 1)), ∑ k2 ∈ Finset.range (rcnt (LR 2)), 1 :=
      Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ => by split_ifs <;> omega
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hle
    have : (2 : Nat) ^ 20 = 1048576 := by norm_num
    omega
  have hCS : ∀ k0 < rcnt (LR 0), CS k0 =
      (∑ k1 ∈ Finset.range (rcnt (LR 1)), ∑ k2 ∈ Finset.range (rcnt (LR 2)),
        if ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
          trK n (Nat.mul n w) LR TR 0 k0] m = true then 1 else 0) +
      1048576 * (∑ k1 ∈ Finset.range (rcnt (LR 1)), ∑ k2 ∈ Finset.range (rcnt (LR 2)),
        if (ordB0 w bs [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
          trK n (Nat.mul n w) LR TR 0 k0] m && cnt3.condsK w bs XP
            [trK n (Nat.mul n w) LR TR 2 k2, trK n (Nat.mul n w) LR TR 1 k1,
              trK n (Nat.mul n w) LR TR 0 k0] conds) = true then 1 else 0) := by
    intro k0 hk0
    rw [← h k0 hk0, Cnt3P.cnt3_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k2 _ => Cnt3P.vv_split _ _ _ _ _ _ _ _ _ _ _
  rw [Cnt3P.countW_blocks, Cnt3P.countW_blocks, sumN_eq, sumN_eq, Tab.lsum, Tab.lsum,
    hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num)]
  constructor
  · refine Finset.sum_congr rfl fun k0 hk0 => ?_
    rw [Finset.mem_range] at hk0
    change _ = CS k0 % 1048576
    rw [hCS k0 hk0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hA k0 hk0)]
    refine Finset.sum_congr rfl fun k1 hk1 => Finset.sum_congr rfl fun k2 hk2 => ?_
    rw [Finset.mem_range] at hk1 hk2
    rw [Cnt3P.ordB_ag (Cnt3P.word_ag hb hp hl hk0 hk1 hk2) hbsl,
      ← Cnt3P.ordB0_eq (hK hk0 hk1 hk2) hbsl]
  · refine Finset.sum_congr rfl fun k0 hk0 => ?_
    rw [Finset.mem_range] at hk0
    change _ = CS k0 / 1048576
    rw [hCS k0 hk0]
    have hA0 := hA k0 hk0
    have hdiv : ∀ a b : Nat, a < 1048576 → (a + 1048576 * b) / 1048576 = b := fun a b ha => by
      omega
    rw [hdiv _ _ hA0]
    refine Finset.sum_congr rfl fun k1 hk1 => Finset.sum_congr rfl fun k2 hk2 => ?_
    rw [Finset.mem_range] at hk1 hk2
    have hw := Cnt3P.word_ag hb hp hl hk0 hk1 hk2
    rw [Cnt3P.ordB_ag hw hbsl, ← Cnt3P.ordB0_eq (hK hk0 hk1 hk2) hbsl,
      Cnt3P.condsOK_ag (Cnt3P.rangeL_ag hXr) hw hbsl,
      ← Cnt3P.condsK_eq hXr (hK hk0 hk1 hk2) hbsl]

end CFSG.KS.SporSch

end
