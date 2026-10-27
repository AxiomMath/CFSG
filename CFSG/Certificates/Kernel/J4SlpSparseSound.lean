module

public import Certificates.Data.Kernel.J4SlpSparse
public import CFSG.Certificates.Kernel.SporSch.J4S11Sound

public section

namespace CFSG.KC.J4Sp

open CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ

@[expose] def SpOK (n : Nat) (R : Array Pair) (L : List Ent) (b : Nat) : Prop :=
  R.size = n ∧ ∀ e ∈ L, e.1 < b ∧ e.1 < n ∧ PairOK R[e.1]! e.2.1 e.2.2

theorem pullS_cons (r : Nat) (e : Ent) (L : List Ent) (k : Ent → List Ent → Option (List Ent)) :
    pullS r (e :: L) k = Bool.rec (motive := fun _ => Option (List Ent))
      (pullS r L fun f L' => k f (e :: L')) (k e L) (Nat.beq e.1 r) := rfl

theorem pullS_some (r : Nat) : ∀ (L : List Ent) (k : Ent → List Ent → Option (List Ent))
    (out : List Ent), pullS r L k = some out →
    ∃ e L', e ∈ L ∧ e.1 = r ∧ (∀ x ∈ L', x ∈ L) ∧ k e L' = some out
  | [], _, _, h => by cases h
  | e :: L, k, out, h => by
    rw [pullS_cons] at h
    cases hb : Nat.beq e.1 r
    · rw [hb] at h
      obtain ⟨f, L', hf, hr, hL', hk⟩ := pullS_some r L _ out h
      refine ⟨f, e :: L', List.mem_cons_of_mem _ hf, hr, fun x hx => ?_, hk⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hL' x hx)
    · rw [hb] at h
      exact ⟨e, L, List.mem_cons_self, Nat.eq_of_beq_eq_true hb,
        fun x hx => List.mem_cons_of_mem _ hx, h⟩

theorem strictO_eq (y : Nat) (k : Nat → Option (List Ent)) : strictO y k = k y := by
  cases y <;> rfl

theorem pushS_some {n b0 r a b : Nat} {L : List Ent} {k : List Ent → Nat → Option (List Ent)}
    {out : List Ent} (h : pushS n b0 r a b L k = some out) :
    b0 ≤ r ∧ r < n ∧ k ((r, a, b) :: L) (r + 1) = some out := by
  unfold pushS at h
  cases h1 : Nat.ble b0 r <;> cases h2 : Nat.blt r n <;> rw [h1, h2] at h
  · cases h
  · cases h
  · cases h
  · rw [strictO_eq, strictO_eq] at h
    exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, h⟩

theorem SpOK.mono {n : Nat} {R : Array Pair} {L L' : List Ent} {b : Nat} (hR : SpOK n R L b)
    (h : ∀ x ∈ L', x ∈ L) : SpOK n R L' b :=
  ⟨hR.1, fun e he => hR.2 e (h e he)⟩

theorem SpOK.cons {n : Nat} {R : Array Pair} {L L' : List Ent} {b : Nat} (hR : SpOK n R L b)
    {e : Ent} (he : e ∈ L) (h : ∀ x ∈ L', x ∈ L) : SpOK n R (e :: L') b :=
  hR.mono fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact he
    · exact h x hx

theorem SpOK.push {n : Nat} {R : Array Pair} {L : List Ent} {b : Nat} (hR : SpOK n R L b)
    {r : Nat} (hb : b ≤ r) (hn : r < n) {P : Pair} {x y : Nat} (hP : PairOK P x y) :
    SpOK n (R.setIfInBounds r P) ((r, x, y) :: L) (r + 1) := by
  obtain ⟨hs, hL⟩ := hR
  refine ⟨by rw [Array.size_setIfInBounds, hs], fun e he => ?_⟩
  rcases List.mem_cons.1 he with rfl | he
  · refine ⟨Nat.lt_succ_self _, hn, ?_⟩
    rw [getElem!_setIfInBounds_of_lt' (by rw [hs]; exact hn), if_pos rfl]
    exact hP
  · obtain ⟨h1, h2, h3⟩ := hL e he
    refine ⟨by omega, h2, ?_⟩
    rw [getElem!_setIfInBounds_of_lt' (by rw [hs]; exact h2), if_neg (by omega)]
    exact h3

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

theorem stepS_ok {n : Nat} {R : Array Pair} {L : List Ent} {b : Nat} (hR : SpOK n R L b)
    (ins : Instr) {k : List Ent → Nat → Option (List Ent)} {out : List Ent}
    (h : stepS c rm one n ins L b k = some out) :
    ∃ L' b', SpOK n (Instr.runN O R ins) L' b' ∧ k L' b' = some out := by
  have pr : ∀ {e : Ent}, e ∈ L → PairOK R[e.1]! e.2.1 e.2.2 := fun he => (hR.2 _ he).2.2
  cases ins with
  | mu i j r =>
    change pullS i L (fun ei L1 => pullS j (ei :: L1) fun ej L2 =>
      pushS n b r (mulJ c rm ei.2.1 ej.2.1) (mulJ c rm ej.2.2 ei.2.2) (ej :: L2) k) = some out at h
    obtain ⟨ei, L1, hei, hi, hL1, h⟩ := pullS_some i L _ out h
    obtain ⟨ej, L2, hej, hj, hL2, h⟩ := pullS_some j (ei :: L1) _ out h
    obtain ⟨hb, hn, h⟩ := pushS_some h
    have hej' : ej ∈ L := by
      rcases List.mem_cons.1 hej with rfl | hej
      · exact hei
      · exact hL1 _ hej
    have hsub : ∀ x ∈ L2, x ∈ L := fun x hx => by
      rcases List.mem_cons.1 (hL2 x hx) with rfl | hx'
      · exact hei
      · exact hL1 _ hx'
    have hR2 : SpOK n R (ej :: L2) b := hR.cons hej' hsub
    have hPi := pr hei
    have hPj := pr hej'
    rw [hi] at hPi
    rw [hj] at hPj
    exact ⟨_, _, hR2.push hb hn (mulP_ok hK hPi hPj), h⟩
  | iv i r =>
    change pullS i L (fun ei L1 => pushS n b r ei.2.2 ei.2.1 (ei :: L1) k) = some out at h
    obtain ⟨ei, L1, hei, hi, hL1, h⟩ := pullS_some i L _ out h
    obtain ⟨hb, hn, h⟩ := pushS_some h
    have hPi := pr hei
    rw [hi] at hPi
    exact ⟨_, _, (hR.cons hei hL1).push hb hn (invP_ok hPi), h⟩
  | pwr e i r =>
    change pullS i L (fun ei L1 => pushS n b r (powJ c rm one ei.2.1 e) (powJ c rm one ei.2.2 e)
      (ei :: L1) k) = some out at h
    obtain ⟨ei, L1, hei, hi, hL1, h⟩ := pullS_some i L _ out h
    obtain ⟨hb, hn, h⟩ := pushS_some h
    have hPi := pr hei
    rw [hi] at hPi
    exact ⟨_, _, (hR.cons hei hL1).push hb hn (powP_ok hK hPi e), h⟩

theorem runS_ok {n : Nat} : ∀ (prog : List Instr) {R : Array Pair} {L : List Ent} {b : Nat}
    {out : List Ent}, SpOK n R L b → runS c rm one n prog L b = some out →
    ∃ b', SpOK n (runProgN O R prog) out b'
  | [], _, _, b, _, hR, h => by
    cases h
    exact ⟨b, hR⟩
  | ins :: prog, R, L, b, out, hR, h => by
    change stepS c rm one n ins L b (fun L b => runS c rm one n prog L b) = some out at h
    obtain ⟨L', b', hR', h'⟩ := stepS_ok hK hR ins h
    exact runS_ok prog hR' h'

theorem slpS_ok {n K B : Nat} {prog : List Instr} {R : Array Pair} {L : List Ent} {b : Nat}
    (hR : SpOK n R L b) (h : slpS c rm one n K B prog L b = true) :
    ∃ y, PairOK (runProgN O R prog)[K]! B y := by
  unfold slpS at h
  cases hr : runS c rm one n prog L b with
  | none => rw [hr] at h; cases h
  | some L' =>
    rw [hr] at h
    change Option.rec (motive := fun _ => Bool) false (headB B) (getS K L') = true at h
    obtain ⟨b', hR'⟩ := runS_ok hK prog hR hr
    cases hg : getS K L' with
    | none => rw [hg] at h; cases h
    | some l =>
      rw [hg] at h
      obtain ⟨e, _, he, hk, _, hl⟩ := pullS_some K L' _ l hg
      cases hl
      have hB : e.2.1 = B := Nat.eq_of_beq_eq_true h
      have hP := (hR'.2 e he).2.2
      rw [hk, hB] at hP
      exact ⟨_, hP⟩

omit hK in
theorem init_ok {n : Nat} (hn : 3 ≤ n) {X Y : Pair} {x1 x2 y1 y2 : Nat} (hX : PairOK X x1 x2)
    (hY : PairOK Y y1 y2) : SpOK n (initRegsN O n X Y) [(1, x1, x2), (2, y1, y2)] 3 := by
  have hs : (initRegsN O n X Y).size = n := by simp [initRegsN]
  refine ⟨hs, fun e he => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · refine ⟨by omega, by omega, ?_⟩
    rw [getElem!_pos _ 1 (by rw [hs]; omega)]
    simpa [initRegsN] using hX
  · refine ⟨by omega, by omega, ?_⟩
    rw [getElem!_pos _ 2 (by rw [hs]; omega)]
    simpa [initRegsN] using hY

theorem slpS_sound {n K B Bi : Nat} (hn : 3 ≤ n) {X Y P : Pair} {x1 x2 y1 y2 : Nat}
    (hX : PairOK X x1 x2) (hY : PairOK Y y1 y2) (hP : PairOK P B Bi) {prog : List Instr}
    (h : slpS c rm one n K B prog [(1, x1, x2), (2, y1, y2)] 3 = true) :
    O.eq ((runProgN O (initRegsN O n X Y) prog)[K]!).1 P.1 = true := by
  obtain ⟨_, hQ⟩ := slpS_ok hK (init_ok hn hX hY) h
  have e := enc_inj hQ.1.1 hP.1.1 (by rw [hQ.1.2, hP.1.2])
  change (_ == _) = true
  rw [e]
  exact beq_self_eq_true _

theorem slpT_sound {n K B Bi : Nat} (hn : 3 ≤ n) {X Y P : Pair} {x1 x2 y1 y2 : Nat}
    (hX : PairOK X x1 x2) (hY : PairOK Y y1 y2) (hP : PairOK P B Bi) {cs : List Char}
    (h : slpT c rm one n K B cs x1 x2 y1 y2 = true) :
    ((parseSLP (String.ofList cs)).getD []).all (Instr.lt n) = true ∧
      O.eq ((runProgN O (initRegsN O n X Y) ((parseSLP (String.ofList cs)).getD []))[K]!).1
        P.1 = true := by
  unfold slpT at h
  cases hp : CFSG.KS.SporSch.J4E.parseK cs with
  | none => rw [hp] at h; cases h
  | some codes =>
    rw [hp] at h
    change andB _ _ = true at h
    have hab := h
    unfold andB at hab
    cases ha : (codes.map CFSG.KS.SporSch.J4E.decodeK).all (Instr.lt n) <;> rw [ha] at hab
    · cases hab
    obtain ⟨p, hp1, hp2⟩ := Option.map_eq_some_iff.1 (CFSG.KS.SporSch.J4E.parseK_sound hp)
    have e : codes.map CFSG.KS.SporSch.J4E.decodeK = p := by
      rw [← hp2, List.map_map]
      simp only [Function.comp_def, CFSG.KS.SporSch.J4E.decodeK_code, List.map_id']
    rw [hp1, Option.getD_some, ← e]
    exact ⟨ha, slpS_sound hK hn hX hY hP hab⟩

end CFSG.KC.J4Sp

end
