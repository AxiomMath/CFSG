module

public import CFSG.Certificates.Kernel.Census.ToMain
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Monster.B.Co2.Native

theorem allRange_zero (f : Nat → Bool) : ∀ i < 0, f i = true := fun _ h => absurd h (by omega)

theorem allRange_extend {f : Nat → Bool} {a len : Nat} (h : ∀ i < a, f i = true)
    (hb : (List.range' a len).all f = true) : ∀ i < a + len, f i = true := by
  intro i hi
  rcases Nat.lt_or_ge i a with h1 | h1
  · exact h i h1
  · exact List.all_eq_true.1 hb i (List.mem_range'_1.2 ⟨h1, hi⟩)

theorem ppointsOK_split {n w : Nat} {gs : Array Nat} {c : ArrCertP} (B : Nat) :
    ∀ (i : Nat) (us : List Nat) (es : List (Array Nat)) (ps ls : List Nat),
      ppointsOK n w gs c i us es ps ls = (ppointsOK n w gs c i (us.take B) es ps ls &&
        ppointsOK n w gs c (i + B) (us.drop B) (es.drop B) (ps.drop B) (ls.drop B)) := by
  have hd : ∀ {α : Type} (B : Nat) (l : List α), l.drop (B + 1) = l.tail.drop B := by
    intro α B l
    cases l <;> simp
  induction B with
  | zero =>
    intro i us es ps ls
    simp [ppointsOK]
  | succ B ih =>
    intro i us es ps ls
    cases us with
    | nil => simp [ppointsOK]
    | cons u us =>
      have hi : i + (B + 1) = i + 1 + B := by omega
      simp only [List.take_succ_cons, List.drop_succ_cons, ppointsOK]
      rw [ih (i + 1) us es.tail ps.tail ls.tail, hd B es, hd B ps, hd B ls, hi, Bool.and_assoc]

theorem ppointsOK_chunk {n w : Nat} {gs : Array Nat} {c : ArrCertP} {a B : Nat} {us : List Nat}
    {es : List (Array Nat)} {ps ls : List Nat}
    (h1 : ppointsOK n w gs c a ((us.drop a).take B) (es.drop a) (ps.drop a) (ls.drop a) = true)
    (h2 : ppointsOK n w gs c (a + B) (us.drop (a + B)) (es.drop (a + B)) (ps.drop (a + B))
      (ls.drop (a + B)) = true) :
    ppointsOK n w gs c a (us.drop a) (es.drop a) (ps.drop a) (ls.drop a) = true := by
  rw [ppointsOK_split B, h1, Bool.true_and]
  simpa [List.drop_drop, Nat.add_comm] using h2

@[expose] noncomputable def pwordOK (n w : Nat) (gens : Array Nat) (x : Nat) (wd : List Nat) :
    Bool :=
  wd.all (fun i => Nat.blt i gens.size) && Nat.beq x (pprod n w (wd.map fun i => gens[i]!))

@[expose] noncomputable def pwordsWalk (n w : Nat) (gens : Array Nat) :
    List Nat → List (List Nat) → Bool
  | [], _ => true
  | x :: xs, ws => pwordOK n w gens x (ws.headD []) && pwordsWalk n w gens xs ws.tail

theorem pwordsWalk_spec {n w : Nat} {gens : Array Nat} :
    ∀ (xs : List Nat) (ws : List (List Nat)), pwordsWalk n w gens xs ws = true →
      ∀ k (hk : k < xs.length), pwordOK n w gens xs[k] (ws.getD k []) = true := by
  intro xs
  induction xs with
  | nil => intro ws _ k hk; exact absurd hk (by simp)
  | cons x xs ih =>
    intro ws h k hk
    simp only [pwordsWalk, Bool.and_eq_true] at h
    cases k with
    | zero => cases ws <;> simpa using h.1
    | succ k =>
      have := ih ws.tail h.2 k (by simpa using hk)
      cases ws <;> simpa using this

theorem pwordsWalk_split {n w : Nat} {gens : Array Nat} (B : Nat) :
    ∀ (xs : List Nat) (ws : List (List Nat)), pwordsWalk n w gens xs ws =
      (pwordsWalk n w gens (xs.take B) ws && pwordsWalk n w gens (xs.drop B) (ws.drop B)) := by
  induction B with
  | zero => intro xs ws; simp [pwordsWalk]
  | succ B ih =>
    intro xs ws
    cases xs with
    | nil => simp [pwordsWalk]
    | cons x xs =>
      have hd : ws.drop (B + 1) = ws.tail.drop B := by cases ws <;> simp
      simp only [List.take_succ_cons, List.drop_succ_cons, pwordsWalk]
      rw [ih xs ws.tail, hd, Bool.and_assoc]

theorem pwordsWalk_chunk {n w : Nat} {gens : Array Nat} {a B : Nat} {xs : List Nat}
    {ws : List (List Nat)} (h1 : pwordsWalk n w gens ((xs.drop a).take B) (ws.drop a) = true)
    (h2 : pwordsWalk n w gens (xs.drop (a + B)) (ws.drop (a + B)) = true) :
    pwordsWalk n w gens (xs.drop a) (ws.drop a) = true := by
  rw [pwordsWalk_split B, h1, Bool.true_and]
  simpa [List.drop_drop, Nat.add_comm] using h2

theorem pxsOK_of_walk {n w : Nat} {gens xs : Array Nat} {ws : List (List Nat)}
    (h : pwordsWalk n w gens xs.toList ws = true) : pxsOK n w gens xs ws = true := by
  unfold pxsOK
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' : k < xs.size := List.mem_range.1 hk
  have := pwordsWalk_spec _ _ h k (by simpa using hk')
  rw [getElem!_pos xs k hk']
  simpa [pwordOK] using this

private theorem pg_big {n w p k : Nat} (hp : canon1 n w p = true) (hk : n ≤ k) :
    pg w (CFSG.KS.mask w) p k = 0 := by
  have h0 : p >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hp
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h0
  have hlt : p < 2 ^ (n * w) := by
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · exact h0
  apply Nat.eq_of_testBit_eq
  intro j
  rw [CFSG.KS.PackFld.testBit_pgM, Nat.zero_testBit]
  have hle : n * w ≤ w * k + j := by
    have := Nat.mul_le_mul_right w hk
    rw [Nat.mul_comm k w] at this
    omega
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hle)),
    Bool.and_false]

private theorem unpackP_get! {n w p i : Nat} (hi : i < n) :
    (unpackP n w p)[i]! = pg w (CFSG.KS.mask w) p i := by
  rw [getElem!_pos _ _ (by simp [unpackP]; exact hi)]
  unfold unpackP
  rw [Array.getElem_ofFn]

theorem unpackP_pc {n w p q : Nat} (hn : n < 2 ^ 32) (_hw : n ≤ 2 ^ w)
    (hp : canon1 n w p = true) :
    unpackP n w (pc n w p q) = compA n (unpackP n w p) (unpackP n w q) := by
  apply Array.ext
  · simp [unpackP, compA]
  · intro i h1 _
    have hi : i < n := by simpa [unpackP] using h1
    simp only [compA, Array.getElem_ofFn]
    rw [unpackP_get! hi]
    have hL : (unpackP n w (pc n w p q))[i] =
        pg w (CFSG.KS.mask w) p (pg w (CFSG.KS.mask w) q i) := by
      simp only [unpackP, pc, Array.getElem_ofFn]
      exact CFSG.KS.PackFld.pg_pcomp hn hi
    rw [hL]
    by_cases hk : pg w (CFSG.KS.mask w) q i < n
    · rw [unpackP_get! hk]
    · rw [getElem!_neg _ _ (by simp only [unpackP, Array.size_ofFn]; exact hk),
        pg_big hp (by omega)]
      rfl

private theorem lt_of_canon {n w p : Nat} (hp : canon1 n w p = true) : p < 2 ^ (n * w) := by
  have h0 : p >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hp
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  · exact h0

private theorem eq_of_pg {n w p q : Nat} (hp : canon1 n w p = true) (hq : canon1 n w q = true)
    (h : ∀ i < n, pg w (CFSG.KS.mask w) p i = pg w (CFSG.KS.mask w) q i) : p = q := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < n * w
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, Nat.mul_zero] at hb
        omega
      · exact h0
    have hi : b / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw]
      exact hb
    have hd := Nat.div_add_mod b w
    have hm : b % w < w := Nat.mod_lt _ hw
    have e := congrArg (fun x => x.testBit (b % w)) (h _ hi)
    rw [CFSG.KS.PackFld.testBit_pgM, CFSG.KS.PackFld.testBit_pgM, hd] at e
    simpa [hm] using e
  · have hle : n * w ≤ b := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_of_canon hp) (Nat.pow_le_pow_right
      (by omega) hle)), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt_of_canon hq)
      (Nat.pow_le_pow_right (by omega) hle))]

private theorem eqA_unpackP' {n w p q : Nat} (hp : canon1 n w p = true)
    (hq : canon1 n w q = true) : eqA n (unpackP n w p) (unpackP n w q) = Nat.beq p q := by
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq]
  unfold eqA allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h
    refine eq_of_pg hp hq (fun i hi => ?_)
    have := h ⟨i, hi⟩ (List.mem_finRange _)
    rw [beq_iff_eq, unpackP_get! hi, unpackP_get! hi] at this
    exact this
  · intro h i _
    rw [h]
    exact beq_self_eq_true _

theorem pinXL_eq {n w P : Nat} {xs : Array Nat} (hP : canon1 n w P = true)
    (hxs : xs.toList.all (canon1 n w) = true) :
    pinXL xs P = inXL n (xs.map (unpackP n w)) (unpackP n w P) := by
  unfold pinXL CFSG.ComponentClassification.RankTwoSporadic.Cert.inXL
  rw [Array.toList_map, List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  have hc : ∀ x ∈ xs.toList, canon1 n w x = true := List.all_eq_true.mp hxs
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rw [Function.comp_apply, eqA_unpackP' hP (hc x hx)]; exact h⟩
  · rintro ⟨x, hx, h⟩
    rw [Function.comp_apply, eqA_unpackP' hP (hc x hx)] at h
    exact ⟨x, hx, h⟩

end CFSG.KC.Census
