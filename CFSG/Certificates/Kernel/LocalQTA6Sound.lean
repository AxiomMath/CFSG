module

public import Certificates.Data.Kernel.LocalQT.A6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSA6Inputs
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.LocalQTBfsKSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KC.LQT.A6

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.QuasithinUnique.Id2519.UHS
open CFSG.KS CFSG.KS.Raw

@[expose] def letterArrG (g0 g1 g1i : Array ℕ) (l : ℕ) : Array ℕ :=
  if l = 0 then g0 else if l = 1 then g1 else g1i

@[expose] def wArrG (g0 g1 g1i : Array ℕ) (ws : List ℕ) : List (Array ℕ) :=
  (ws.map (letterArrG g0 g1 g1i)).reverse

@[expose] def nodeWordFuelG (par lab : Array ℕ) (y1 y2 : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, k =>
    if k = 0 then [] else
      nodeWordFuelG par lab y1 y2 fuel par[k]! ++ (if lab[k]! = 0 then y1 else y2)

@[expose] def a6CheckG (g0 g1 g1i : Array ℕ) (y1 y2 c : List ℕ) (par lab : Array ℕ)
    (nw : ℕ → List ℕ) (cw : Array (List ℕ)) : Bool :=
  ordB PairHS.bs (wArrG g0 g1 g1i y1) 3 && ordB PairHS.bs (wArrG g0 g1 g1i y2) 5 &&
  (baseImgs PairHS.bs (wArrG g0 g1 g1i (y1 ++ c)) ==
    baseImgs PairHS.bs (wArrG g0 g1 g1i (c ++ y1))) &&
  (baseImgs PairHS.bs (wArrG g0 g1 g1i (y2 ++ c)) ==
    baseImgs PairHS.bs (wArrG g0 g1 g1i (c ++ y2))) &&
  decide (par.size = 360) && decide (lab.size = 360) &&
  strictInc ((List.range 360).map fun k =>
    imgKey 3850 (baseImgs PairHS.bs (wArrG g0 g1 g1i (nw k)))).mergeSort &&
  (List.range 360).all fun k =>
    !ordB PairHS.bs (wArrG g0 g1 g1i (nw k)) 2 ||
      (baseImgs PairHS.bs (wArrG g0 g1 g1i (cw[k]! ++ c)) ==
        baseImgs PairHS.bs (wArrG g0 g1 g1i (c ++ nw k ++ cw[k]!)))

theorem a6Check_eq : a6Check = a6CheckG PairHS.gens[0]! PairHS.gens[1]! PairHS.gensInv[1]!
    y1Letters y2Letters cLetters nodePar nodeLab nodeWord conjWords := rfl

theorem nodeWord_eq (k : ℕ) :
    nodeWord k = nodeWordFuelG nodePar nodeLab y1Letters y2Letters 360 k := by
  suffices h : ∀ f k, nodeWordFuel f k = nodeWordFuelG nodePar nodeLab y1Letters y2Letters f k from
    h 360 k
  intro f
  induction f with
  | zero => intro k; rfl
  | succ f ih =>
    intro k
    rw [nodeWordFuel, nodeWordFuelG, ih]

section Proof

open CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PackFld

private theorem beq_false' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem mask12 : mask 12 = 4095 := rfl

private theorem unpack_get' {n w P i : ℕ} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  simp [unpack, hi]

private theorem lt_of_canon {P : ℕ} (h : CFSG.KS.Prim.canonK 3850 12 4095 46200 P = true) :
    ∀ q < 3850, pg 12 4095 P q < 3850 := by
  have h1 := range_of_canonK (n := 3850) (w := 12) (G := P) h
  intro q hq
  have h2 := CFSG.KS.allN_spec h1 q hq
  rw [mask12] at h2
  simpa [Nat.blt_eq] using h2

private theorem evR_snoc (u : List (Array ℕ)) (t : Array ℕ) (p : ℕ) :
    evR (u ++ [t]) p = t[evR u p]! := by
  simp [evR, List.foldl_append]

private theorem wArrG_cons (g0 g1 g1i : Array ℕ) (l : ℕ) (w : List ℕ) :
    wArrG g0 g1 g1i (l :: w) = wArrG g0 g1 g1i w ++ [letterArrG g0 g1 g1i l] := by
  simp [wArrG]

private theorem evWK_append (P0 P1 Q1 : ℕ) : ∀ (a b : List ℕ) (p : ℕ),
    evWK P0 P1 Q1 (a ++ b) p = evWK P0 P1 Q1 a (evWK P0 P1 Q1 b p)
  | [], b, p => rfl
  | l :: a, b, p => by
    change strictN (evWK P0 P1 Q1 (a ++ b) p) (imgA P0 P1 Q1 l) =
      strictN (evWK P0 P1 Q1 a (evWK P0 P1 Q1 b p)) (imgA P0 P1 Q1 l)
    rw [evWK_append P0 P1 Q1 a b p]

private def Good (P0 P1 Q1 : ℕ) : Prop :=
  (∀ q < 3850, pg 12 4095 P0 q < 3850) ∧ (∀ q < 3850, pg 12 4095 P1 q < 3850) ∧
    ∀ q < 3850, pg 12 4095 Q1 q < 3850

private theorem imgA_lt {P0 P1 Q1 : ℕ} (hg : Good P0 P1 Q1) (l : ℕ) {p : ℕ} (hp : p < 3850) :
    imgA P0 P1 Q1 l p < 3850 := by
  unfold imgA
  by_cases hl0 : l = 0
  · subst hl0
    exact hg.1 p hp
  · by_cases hl1 : l = 1
    · subst hl1
      exact hg.2.1 p hp
    · rw [beq_false' hl0, beq_false' hl1]
      exact hg.2.2 p hp

private theorem imgA_zero (P0 P1 Q1 p : ℕ) : imgA P0 P1 Q1 0 p = pg 12 4095 P0 p := rfl

private theorem imgA_one (P0 P1 Q1 p : ℕ) : imgA P0 P1 Q1 1 p = pg 12 4095 P1 p := rfl

private theorem imgA_other {P0 P1 Q1 : ℕ} {l : ℕ} (h0 : l ≠ 0) (h1 : l ≠ 1) (p : ℕ) :
    imgA P0 P1 Q1 l p = pg 12 4095 Q1 p := by
  unfold imgA
  rw [beq_false' h0, beq_false' h1]

private theorem imgA_get {P0 P1 Q1 : ℕ} {g0 g1 g1i : Array ℕ} (h0 : g0 = unpack 3850 12 P0)
    (h1 : g1 = unpack 3850 12 P1) (h2 : g1i = unpack 3850 12 Q1) (l : ℕ) {p : ℕ}
    (hp : p < 3850) : imgA P0 P1 Q1 l p = (letterArrG g0 g1 g1i l)[p]! := by
  by_cases hl0 : l = 0
  · subst hl0
    have e : letterArrG g0 g1 g1i 0 = g0 := by simp [letterArrG]
    rw [e, h0, imgA_zero, unpack_get' hp, mask12]
  · by_cases hl1 : l = 1
    · subst hl1
      have e : letterArrG g0 g1 g1i 1 = g1 := by simp [letterArrG]
      rw [e, h1, imgA_one, unpack_get' hp, mask12]
    · have e : letterArrG g0 g1 g1i l = g1i := by simp [letterArrG, hl0, hl1]
      rw [e, h2, imgA_other hl0 hl1, unpack_get' hp, mask12]

private theorem evWK_lt {P0 P1 Q1 : ℕ} (hg : Good P0 P1 Q1) : ∀ (w : List ℕ) {p : ℕ},
    p < 3850 → evWK P0 P1 Q1 w p < 3850
  | [], _, hp => hp
  | l :: w, p, hp => by
    change strictN (evWK P0 P1 Q1 w p) (imgA P0 P1 Q1 l) < 3850
    rw [strictN_eqP]
    exact imgA_lt hg l (evWK_lt hg w hp)

private theorem evWK_eq {P0 P1 Q1 : ℕ} (hg : Good P0 P1 Q1) {g0 g1 g1i : Array ℕ}
    (h0 : g0 = unpack 3850 12 P0) (h1 : g1 = unpack 3850 12 P1) (h2 : g1i = unpack 3850 12 Q1) :
    ∀ (w : List ℕ) {p : ℕ}, p < 3850 → evWK P0 P1 Q1 w p = evR (wArrG g0 g1 g1i w) p
  | [], p, _ => rfl
  | l :: w, p, hp => by
    have ih := evWK_eq hg h0 h1 h2 w hp
    have hlt := evWK_lt hg w hp
    change strictN (evWK P0 P1 Q1 w p) (imgA P0 P1 Q1 l) = _
    rw [strictN_eqP, wArrG_cons, evR_snoc, ← ih, imgA_get h0 h1 h2 l hlt]

private theorem evR_lt {P0 P1 Q1 : ℕ} (hg : Good P0 P1 Q1) {g0 g1 g1i : Array ℕ}
    (h0 : g0 = unpack 3850 12 P0) (h1 : g1 = unpack 3850 12 P1) (h2 : g1i = unpack 3850 12 Q1)
    (w : List ℕ) {p : ℕ} (hp : p < 3850) : evR (wArrG g0 g1 g1i w) p < 3850 := by
  rw [← evWK_eq hg h0 h1 h2 w hp]
  exact evWK_lt hg w hp

private theorem powK_eq' {W : List (Array ℕ)} {f : ℕ → ℕ} (hf : ∀ p < 3850, f p = evR W p)
    (hW : ∀ p < 3850, evR W p < 3850) :
    ∀ (e : ℕ), ∀ p < 3850, powK f e p = evPow W e p ∧ evPow W e p < 3850
  | 0, p, hp => ⟨rfl, hp⟩
  | e + 1, p, hp => by
    obtain ⟨ih1, ih2⟩ := powK_eq' hf hW e p hp
    change strictN (powK f e p) f = evR W (evPow W e p) ∧ evR W (evPow W e p) < 3850
    rw [strictN_eqP, ih1, hf _ ih2]
    exact ⟨rfl, hW _ ih2⟩

private theorem fixK_iff {f : ℕ → ℕ} : fixK f = true ↔ ∀ b < 4, f b = b := by
  unfold fixK
  constructor
  · intro h b hb
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h b hb)
  · intro h
    exact allN_of_forall fun b hb => by rw [h b hb]; exact Nat.beq_refl b

private theorem fixB_iff {W : List (Array ℕ)} {e : ℕ} :
    fixB PairHS.bs W e = true ↔ ∀ b < 4, evPow W e b = b := by
  simp only [fixB, PairHS.bs, List.all_cons, List.all_nil, Bool.and_eq_true, beq_iff_eq, and_true]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ b hb
    interval_cases b <;> assumption
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)⟩

private theorem fixK_powK {f : ℕ → ℕ} {W : List (Array ℕ)} (hf : ∀ p < 3850, f p = evR W p)
    (hW : ∀ p < 3850, evR W p < 3850) (e : ℕ) : fixK (powK f e) = fixB PairHS.bs W e := by
  rw [Bool.eq_iff_iff, fixK_iff, fixB_iff]
  constructor <;> intro h b hb
  · rw [← (powK_eq' hf hW e b (by omega)).1]
    exact h b hb
  · rw [(powK_eq' hf hW e b (by omega)).1]
    exact h b hb

private theorem ordPK_eq {f : ℕ → ℕ} {W : List (Array ℕ)} (hf : ∀ p < 3850, f p = evR W p)
    (hW : ∀ p < 3850, evR W p < 3850) {m : ℕ}
    (hm : CFSG.Sporadic.Schreier.Native.divParts m = [1]) :
    ordPK f m = ordB PairHS.bs W m := by
  have e1 : fixK f = fixB PairHS.bs W 1 := by
    have h1 : powK f 1 = f := funext fun p => strictN_eqP p f
    have := fixK_powK hf hW 1
    rwa [h1] at this
  unfold ordPK ordB
  rw [fixK_powK hf hW m, e1, hm]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  cases fixB PairHS.bs W m <;> cases fixB PairHS.bs W 1 <;> rfl

private theorem div3 : CFSG.Sporadic.Schreier.Native.divParts 3 = [1] := by decide
private theorem div5 : CFSG.Sporadic.Schreier.Native.divParts 5 = [1] := by decide
private theorem div2 : CFSG.Sporadic.Schreier.Native.divParts 2 = [1] := by decide

private theorem arrGetN (par : Array ℕ) (k : ℕ) : par[k]! = par.toList.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases par[k]? <;> rfl

private theorem arrGetW (cw : Array (List ℕ)) (k : ℕ) : cw[k]! = cw.toList.getD k [] := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases cw[k]? <;> rfl

private theorem getK_cons (x : ℕ) (l : List ℕ) (j : ℕ) :
    CFSG.KC.LQT.S.getK (x :: l) j =
      Bool.rec (CFSG.KC.LQT.S.getK l (Nat.sub j 1)) x (Nat.beq j 0) := rfl

private theorem getK_eq : ∀ (l : List ℕ) (i : ℕ), CFSG.KC.LQT.S.getK l i = l.getD i 0
  | [], i => by simp [CFSG.KC.LQT.S.getK]
  | x :: l, 0 => by simp [getK_cons]
  | x :: l, i + 1 => by
    rw [getK_cons, beq_false' (Nat.succ_ne_zero i)]
    change CFSG.KC.LQT.S.getK l i = _
    rw [getK_eq l i]
    simp

private theorem getW_cons (x : List ℕ) (l : List (List ℕ)) (j : ℕ) :
    getW (x :: l) j = Bool.rec (getW l (Nat.sub j 1)) x (Nat.beq j 0) := rfl

private theorem getW_eq : ∀ (l : List (List ℕ)) (i : ℕ), getW l i = l.getD i []
  | [], i => by simp [getW]
  | x :: l, 0 => by simp [getW_cons]
  | x :: l, i + 1 => by
    rw [getW_cons, beq_false' (Nat.succ_ne_zero i)]
    change getW l i = _
    rw [getW_eq l i]
    simp

private theorem recBool_eq (a : ℕ) (y1 y2 : List ℕ) :
    (Bool.rec y2 y1 (Nat.beq a 0) : List ℕ) = if a = 0 then y1 else y2 := by
  by_cases h : a = 0
  · subst h
    rfl
  · rw [beq_false' h, if_neg h]

private theorem evNodeK_succ (P0 P1 Q1 : ℕ) (y1 y2 par lab : List ℕ) (f k p : ℕ) :
    evNodeK P0 P1 Q1 y1 y2 par lab (f + 1) k p =
      Bool.rec (motive := fun _ => ℕ)
        (evNodeK P0 P1 Q1 y1 y2 par lab f (CFSG.KC.LQT.S.getK par k)
          (evWK P0 P1 Q1 (Bool.rec y2 y1 (Nat.beq (CFSG.KC.LQT.S.getK lab k) 0)) p)) p
        (Nat.beq k 0) := by
  change Bool.rec (motive := fun _ => ℕ)
    (strictN (evWK P0 P1 Q1 (Bool.rec y2 y1 (Nat.beq (CFSG.KC.LQT.S.getK lab k) 0)) p)
      (evNodeK P0 P1 Q1 y1 y2 par lab f (CFSG.KC.LQT.S.getK par k))) p (Nat.beq k 0) = _
  rw [strictN_eqP]

private theorem nodeWordFuelG_succ (par lab : Array ℕ) (y1 y2 : List ℕ) (f k : ℕ) (hk : k ≠ 0) :
    nodeWordFuelG par lab y1 y2 (f + 1) k =
      nodeWordFuelG par lab y1 y2 f par[k]! ++ (if lab[k]! = 0 then y1 else y2) := by
  rw [nodeWordFuelG, if_neg hk]

private theorem evNodeK_eq {P0 P1 Q1 : ℕ} (hg : Good P0 P1 Q1) (y1 y2 : List ℕ)
    (par lab : Array ℕ) : ∀ (fuel k p : ℕ), p < 3850 →
      evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList fuel k p =
        evWK P0 P1 Q1 (nodeWordFuelG par lab y1 y2 fuel k) p ∧
      evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList fuel k p < 3850
  | 0, k, p, hp => ⟨rfl, hp⟩
  | f + 1, k, p, hp => by
    by_cases hk : k = 0
    · subst hk
      refine ⟨?_, hp⟩
      rw [evNodeK_succ]
      simp [nodeWordFuelG]
      rfl
    · have hkb : Nat.beq k 0 = false := beq_false' hk
      have hs : evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList (f + 1) k p =
          evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList f par[k]!
            (evWK P0 P1 Q1 (if lab[k]! = 0 then y1 else y2) p) := by
        rw [evNodeK_succ, hkb, getK_eq, getK_eq, ← arrGetN par, ← arrGetN lab, ← recBool_eq]
      rw [hs, nodeWordFuelG_succ par lab y1 y2 f k hk, evWK_append]
      exact evNodeK_eq hg y1 y2 par lab f par[k]! _ (evWK_lt hg _ hp)

private theorem distinctK_spec (key : ℕ → ℕ) : ∀ (m : ℕ) (t : NT), OrdN t →
    distinctK key m t = true → (∀ i < m, ¬ memN t (key i)) ∧ ((List.range m).map key).Nodup
  | 0, t, _, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), List.nodup_nil⟩
  | k + 1, t, ht, h => by
    change strictB (key k) (fun x => Bool.rec (motive := fun _ => Bool)
      (distinctK key k (insT t x)) false (memT t x)) = true at h
    rw [strictB_eqP] at h
    cases hm : memT t (key k) with
    | true =>
      rw [hm] at h
      have h' : (false : Bool) = true := h
      exact absurd h' (by decide)
    | false =>
      rw [hm] at h
      change distinctK key k (insT t (key k)) = true at h
      obtain ⟨h1, h2⟩ := distinctK_spec key k (insT t (key k)) (ord_insT _ ht) h
      have hnm : ¬ memN t (key k) := fun hmem => by
        have := (memT_iff ht _).2 hmem
        rw [hm] at this
        exact absurd this (by decide)
      refine ⟨?_, ?_⟩
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | rfl
        · exact fun hmem => h1 i hik ((mem_insT _ _ t).2 (Or.inr hmem))
        · exact hnm
      · rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h2, List.nodup_singleton _, fun a ha b hb => ?_⟩
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
        rw [List.mem_singleton.1 hb]
        intro heq
        exact h1 i (List.mem_range.1 hi) ((mem_insT _ _ t).2 (Or.inl heq))

private theorem strictInc_of_pairwise' : ∀ {l : List ℕ}, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h1 := List.rel_of_pairwise_cons h List.mem_cons_self
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, strictInc_of_pairwise' (List.Pairwise.of_cons h)⟩

private theorem strictInc_mergeSort_of_nodup {l : List ℕ} (h : l.Nodup) :
    strictInc l.mergeSort = true := by
  have hM := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hn : l.mergeSort.Nodup := ((List.mergeSort_perm _ _).nodup_iff).2 h
  apply strictInc_of_pairwise'
  exact (hM.and hn).imp fun ⟨hab, hne⟩ => lt_of_le_of_ne (by simpa using hab) hne

private theorem eqB_iff {f g : ℕ → ℕ} : eqB f g = true ↔ ∀ b < 4, f b = g b := by
  unfold eqB
  constructor
  · intro h b hb
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h b hb)
  · intro h
    exact allN_of_forall fun b hb => by rw [h b hb]; exact Nat.beq_refl _

private theorem lenA_eq' {α : Type} : ∀ l : List α, lenA l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenA_eq' l)

private theorem baseImgs_beq {P0 P1 Q1 : ℕ} (hg : Good P0 P1 Q1) {g0 g1 g1i : Array ℕ}
    (h0 : g0 = unpack 3850 12 P0) (h1 : g1 = unpack 3850 12 P1) (h2 : g1i = unpack 3850 12 Q1)
    {W1 W2 : List ℕ} (hq : ∀ b < 4, evWK P0 P1 Q1 W1 b = evWK P0 P1 Q1 W2 b) :
    (baseImgs PairHS.bs (wArrG g0 g1 g1i W1) == baseImgs PairHS.bs (wArrG g0 g1 g1i W2)) =
      true := by
  rw [beq_iff_eq]
  have e : ∀ b < 4, evR (wArrG g0 g1 g1i W1) b = evR (wArrG g0 g1 g1i W2) b := fun b hb => by
    rw [← evWK_eq hg h0 h1 h2 W1 (by omega), ← evWK_eq hg h0 h1 h2 W2 (by omega)]
    exact hq b hb
  simp only [baseImgs, PairHS.bs, List.map_cons, List.map_nil]
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]

private theorem allBs_cons' (b : Bool) (l : List Bool) :
    CFSG.KC.LQT.S.allBs (b :: l) = CFSG.KC.Ord.andB b (CFSG.KC.LQT.S.allBs l) := rfl

private theorem allBs_nil' : CFSG.KC.LQT.S.allBs [] = true := rfl

private theorem a6Check_of_a6K {g0 g1 g1i : Array ℕ} {P0 P1 Q1 : ℕ} (h0 : g0 = unpack 3850 12 P0)
    (h1 : g1 = unpack 3850 12 P1) (h2 : g1i = unpack 3850 12 Q1) (y1 y2 c : List ℕ)
    (par lab : Array ℕ) (nw : ℕ → List ℕ) (cw : Array (List ℕ))
    (hnw : ∀ k, nw k = nodeWordFuelG par lab y1 y2 360 k)
    (h : a6K P0 P1 Q1 y1 y2 c par.toList lab.toList cw.toList = true) :
    a6CheckG g0 g1 g1i y1 y2 c par lab nw cw = true := by
  unfold a6K at h
  simp only [allBs_cons', allBs_nil', CFSG.KC.LQT.P.andB_iff, and_true] at h
  obtain ⟨hc0, hc1, hc2, ho1, ho2, he1, he2, hp, hl, hd, hn⟩ := h
  have hg : Good P0 P1 Q1 := ⟨lt_of_canon hc0, lt_of_canon hc1, lt_of_canon hc2⟩
  have hW : ∀ (w : List ℕ), ∀ p < 3850, evR (wArrG g0 g1 g1i w) p < 3850 :=
    fun w p hp => evR_lt hg h0 h1 h2 w hp
  have hE : ∀ (w : List ℕ) (p : ℕ), p < 3850 → evWK P0 P1 Q1 w p = evR (wArrG g0 g1 g1i w) p :=
    fun w p hp => evWK_eq hg h0 h1 h2 w hp
  unfold a6CheckG
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ordPK_eq (fun p hp => hE y1 p hp) (hW y1) div3]
    exact ho1
  · rw [← ordPK_eq (fun p hp => hE y2 p hp) (hW y2) div5]
    exact ho2
  · refine baseImgs_beq hg h0 h1 h2 fun b hb => ?_
    rw [evWK_append, evWK_append]
    exact eqB_iff.1 he1 b hb
  · refine baseImgs_beq hg h0 h1 h2 fun b hb => ?_
    rw [evWK_append, evWK_append]
    exact eqB_iff.1 he2 b hb
  · have := Nat.eq_of_beq_eq_true hp
    rw [lenA_eq', Array.length_toList] at this
    exact this
  · have := Nat.eq_of_beq_eq_true hl
    rw [lenA_eq', Array.length_toList] at this
    exact this
  · have hnd := (distinctK_spec _ 360 NT.lf (by simp [OrdN]) hd).2
    have key_eq : ∀ k, imgKey 3850 (baseImgs PairHS.bs (wArrG g0 g1 g1i (nw k))) =
        keyB (evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList 360 k) := fun k => by
      have eN : ∀ b < 4, evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList 360 k b =
          evR (wArrG g0 g1 g1i (nw k)) b := fun b hb => by
        rw [hnw k, (evNodeK_eq hg y1 y2 par lab 360 k b (by omega)).1, hE _ b (by omega)]
      simp only [keyB, imgKey, baseImgs, PairHS.bs, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil]
      rw [eN 0 (by norm_num), eN 1 (by norm_num), eN 2 (by norm_num), eN 3 (by norm_num)]
      simp
    have hmap : ((List.range 360).map fun k =>
        imgKey 3850 (baseImgs PairHS.bs (wArrG g0 g1 g1i (nw k)))) =
        (List.range 360).map fun k =>
          keyB (evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList 360 k) :=
      List.map_congr_left fun k _ => key_eq k
    rw [hmap]
    exact strictInc_mergeSort_of_nodup hnd
  · rw [List.all_eq_true]
    intro k hk
    have hk' := List.mem_range.1 hk
    have himp := (CFSG.KC.LQT.P.impB_iff).1 (CFSG.KS.allN_spec hn k hk')
    have eN : ∀ p < 3850, evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList 360 k p =
        evR (wArrG g0 g1 g1i (nw k)) p := fun p hp => by
      rw [hnw k, (evNodeK_eq hg y1 y2 par lab 360 k p hp).1, hE _ p hp]
    by_cases hord : ordB PairHS.bs (wArrG g0 g1 g1i (nw k)) 2 = true
    · have hpk : ordPK (evNodeK P0 P1 Q1 y1 y2 par.toList lab.toList 360 k) 2 = true := by
        rw [ordPK_eq eN (hW (nw k)) div2]
        exact hord
      have heq := eqB_iff.1 (himp hpk)
      rw [hord, Bool.not_true, Bool.false_or]
      refine baseImgs_beq hg h0 h1 h2 fun b hb => ?_
      have hb' := heq b hb
      rw [getW_eq, ← arrGetW] at hb'
      have hlt := evWK_lt hg cw[k]! (p := b) (by omega)
      simp only [evWK_append]
      rw [hb']
      congr 1
      rw [hnw k]
      exact (evNodeK_eq hg y1 y2 par lab 360 k _ hlt).1
    · have hf : ordB PairHS.bs (wArrG g0 g1 g1i (nw k)) 2 = false := by simpa using hord
      rw [hf]
      rfl

end Proof

theorem a6_sound {g0 g1 g1i : Array ℕ} {P0 P1 Q1 : ℕ} (h0 : g0 = unpack 3850 12 P0)
    (h1 : g1 = unpack 3850 12 P1) (h2 : g1i = unpack 3850 12 Q1) (y1 y2 c : List ℕ)
    (par lab : Array ℕ) (nw : ℕ → List ℕ) (cw : Array (List ℕ))
    (hnw : ∀ k, nw k = nodeWordFuelG par lab y1 y2 360 k)
    (h : a6K P0 P1 Q1 y1 y2 c par.toList lab.toList cw.toList = true) :
    a6CheckG g0 g1 g1i y1 y2 c par lab nw cw = true :=
  a6Check_of_a6K h0 h1 h2 y1 y2 c par lab nw cw hnw h

end CFSG.KC.LQT.A6

end
