
module

public import Certificates.Data.Kernel.Spor.HNAOrb
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNOTests

public section

namespace CFSG.KS.HNA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.ComponentClassification.RankTwoSporadic.HN

theorem strictB_app' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_app' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem bAnd_eq' (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_eq' (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

theorem of_slices' {L K : Nat} {f : Nat → Bool} (hL : 0 < L)
    (h : ∀ s < K, allN L (fun d => f (Nat.add (Nat.mul L s) d)) = true) :
    ∀ i < L * K, f i = true := by
  intro i hi
  have hs : i / L < K := (Nat.div_lt_iff_lt_mul hL).2 (by rwa [Nat.mul_comm] at hi)
  have h1 := allN_spec (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  rwa [e] at h1

theorem listUp_aux (F : Nat → Nat) : ∀ (k j : Nat),
    Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun _ ih j => List.cons (F j) (ih (Nat.succ j))) k j = (List.range' j k).map F
  | 0, _ => rfl
  | k + 1, j => by
    rw [List.range'_succ, List.map_cons, ← listUp_aux F k (j + 1)]

theorem listUp_eq (F : Nat → Nat) (k : Nat) : listUp F k = (List.range k).map F := by
  rw [List.range_eq_range']
  exact listUp_aux F k 0

theorem pairsOf_map_range' (F : Nat → Nat) : ∀ (k j : Nat),
    pairsOf ((List.range' j (2 * k)).map F) =
      (List.range k).map fun t => (F (j + 2 * t), F (j + 2 * t + 1))
  | 0, _ => rfl
  | k + 1, j => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, List.range'_succ, List.range'_succ,
      List.map_cons, List.map_cons, pairsOf, pairsOf_map_range' F k (j + 1 + 1),
      List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp, Prod.mk.injEq]
    constructor <;> congr 1 <;> omega

theorem pairsOf_map_range (F : Nat → Nat) (k : Nat) :
    pairsOf ((List.range (2 * k)).map F) = (List.range k).map fun t => (F (2 * t), F (2 * t + 1)) := by
  rw [List.range_eq_range', pairsOf_map_range' F k 0]
  simp

@[expose] def awOf (Wc Wf Wm : Nat → Nat) (i : Nat) : AWit :=
  if Wc i = 0 then .skip else .ord4 [Wf i] (Wm i)

section Wits

variable {Wc Wf Wm : Nat → Nat} {N : Nat}

theorem wbRun_nil (ph i : Nat) :
    wbRun Wc Wf Wm N [] ph i = (Nat.beq ph 0 && Nat.beq i N) := bAnd_eq' _ _

theorem wbRun_cons (x : Nat) (r : List Nat) (ph i : Nat) :
    wbRun Wc Wf Wm N (x :: r) ph i =
      if Nat.beq ph 0 = true then
        (if Nat.beq x 0 = true then (Nat.beq (Wc i) 0 && wbRun Wc Wf Wm N r 0 (i + 1))
          else (!Nat.beq (Wc i) 0 && wbRun Wc Wf Wm N r 1 i))
      else if Nat.beq ph 1 = true then (Nat.beq x 1 && wbRun Wc Wf Wm N r 2 i)
      else if Nat.beq ph 2 = true then (Nat.beq x (Wf i) && wbRun Wc Wf Wm N r 3 i)
      else (Nat.beq x (Wm i) && wbRun Wc Wf Wm N r 0 (i + 1)) := by
  change bIf(Nat.beq ph 0, bIf(Nat.beq x 0, bAnd(Nat.beq (Wc i) 0, wbRun Wc Wf Wm N r 0 (i + 1)),
      bAnd(Bool.not (Nat.beq (Wc i) 0), wbRun Wc Wf Wm N r 1 i)),
    bIf(Nat.beq ph 1, bAnd(Nat.beq x 1, wbRun Wc Wf Wm N r 2 i),
    bIf(Nat.beq ph 2, bAnd(Nat.beq x (Wf i), wbRun Wc Wf Wm N r 3 i),
      bAnd(Nat.beq x (Wm i), wbRun Wc Wf Wm N r 0 (i + 1))))) = _
  simp only [bAnd_eq']
  simp only [bIf_eq']

theorem wbRun_le : ∀ (L : List Nat) (ph i : Nat), wbRun Wc Wf Wm N L ph i = true → i ≤ N
  | [], ph, i, h => by
    rw [wbRun_nil, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    omega
  | x :: r, ph, i, h => by
    rw [wbRun_cons] at h
    split_ifs at h <;> simp only [Bool.and_eq_true] at h
    · have := wbRun_le r _ _ h.2; omega
    · exact wbRun_le r _ _ h.2
    · exact wbRun_le r _ _ h.2
    · exact wbRun_le r _ _ h.2
    · have := wbRun_le r _ _ h.2; omega

theorem range'_cons {i k : Nat} (h : i < k) : List.range' i (k - i) = i :: List.range' (i + 1) (k - (i + 1)) := by
  rw [show k - i = (k - (i + 1)) + 1 by omega, List.range'_succ]

theorem witsOf_nil : ∀ fuel : Nat, witsOf fuel [] = []
  | 0 => rfl
  | _ + 1 => rfl

theorem witsOf_skip (fuel : Nat) (r : List Nat) : witsOf (fuel + 1) (0 :: r) = .skip :: witsOf fuel r :=
  rfl

theorem witsOf_ord4 (fuel c f m : Nat) (r : List Nat) :
    witsOf (fuel + 1) ((c + 1) :: 1 :: f :: m :: r) = .ord4 [f] m :: witsOf fuel r := rfl

theorem witsOf_of_wbRun : ∀ (fuel : Nat) (L : List Nat) (i : Nat), L.length ≤ fuel →
    wbRun Wc Wf Wm N L 0 i = true →
      witsOf fuel L = (List.range' i (N - i)).map (awOf Wc Wf Wm)
  | fuel, [], i, _, h => by
    rw [wbRun_nil, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    rw [h.2, Nat.sub_self, witsOf_nil]
    rfl
  | 0, _ :: _, _, hl, _ => absurd hl (by simp)
  | fuel + 1, x :: r, i, hl, h => by
    have b00 : Nat.beq 0 0 = true := rfl
    have b11 : Nat.beq 1 1 = true := rfl
    have b22 : Nat.beq 2 2 = true := rfl
    have n10 : ¬ Nat.beq 1 0 = true := by decide
    have n20 : ¬ Nat.beq 2 0 = true := by decide
    have n21 : ¬ Nat.beq 2 1 = true := by decide
    have n30 : ¬ Nat.beq 3 0 = true := by decide
    have n31 : ¬ Nat.beq 3 1 = true := by decide
    have n32 : ¬ Nat.beq 3 2 = true := by decide
    rw [wbRun_cons, ite_eq_left b00] at h
    by_cases hx : x = 0
    · subst hx
      rw [ite_eq_left b00, Bool.and_eq_true, Nat.beq_eq] at h
      have hi := wbRun_le r _ _ h.2
      have ha : awOf Wc Wf Wm i = .skip := ite_eq_left h.1
      rw [witsOf_skip, witsOf_of_wbRun fuel r (i + 1) (Nat.le_of_succ_le_succ hl) h.2,
        range'_cons (i := i) (k := N) (by omega), List.map_cons, ha]
    · rw [ite_eq_right (fun e => hx (Nat.eq_of_beq_eq_true e)), Bool.and_eq_true] at h
      obtain ⟨hc, h⟩ := h
      have hc' : Wc i ≠ 0 := fun e => by rw [e] at hc; exact absurd hc (by decide)
      have ha : awOf Wc Wf Wm i = .ord4 [Wf i] (Wm i) := ite_eq_right hc'
      match r, hl, h with
      | [], _, h =>
        rw [wbRun_nil, Bool.and_eq_true] at h
        exact absurd h.1 n10
      | y :: r, hl, h =>
        rw [wbRun_cons, ite_eq_right n10, ite_eq_left b11, Bool.and_eq_true, Nat.beq_eq] at h
        obtain ⟨rfl, h⟩ := h
        match r, hl, h with
        | [], _, h =>
          rw [wbRun_nil, Bool.and_eq_true] at h
          exact absurd h.1 n20
        | f :: r, hl, h =>
          rw [wbRun_cons, ite_eq_right n20, ite_eq_right n21, ite_eq_left b22, Bool.and_eq_true, Nat.beq_eq] at h
          obtain ⟨rfl, h⟩ := h
          match r, hl, h with
          | [], _, h =>
            rw [wbRun_nil, Bool.and_eq_true] at h
            exact absurd h.1 n30
          | m :: r, hl, h =>
            rw [wbRun_cons, ite_eq_right n30, ite_eq_right n31, ite_eq_right n32, Bool.and_eq_true, Nat.beq_eq] at h
            obtain ⟨rfl, h⟩ := h
            have hi := wbRun_le r _ _ h
            have hl' : r.length ≤ fuel := by
              simp only [List.length_cons] at hl
              omega
            obtain ⟨c, rfl⟩ : ∃ c, x = c + 1 := ⟨x - 1, by omega⟩
            rw [witsOf_ord4, witsOf_of_wbRun fuel r (i + 1) hl' h,
              range'_cons (i := i) (k := N) (by omega), List.map_cons, ha]

end Wits

theorem progOK_of {A B : Nat → Nat} : ∀ (k j m : Nat),
    (∀ t < k, A (j + t) < m + t ∧ B (j + t) < m + t) →
      progOK m ((List.range' j k).map fun t => (A t, B t)) = true
  | 0, _, _, _ => rfl
  | k + 1, j, m, h => by
    rw [List.range'_succ, List.map_cons]
    simp only [progOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by simpa using (h 0 (by omega)).1, by simpa using (h 0 (by omega)).2⟩,
      progOK_of k (j + 1) (m + 1) fun t ht => ?_⟩
    have := h (t + 1) (by omega)
    rw [show j + 1 + t = j + (t + 1) by omega, show m + 1 + t = m + (t + 1) by omega]
    exact this

variable {n w : Nat}

theorem regsFrom_unpack {m : Nat} {X A B : Nat → Nat} : ∀ (k j : Nat) (R : Array (Array Nat)),
    R.size = m + j → (∀ i < m + j, R[i]! = unpack n w (X i) ∧ PP n w (X i)) →
    (∀ t < k, stepK n w m X A B (j + t) = true) →
    (regsFrom n R ((List.range' j k).map fun t => (A t, B t))).size = m + j + k ∧
      ∀ i < m + j + k, (regsFrom n R ((List.range' j k).map fun t => (A t, B t)))[i]! =
        unpack n w (X i) ∧ PP n w (X i)
  | 0, j, R, hs, hR, _ => ⟨hs, fun i hi => hR i hi⟩
  | k + 1, j, R, hs, hR, hst => by
    have h0 := hst 0 (by omega)
    rw [Nat.add_zero] at h0
    unfold stepK at h0
    simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h0
    obtain ⟨ha, hb, he⟩ := h0
    have hA := hR _ ha
    have hB := hR _ hb
    have hnew : compA n R[A j]! R[B j]! = unpack n w (X (m + j)) ∧ PP n w (X (m + j)) := by
      rw [hA.1, hB.1, compA_PP hA.2 hB.2, ← he]
      exact ⟨rfl, hA.2.mul hB.2⟩
    have hget : (R.push (compA n R[A j]! R[B j]!))[m + j]! = compA n R[A j]! R[B j]! := by
      rw [← hs, getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]
    rw [List.range'_succ, List.map_cons]
    have ih := regsFrom_unpack (m := m) (X := X) (A := A) (B := B) k (j + 1)
      (R.push (compA n R[A j]! R[B j]!))
      (by rw [Array.size_push, hs]; omega)
      (fun i hi => by
        by_cases hlt : i < m + j
        · rw [getElem!_pos _ i (by rw [Array.size_push]; omega), Array.getElem_push_lt (by omega),
            ← getElem!_pos R i (by omega)]
          exact hR i hlt
        · obtain rfl : i = m + j := by omega
          rw [hget]
          exact hnew)
      (fun t ht => by
        have := hst (t + 1) (by omega)
        rwa [show j + (t + 1) = j + 1 + t by omega] at this)
    have e : regsFrom n R ((A j, B j) :: (List.range' (j + 1) k).map fun t => (A t, B t)) =
        regsFrom n (R.push (compA n R[A j]! R[B j]!))
          ((List.range' (j + 1) k).map fun t => (A t, B t)) := rfl
    refine ⟨?_, fun i hi => ?_⟩
    · rw [e, ih.1]
      omega
    · rw [e]
      exact ih.2 i (by omega)

theorem prodA_single (hsz : szOK n w = true) {p : Nat} (hp : PP n w p) :
    prodA n [unpack n w p] = unpack n w (pcomp n w (mask w) p (pidn n w)) := by
  change compA n (unpack n w p) (idA n) = _
  rw [idA_eq hsz, compA_PP hp (PP.id hsz)]

theorem powA_unpack (hsz : szOK n w = true) {p : Nat} (hp : PP n w p) : ∀ k : Nat,
    powA n (unpack n w p) k = unpack n w (ppow n w (mask w) (pidn n w) p k) ∧
      PP n w (ppow n w (mask w) (pidn n w) p k)
  | 0 => ⟨idA_eq hsz, PP.id hsz⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := powA_unpack hsz hp k
    have e : ppow n w (mask w) (pidn n w) p (k + 1) =
        pcomp n w (mask w) p (ppow n w (mask w) (pidn n w) p k) :=
      strictN_app' _ _
    refine ⟨?_, by rw [e]; exact hp.mul h2⟩
    change compA n (unpack n w p) (powA n (unpack n w p) k) = _
    rw [h1, compA_PP hp h2, e]

theorem commutatorA_unpack {p q : Nat} (hp : PP n w p) (hq : PP n w q) :
    commutatorA n (unpack n w p) (unpack n w q) = unpack n w (commP n w p q) ∧
      PP n w (commP n w p q) := by
  unfold commutatorA commP
  rw [invCand_PP hp, invCand_PP hq, compA_PP hp hq, compA_PP hp.inv hq.inv,
    compA_PP (hp.mul hq) (hp.inv.mul hq.inv)]
  exact ⟨rfl, (hp.mul hq).mul (hp.inv.mul hq.inv)⟩

theorem aWitOK_of_witK (hsz : szOK n w = true) {T C Wc Wf Wm : Nat → Nat} {nc i : Nat}
    {cs : Array (Array Nat)} (hcs : cs.size = nc)
    (hC : ∀ f < nc, cs[f]! = unpack n w (C f) ∧ PP n w (C f)) (hT : PP n w (T i))
    (h : witK n w (pidn n w) T C Wc Wf Wm nc i = true) :
    aWitOK n cs (unpack n w (T i)) (awOf Wc Wf Wm i) = true := by
  unfold witK at h
  rw [strictB_app', bIf_eq'] at h
  have hI := PP.id hsz
  unfold awOf
  split_ifs at h with hc
  · rw [ite_eq_left (Nat.eq_of_beq_eq_true hc)]
    simp only [aWitOK, isInvolA]
    rw [idA_eq hsz, eqA_PP hT hI, compA_PP hT hT, eqA_PP (hT.mul hT) hI]
    simpa only [bAnd_eq'] using h
  · rw [ite_eq_right (fun e => hc (by rw [e]; rfl))]
    rw [bAnd_eq', Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hf, h⟩ := h
    simp only [aWitOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq, List.map_cons, List.map_nil]
    refine ⟨by rw [hcs]; exact hf, ?_⟩
    obtain ⟨hCe, hCp⟩ := hC _ hf
    obtain ⟨e1, p1⟩ := commutatorA_unpack hT hCp
    rw [hCe, e1, prodA_single hsz p1]
    obtain ⟨e2, p2⟩ := powA_unpack hsz (p1.mul hI) (Wm i)
    rw [e2]
    unfold ord4K at h
    rw [strictB_app'] at h
    unfold ord4A
    rw [compA_PP p2 p2, idA_eq hsz, eqA_PP (p2.mul p2) hI, compA_PP (p2.mul p2) (p2.mul p2),
      eqA_PP ((p2.mul p2).mul (p2.mul p2)) hI]
    simpa only [bAnd_eq'] using h

end CFSG.KS.HNA

end
