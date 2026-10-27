module

public import Certificates.Data.Kernel.WeylE8.Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.LocalCompE8Sound
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def wordArrL (L : List (List ℤ)) : List ℕ → Array ℕ
  | [] => idA 240
  | r :: l => compA 240 (reflArrL L r) (wordArrL L l)

@[expose] def pArrL (PA PR g : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 120) fun j => PA[g[PR[j.val]!]!]!

@[expose] def pairCheckL (L : List (List ℤ)) (PA PR : Array ℕ) : Bool :=
  allLt 240 (fun x => decide (PA[x]! < 120) && PA[(negArrL L)[x]!]! == PA[x]!) &&
    allLt 240 (fun x => allLt 240 fun y =>
      PA[x]! != PA[y]! || y == x || y == (negArrL L)[x]!) &&
    allLt 120 (fun j => decide (PR[j]! < 240) && PA[PR[j]!]! == j)

@[expose] def zWordCheckL (L : List (List ℤ)) (F : List ℕ) : Bool :=
  eqA 240 (wordArrL L F) (negArrL L)

@[expose] def omCheckL (L : List (List ℤ)) (PA PR : Array ℕ) (OW : List (List ℕ))
    (G : Array (Array ℕ)) : Bool :=
  allLt 8 fun i => eqA 120 (pArrL PA PR (wordArrL L (OW.getD i []))) (copy0Arr G[i]!)

@[expose] def sZeroCheckL (L : List (List ℤ)) (PA PR : Array ℕ) (S : Array (Array ℕ))
    (B : List (Fin 120)) : Bool :=
  !(siftA 120 (rawLevels 120 S (B.map Fin.val).toArray) (B.map Fin.val).toArray 0
    (pArrL PA PR (reflArrL L 1)))

@[expose] def trialityCheckL (L : List (List ℤ)) (OW : List (List ℕ)) : Bool :=
  let u := compA 240 (wordArrL L (OW.getD 4 [])) (wordArrL L (OW.getD 6 []))
  let y := compA 240 (wordArrL L (OW.getD 6 [])) (wordArrL L (OW.getD 0 []))
  eqA 240 (compA 240 u u) (idA 240) && !(eqA 240 (compA 240 y y) (idA 240)) &&
    eqA 240 (compA 240 y y) (negArrL L)

theorem wordArr_eq (l : List ℕ) : wordArr l = wordArrL rootList l := by
  induction l with
  | nil => rfl
  | cons r l ih => simp only [wordArr, wordArrL, ih, reflArr_eq]

theorem pairCheck_eq : pairCheck = pairCheckL rootList pairArr pairRepArr := rfl

theorem zWordCheck_eq : zWordCheck = zWordCheckL rootList frameRootList := by
  simp only [zWordCheck, zWordCheckL, wordArr_eq, negArr_eq]

theorem omCheck_eq : omCheck = omCheckL rootList pairArr pairRepArr omWords genArrs := by
  simp only [omCheck, omCheckL, wordArr_eq]
  rfl

theorem sZeroCheck_eq : sZeroCheck = sZeroCheckL rootList pairArr pairRepArr omega1S omega1Base :=
  rfl

theorem trialityCheck_eq : trialityCheck = trialityCheckL rootList omWords := by
  simp only [trialityCheck, trialityCheckL, wordArr_eq, negArr_eq]

theorem siftK_eq {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hg : g = unpack n w G) (hG : Nat.shiftRight G (n * w) = 0)
    (hc : CFSG.KS.Prim.canonK n w (mask w) (n * w) G = true) :
    siftA n (rawLevels n S base) base 0 g = siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G :=
  CFSG.KS.Raw.siftK_eq hb hp hl hg hG (range_of_canonK hc)

private theorem e8_eq (P i : Nat) : e8 P i = pg 8 (mask 8) P i := rfl

private theorem notB'_eq' (b : Bool) : notB' b = !b := by cases b <;> rfl

private theorem bindList_go {n P : Nat} : ∀ (l : List Nat) (j : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
      (fun p _ ih j => bAnd(Nat.blt p (nat_lit 240),
        bAnd(Nat.beq p (pg (nat_lit 8) (nat_lit 255) P j), ih (Nat.succ j)))) l j = true →
    j + l.length = n ∧ ∀ i (hi : i < l.length), l[i] < 240 ∧ l[i] = e8 P (j + i)
  | [], j, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun i hi => absurd hi (by simp)⟩
  | p :: l, j, h => by
    have h' : (Nat.blt p 240 && (Nat.beq p (e8 P j) &&
        List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j n)
          (fun p _ ih j => bAnd(Nat.blt p (nat_lit 240),
            bAnd(Nat.beq p (pg (nat_lit 8) (nat_lit 255) P j), ih (Nat.succ j)))) l (j + 1))) =
        true := by
      rw [← Orb.bAnd_eq, ← Orb.bAnd_eq]
      exact h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    obtain ⟨ih1, ih2⟩ := bindList_go l (j + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · exact ⟨h1, by simpa using h2⟩
    · have := ih2 i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      exact ⟨this.1, by rw [this.2]; congr 1; omega⟩

private theorem bindList_spec {l : List Nat} {n P : Nat} (h : bindList l n P = true) :
    l.length = n ∧ ∀ i (hi : i < l.length), l[i] < 240 ∧ l[i] = e8 P i := by
  obtain ⟨h1, h2⟩ := bindList_go (n := n) (P := P) l 0 h
  exact ⟨by omega, fun i hi => by simpa using h2 i hi⟩

private theorem bindArr {A : Array ℕ} {n P : Nat} (h : bindList A.toList n P = true) {i : Nat}
    (hi : i < n) : A[i]! = e8 P i ∧ e8 P i < 240 := by
  obtain ⟨h1, h2⟩ := bindList_spec h
  have hs : i < A.size := by rw [← Array.length_toList, h1]; exact hi
  have := h2 i (by rw [h1]; exact hi)
  rw [Array.getElem_toList] at this
  rw [getElem!_pos A i hs, ← this.2]
  exact ⟨rfl, this.1⟩

private theorem arr_ext {A B : Array ℕ} {n : ℕ} (hA : A.size = n) (hB : B.size = n)
    (h : ∀ i < n, A[i]! = B[i]!) : A = B := by
  apply Array.ext (by omega)
  intro i h1 h2
  have := h i (by omega)
  rwa [getElem!_pos A i h1, getElem!_pos B i h2] at this

private theorem unpack_size (n w P : ℕ) : (unpack n w P).size = n := by
  simp [unpack]

private theorem rt_lt {RK RT : Nat → Nat} (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) {r : Nat}
    (hr' : r < 240) {i : Nat} (hi : i < 240) : pg 8 (mask 8) (RT r) i < 240 := by
  have h := hr r hr'
  unfold reflRowOK at h
  rw [Orb.strictB_eq, Orb.allN_iff] at h
  have h1 := h i hi
  rw [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h1
  exact h1.1

private theorem neg_lt {RK : Nat → Nat} {NEG : Nat} (hn : negTabOK RK NEG = true) {i : Nat}
    (hi : i < 240) : e8 NEG i < 240 := by
  unfold negTabOK at hn
  rw [Orb.allN_iff] at hn
  have h1 := hn i hi
  rw [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h1
  exact h1.1

private theorem unpack_pcomp {P Q : Nat} (hQ : ∀ i < 240, pg 8 (mask 8) Q i < 240) :
    unpack 240 8 (pcomp 240 8 (mask 8) P Q) = compA 240 (unpack 240 8 P) (unpack 240 8 Q) := by
  apply arr_ext (unpack_size _ _ _) (by simp [compA])
  intro i hi
  rw [Orb.unpack_get hi, PF.pg_pcomp (by norm_num) hi, compA_get hi, Orb.unpack_get hi,
    Orb.unpack_get (hQ i hi)]

private theorem pcomp_lt {P Q : Nat} (hP : ∀ i < 240, pg 8 (mask 8) P i < 240)
    (hQ : ∀ i < 240, pg 8 (mask 8) Q i < 240) :
    ∀ i < 240, pg 8 (mask 8) (pcomp 240 8 (mask 8) P Q) i < 240 := fun i hi => by
  rw [PF.pg_pcomp (by norm_num) hi]
  exact hP _ (hQ i hi)

private theorem unpack_pidn : unpack 240 8 (pidn 240 8) = idA 240 := by
  apply arr_ext (unpack_size _ _ _) (by simp [idA])
  intro i hi
  rw [Orb.unpack_get hi, PF.pg_pidn (by norm_num) (by norm_num) hi, idA, getElem!_ofFn_nat _ hi]

private theorem pg_low {X i : Nat} (hi : i < 240) :
    pg 8 (mask 8) (low X) i = pg 8 (mask 8) X i := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [PF.testBit_pgM, PF.testBit_pgM]
  by_cases hk : k < 8
  · have e : low X = X &&& (2 ^ 1920 - 1) := by
      rw [← PF.mask_eq]
      rfl
    have h1 : 8 * i + k < 1920 := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hk, h1]
  · simp [hk]

private theorem unpack_low (X : Nat) : unpack 240 8 (low X) = unpack 240 8 X :=
  arr_ext (unpack_size _ _ _) (unpack_size _ _ _) fun i hi => by
    rw [Orb.unpack_get hi, Orb.unpack_get hi, pg_low hi]

private noncomputable def wpart (RT : Nat → Nat) (W n k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn (nat_lit 240) (nat_lit 8))
    (fun k ih => strictN ih fun A =>
      pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) (RT (e8 W (Nat.sub (Nat.sub n k) (nat_lit 1)))) A) k

private theorem wpart_succ (RT : Nat → Nat) (W n k : Nat) :
    wpart RT W n (k + 1) = pcomp 240 8 (mask 8) (RT (e8 W (n - k - 1))) (wpart RT W n k) := by
  have e : wpart RT W n (k + 1) = strictN (wpart RT W n k) fun A =>
      pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) (RT (e8 W (Nat.sub (Nat.sub n k) (nat_lit 1)))) A :=
    rfl
  rw [e, Orb.strictN_eq]
  rfl

private theorem word_eq {L : List (List ℤ)} {RK RT : Nat → Nat}
    (hrefl : ∀ r < 240, reflArrL L r = unpack 240 8 (RT r))
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) {F : List Nat} {W n : Nat}
    (hF : bindList F n W = true) :
    wordArrL L F = unpack 240 8 (wordK RT W n) ∧
      ∀ i < 240, pg 8 (mask 8) (wordK RT W n) i < 240 := by
  obtain ⟨hlen, hget⟩ := bindList_spec hF
  have key : ∀ k ≤ n, wordArrL L (F.drop (n - k)) = unpack 240 8 (wpart RT W n k) ∧
      ∀ i < 240, pg 8 (mask 8) (wpart RT W n k) i < 240 := by
    intro k
    induction k with
    | zero =>
      intro _
      have e : F.drop (n - 0) = [] := List.drop_of_length_le (by omega)
      refine ⟨?_, fun i hi => ?_⟩
      · rw [e]
        exact unpack_pidn.symm
      · have : wpart RT W n 0 = pidn 240 8 := rfl
        rw [this, PF.pg_pidn (by norm_num) (by norm_num) hi]
        exact hi
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hm : n - (k + 1) < F.length := by omega
      have hd : F.drop (n - (k + 1)) = F[n - (k + 1)] :: F.drop (n - k) := by
        rw [List.drop_eq_getElem_cons hm]
        congr 2
        omega
      obtain ⟨hlt, heq⟩ := hget _ hm
      have he : e8 W (n - k - 1) = F[n - (k + 1)] := by
        rw [heq]
        congr 1
      rw [wpart_succ, he]
      refine ⟨?_, pcomp_lt (fun i hi => rt_lt hr hlt hi) ih2⟩
      rw [hd]
      simp only [wordArrL]
      rw [ih1, hrefl _ hlt, unpack_pcomp ih2]
  have := key n le_rfl
  rw [Nat.sub_self, List.drop_zero] at this
  exact this

private theorem fld_pmk {n w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w) :
    PF.Fld w (pmk n w f) (fun i => if i < n then f i else 0) := by
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w f hf (clog n) 0
  have e : pmk n w f = pmkT n w f (clog n) 0 := by
    unfold pmk
    rw [PF.strictN_eqP]
  rw [e]
  refine PF.fld_congr h fun i => ?_
  by_cases hi : i < n
  · have h2 : i < 2 ^ clog n := by omega
    simp [hi, h2]
  · simp [hi]

private theorem pArr_get {PA PR : Array ℕ} {PAP PRP X : Nat}
    (hPA : bindList PA.toList 240 PAP = true) (hPR : bindList PR.toList 120 PRP = true)
    (hX : ∀ i < 240, pg 8 (mask 8) X i < 240) {j : Nat} (hj : j < 120) :
    (pArrL PA PR (unpack 240 8 X))[j]! = e8 PAP (e8 X (e8 PRP j)) := by
  obtain ⟨hr1, hr2⟩ := bindArr hPR hj
  rw [pArrL, getElem!_ofFn_nat _ hj]
  simp only
  rw [hr1, Orb.unpack_get hr2, (bindArr hPA (hX _ hr2)).1]
  rfl

theorem pair_sound {L : List (List ℤ)} {PA PR : Array ℕ} {RK RT : Nat → Nat} {SO NEG PAP PRP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hPA : bindList PA.toList 240 PAP = true) (hPR : bindList PR.toList 120 PRP = true)
    (k : pairK NEG PAP PRP = true) :
    pairCheckL L PA PR = true := by
  have hneg : ∀ x < 240, (negArrL L)[x]! = e8 NEG x := fun x hx => by
    rw [(tables_sound hb hs hr hn).2, Orb.unpack_get hx]
    rfl
  unfold pairK at k
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Orb.strictB_eq] at k
  obtain ⟨k1, k2, k3⟩ := k
  unfold pairCheckL
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun j hj => ?_⟩
  · have h1 := k1 x hx
    simp only [Nat.blt_eq, Nat.beq_eq] at h1
    rw [hneg x hx, (bindArr hPA hx).1, (bindArr hPA (neg_lt hn hx)).1]
    simp only [decide_eq_true_eq, beq_iff_eq]
    exact ⟨h1.1, h1.2⟩
  · have h1 := (k2 x hx) y hy
    rw [hneg x hx, (bindArr hPA hx).1, (bindArr hPA hy).1]
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    by_cases e : e8 PAP x = e8 PAP y
    · simp only [Orb.bIf_eq, Nat.beq_eq, e, ite_true] at h1
      by_cases e2 : y = x
      · exact Or.inl (Or.inr e2)
      · simp only [e2, ite_false] at h1
        exact Or.inr (Nat.eq_of_beq_eq_true h1)
    · exact Or.inl (Or.inl e)
  · have h1 := k3 j hj
    simp only [Nat.blt_eq, Nat.beq_eq] at h1
    rw [(bindArr hPR hj).1, (bindArr hPA h1.1).1]
    simp only [decide_eq_true_eq, beq_iff_eq]
    exact h1

theorem zWord_sound {L : List (List ℤ)} {F : List ℕ} {RK RT : Nat → Nat} {SO NEG FRP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hF : bindList F 8 FRP = true) (k : zK RT NEG FRP = true) :
    zWordCheckL L F = true := by
  obtain ⟨hrefl, hneg⟩ := tables_sound hb hs hr hn
  obtain ⟨hw, -⟩ := word_eq hrefl hr hF
  have hz : wordK RT FRP 8 = low NEG := Nat.eq_of_beq_eq_true k
  unfold zWordCheckL
  rw [hw, hz, unpack_low, hneg]
  exact CFSG.KS.Raw.eqA_self _

theorem om_sound {L : List (List ℤ)} {PA PR : Array ℕ} {OW : List (List ℕ)} {G : Array (Array ℕ)}
    {RK RT GS : Nat → Nat} {SO NEG PAP PRP OWP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hPA : bindList PA.toList 240 PAP = true) (hPR : bindList PR.toList 120 PRP = true)
    (hOW : allN 8 (fun i => bindList (OW.getD i []) 4 (owK OWP i)) = true)
    (hG : ∀ j < 8, copy0Arr G[j]! = unpack 120 9 (GS j)) (k : omK RT PAP PRP OWP GS = true) :
    omCheckL L PA PR OW G = true := by
  obtain ⟨hrefl, -⟩ := tables_sound hb hs hr hn
  unfold omK at k
  rw [Orb.allN_iff] at k hOW
  unfold omCheckL
  rw [allLt_iff]
  intro i hi
  obtain ⟨hw, hwl⟩ := word_eq hrefl hr (hOW i hi)
  have ki := k i hi
  rw [Orb.strictB_eq, Orb.allN_iff] at ki
  rw [hw, hG i hi]
  unfold eqA
  rw [allLt_iff]
  intro j hj
  rw [beq_iff_eq, pArr_get hPA hPR hwl hj, Orb.unpack_get hj]
  exact Nat.eq_of_beq_eq_true (ki j hj)

theorem triality_sound {L : List (List ℤ)} {OW : List (List ℕ)} {RK RT : Nat → Nat}
    {SO NEG OWP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hOW : allN 8 (fun i => bindList (OW.getD i []) 4 (owK OWP i)) = true)
    (k : triK RT NEG OWP = true) :
    trialityCheckL L OW = true := by
  obtain ⟨hrefl, hneg⟩ := tables_sound hb hs hr hn
  rw [Orb.allN_iff] at hOW
  obtain ⟨h0, l0⟩ := word_eq hrefl hr (hOW 0 (by norm_num))
  obtain ⟨h4, l4⟩ := word_eq hrefl hr (hOW 4 (by norm_num))
  obtain ⟨h6, l6⟩ := word_eq hrefl hr (hOW 6 (by norm_num))
  unfold triK at k
  simp only [Orb.strictB_eq, Orb.bAnd_eq, Bool.and_eq_true] at k
  obtain ⟨ku, ky, ky2⟩ := k
  rw [notB'_eq', Bool.not_eq_true'] at ky
  generalize wordK RT (owK OWP 0) 4 = W0 at h0 l0 ku ky ky2
  generalize wordK RT (owK OWP 4) 4 = W4 at h4 l4 ku ky ky2
  generalize wordK RT (owK OWP 6) 4 = W6 at h6 l6 ku ky ky2
  have ku' : pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8) W4 W6) (pcomp 240 8 (mask 8) W4 W6) =
      pidn 240 8 := Nat.eq_of_beq_eq_true ku
  have ky' : pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8) W6 W0) (pcomp 240 8 (mask 8) W6 W0) ≠
      pidn 240 8 := Nat.ne_of_beq_eq_false ky
  have ky2' : pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8) W6 W0) (pcomp 240 8 (mask 8) W6 W0) =
      low NEG := Nat.eq_of_beq_eq_true ky2
  have lU := pcomp_lt l4 l6
  have lY := pcomp_lt l6 l0
  have hYn : eqA 240 (unpack 240 8 (pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8) W6 W0)
      (pcomp 240 8 (mask 8) W6 W0))) (idA 240) = false := by
    cases e : eqA 240 (unpack 240 8 (pcomp 240 8 (mask 8) (pcomp 240 8 (mask 8) W6 W0)
      (pcomp 240 8 (mask 8) W6 W0))) (idA 240)
    · rfl
    · exfalso
      apply ky'
      apply PF.eq_of_fields (n := 240) (by norm_num) (PF.pcomp_shr _ _ (by norm_num) (by norm_num))
        (PF.pidn_shr (by norm_num) (by norm_num))
      intro i hi
      unfold eqA at e
      rw [allLt_iff] at e
      have := e i hi
      rw [beq_iff_eq, Orb.unpack_get hi, idA, getElem!_ofFn_nat _ hi] at this
      rw [this, PF.pg_pidn (by norm_num) (by norm_num) hi]
  unfold trialityCheckL
  simp only []
  rw [h0, h4, h6, ← unpack_pcomp l6, ← unpack_pcomp l0, ← unpack_pcomp lU, ← unpack_pcomp lY,
    hYn, ku', unpack_pidn, ky2', unpack_low, hneg, CFSG.KS.Raw.eqA_self, CFSG.KS.Raw.eqA_self]
  rfl

theorem sZero_sound {L : List (List ℤ)} {PA PR : Array ℕ} {S : Array (Array ℕ)}
    {B : List (Fin 120)} {RK RT PS PSI LR TR TRI : Nat → Nat} {SO NEG PAP PRP kS BP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hPA : bindList PA.toList 240 PAP = true) (hPR : bindList PR.toList 120 PRP = true)
    (kp : pairK NEG PAP PRP = true)
    (hcb : Binds 120 9 PS kS 7 BP S (B.map Fin.val).toArray)
    (hcp : allN kS (fun j => permOK 120 9 (mask 9) (120 * 9) (PS j) (PSI j)) = true)
    (hcl : LevelsOK 120 9 PS PSI LR TR TRI kS 7 BP)
    (k : notB' (siftK 120 9 (mask 9) (120 * 9) (pidn 120 9) LR TRI BP 7 0
      (pairImg RT PAP PRP 1)) = true) :
    sZeroCheckL L PA PR S B = true := by
  obtain ⟨hrefl, -⟩ := tables_sound hb hs hr hn
  unfold pairK at kp
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Orb.strictB_eq] at kp
  obtain ⟨k1, -, -⟩ := kp
  have hX : ∀ i < 240, pg 8 (mask 8) (RT 1) i < 240 := fun i hi => rt_lt hr (by norm_num) hi
  have hf : ∀ j < 120, e8 PAP (e8 (RT 1) (e8 PRP j)) < 120 := fun j hj => by
    have := k1 _ (hX _ (bindArr hPR hj).2)
    simp only [Nat.blt_eq] at this
    exact this.1
  have hP : pairImg RT PAP PRP 1 = pmk 120 9 (fun j => e8 PAP (e8 (RT 1) (e8 PRP j))) := by
    unfold pairImg
    rw [Orb.strictN_eq]
  have hfld := fld_pmk (n := 120) (w := 9) (f := fun j => e8 PAP (e8 (RT 1) (e8 PRP j)))
    (by norm_num) (fun x hx => by have := hf x hx; omega)
  have hpg : ∀ j < 120, pg 9 (mask 9) (pairImg RT PAP PRP 1) j = e8 PAP (e8 (RT 1) (e8 PRP j)) :=
    fun j hj => by
      rw [hP, PF.pg_of_fld hfld (by simp only [hj, ↓reduceIte]; have := hf j hj; omega)]
      simp [hj]
  have hg : pArrL PA PR (reflArrL L 1) = unpack 120 9 (pairImg RT PAP PRP 1) := by
    rw [hrefl 1 (by norm_num)]
    apply arr_ext (by simp [pArrL]) (unpack_size _ _ _)
    intro j hj
    rw [pArr_get hPA hPR hX hj, Orb.unpack_get hj, hpg j hj]
  have hG : Nat.shiftRight (pairImg RT PAP PRP 1) (120 * 9) = 0 := by
    rw [hP]
    exact PF.shr_zero_of_fld (by norm_num) hfld (fun i hi => ite_eq_right_iff.2 (fun h => absurd h (by omega)))
  have hrng : allN 120 (fun i => Nat.blt (pg 9 (mask 9) (pairImg RT PAP PRP 1) i) 120) = true :=
    Orb.allN_iff.2 fun i hi => by
      rw [hpg i hi, Nat.blt_eq]
      exact hf i hi
  unfold sZeroCheckL
  rw [CFSG.KS.Raw.siftK_eq hcb hcp hcl hg hG hrng]
  rw [notB'_eq'] at k
  exact k

end CFSG.KLC.E8

end
