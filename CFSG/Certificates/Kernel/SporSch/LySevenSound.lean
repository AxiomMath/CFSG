module

public import Certificates.Data.Kernel.SporSch.LySeven
public import CFSG.Sporadic.Schreier.LyCheckSeven
import CFSG.Certificates.Kernel.SporSch.StrNl
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas
import CFSG.Certificates.Kernel.SporSch.LySevMat
import CFSG.Certificates.Kernel.SporSch.LySevCbfs
public import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KS.SporSch.LySev

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native

@[expose] noncomputable def dec7 (x : Nat) : Array Nat := Array.ofFn (n := 7) fun r => d3 x r.val

@[expose] noncomputable def dec49 (x : Nat) : Array Nat := Array.ofFn (n := 49) fun t => d3 x t.val

@[expose] def padU (M : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j =>
    if j.val < 7 then (M[i.val]!)[j.val]! else 0

@[expose] noncomputable def qmK (n : Nat) : Nat :=
  foldN n (fun s acc => Nat.lor acc (Nat.shiftLeft (nat_lit 255) (Nat.mul (nat_lit 20) s)))
    (nat_lit 0)

theorem lines_sound {cs : List Char} {LS : List (List Int)} (h : linesK cs LS = true) :
    ∀ k < LS.length, parseInts (((String.ofList cs).splitOn "\n").getD k "") = LS.getD k [] := by
  intro k hk
  obtain ⟨hk', e⟩ := CFSG.KS.SporSch.LyTxt.lines_inv cs [] LS h k hk
  rw [CFSG.KS.SporSch.LyTxt.splitOn_nl, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some,
    CFSG.KS.SporSch.LyTxt.parseInts_ofList, e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    Option.getD_some]

theorem digRun_spec (DG : Nat) (cs : List Char) : ∀ i, digRun cs DG i ≠ 1048576 →
    digRun cs DG i = i + (cs.filter (· != '\n')).length ∧
      ∀ k (hk : k < (cs.filter (· != '\n')).length),
        ((cs.filter (· != '\n'))[k]).toNat - 48 = fld(DG, 4 * (i + k), 15) := by
  induction cs with
  | nil => intro i _; exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
  | cons ch cs ih =>
    intro i hi
    have e : digRun (ch :: cs) DG i = CFSG.KC.Enum.strictN (Char.toNat ch) (fun c =>
        nIf(Nat.beq c (nat_lit 10), digRun cs DG i,
          nIf(bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 57),
              Nat.beq (Nat.sub c (nat_lit 48)) fld(DG, Nat.mul (nat_lit 4) i, nat_lit 15))),
            digRun cs DG (Nat.succ i), nat_lit 1048576))) := rfl
    rw [e, strictN_valL, nIf_eqL, nIf_eqL, bAnd_eqL, bAnd_eqL] at hi ⊢
    by_cases h10 : ch = '\n'
    · have hb : Nat.beq ch.toNat 10 = true := by rw [h10]; rfl
      rw [ite_eq_left hb] at hi ⊢
      have ef : (ch :: cs).filter (· != '\n') = cs.filter (· != '\n') := by
        rw [List.filter_cons_of_neg (by simp [h10])]
      rw [ef]
      exact ih i hi
    · have hb : ¬ Nat.beq ch.toNat 10 = true := by
        rw [Nat.beq_eq]
        exact fun e => h10 (Char.toNat_inj.1 e)
      rw [ite_eq_right hb] at hi ⊢
      have ef : (ch :: cs).filter (· != '\n') = ch :: cs.filter (· != '\n') := by
        rw [List.filter_cons_of_pos (by simpa using h10)]
      by_cases hd : (Nat.ble 48 ch.toNat && (Nat.ble ch.toNat 57 &&
          Nat.beq (Nat.sub ch.toNat 48) (Nat.land (Nat.shiftRight DG (Nat.mul 4 i)) 15))) = true
      · rw [ite_eq_left hd] at hi ⊢
        obtain ⟨h1, h2⟩ := ih (i + 1) hi
        rw [ef]
        simp only [Bool.and_eq_true, Nat.beq_eq] at hd
        refine ⟨by rw [h1, List.length_cons]; omega, fun k hk => ?_⟩
        rcases k with _ | k
        · simp only [List.getElem_cons_zero, Nat.add_zero]
          exact hd.2.2
        · simp only [List.getElem_cons_succ]
          rw [h2 k (by simpa using hk)]
          congr 2
          omega
      · rw [ite_eq_right hd] at hi
        exact absurd rfl hi

theorem digits_sound {cs : List Char} {DG n : Nat} (h : digK cs DG n = true)
    (hn : n < 1048576) :
    digitsTxt (String.ofList cs) = Array.ofFn (n := n) fun i => fld(DG, 4 * i.val, 15) := by
  have hr : digRun cs DG 0 = n := Nat.eq_of_beq_eq_true h
  obtain ⟨h1, h2⟩ := digRun_spec DG cs 0 (by omega)
  rw [hr, Nat.zero_add] at h1
  unfold digitsTxt digitsOf
  have hl : ((String.ofList cs).replace "\n" "").toList = cs.filter (· != '\n') := by
    rw [CFSG.KS.SporSch.StrNl.replace_nl, String.toList_ofList]
  rw [hl]
  apply Array.ext
  · simp [h1]
  · intro k k1 k2
    have hk : k < (cs.filter (· != '\n')).length := by simpa using k1
    simp only [Array.getElem_map, List.getElem_toArray, Array.getElem_ofFn]
    have e3 := h2 k hk
    rw [Nat.zero_add] at e3
    exact e3

private theorem padU_isPad {w S UP : Nat} (hUP : unpackL 111 w S UP = padU uArr) :
    CFSG.KS.SporSch.LySvM.IsPad (unpackL 111 w S UP) := by
  intro i hi j hj
  rw [hUP]
  unfold padU
  rw [ofFn_get! _ hi, ofFn_get! _ hj]

theorem restr_eq {w S T L H CM RM ONE LV HV X UP : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : unpackL 111 w S UP = padU uArr) :
    restrArr (unpackL 111 w S X) = Array.ofFn (n := 49) fun t =>
      fld(mulR 5 w S 111 T L H CM RM X UP, S * (t.val / 7) + w * (t.val % 7), 2 ^ w - 1) :=
  CFSG.KS.SporSch.LySvM.restr_eqL hc hX hU (padU_isPad hUP)

theorem stab_eq {w S T L H CM RM ONE LV HV X UP : Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : unpackL 111 w S UP = padU uArr) :
    stabOK (unpackL 111 w S X) = Nat.beq (mulR 5 w S 111 T L H CM RM X UP)
      (mulR 5 w S 111 T L H CM RM UP (Nat.land (mulR 5 w S 111 T L H CM RM X UP) (2 ^ (7 * S) - 1))) :=
  CFSG.KS.SporSch.LySvM.stab_eqL hc hX hU (padU_isPad hUP)

theorem actKey_fix {w S T L H CM RM ONE LV HV X UP : Nat} {K : ByteArray}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hX : validM 5 (111 * S) L H X = true) (hU : validM 5 (111 * S) L H UP = true)
    (hUP : unpackL 111 w S UP = padU uArr)
    (hK : K.size = 276 ∧ (∀ q < 276, (K.get! q).toNat < 125) ∧
      rrefOK (keyRows K) #[0, 1, 2, 3, 4, 5, 6] = true ∧ keyDigit K 826 = 0 ∧ keyDigit K 827 = 0 ∧
      ∀ j < 111, ∀ m < 7, (uArr[j]!)[m]! = keyDigit K (111 * m + j))
    (hst : stabOK (unpackL 111 w S X) = true)
    (hR : mul7 (restrArr (unpackL 111 w S X)) (inv7 (restrArr (unpackL 111 w S X))) = id7 ())
    (hS : congr7 (restrArr (unpackL 111 w S X)) (keyS K) = keyS K) :
    actKey (frTable (unpackL 111 w S X)) K = some K :=
  CFSG.KS.SporSch.LySvM.actKey_fixL hc hX hU (padU_isPad hUP) hK hst hR hS

theorem vbfs_sound {kg c nS Hh : Nat} {GP E PL C : Nat → Nat} {root : Array Nat}
    {gens : Array (Array Nat)} (hg : gens.size = kg ∧ ∀ j < kg, gens[j]! = dec49 (GP j))
    (hroot : root = dec7 (E 0)) (hE0 : ∀ r < 7, d3 (E 0) r < 5) (hPL0 : PL 0 = 0)
    (hc : c ≤ 78125) (hcov : c ≤ nS * Hh)
    (hC0 : C 0 = 1 + 2 ^ 20 * 2 ^ code7K (E 0))
    (hrun : ∀ q < nS, vRun GP E PL kg c (q * Hh) Hh (C q) = C (q + 1))
    (hCn : Nat.land (C nS) 1048575 = c) :
    vecBFS root gens = (Array.ofFn (n := c) fun i => dec7 (E i.val),
        Array.ofFn (n := c) fun i => Nat.land (PL i.val) 1048575,
        Array.ofFn (n := c) fun i => Nat.shiftRight (PL i.val) 20) ∧
      vecTreeOK root gens (Array.ofFn (n := c) fun i => dec7 (E i.val),
        Array.ofFn (n := c) fun i => Nat.land (PL i.val) 1048575,
        Array.ofFn (n := c) fun i => Nat.shiftRight (PL i.val) 20) = true :=
  CFSG.KS.SporSch.LySvB.vbfs_soundL hg hroot hE0 hPL0 hc hcov hC0 hrun hCn

theorem cbfs_sound {kg c nS Hh cap QM : Nat} {KC ET WT PT SO SOI C : Nat → Nat} {root : Array Nat}
    {gens : Array (Array Nat × Array Nat)} (hg : gens.size = kg) (hkg : kg ≤ 5)
    (hK : ∀ j < kg, ∀ t < 49, ∀ s < 49, fld(KC t, 980 * j + 20 * s, 1048575) =
      gens[j]!.1[7 * (s / 7) + t / 7]! * gens[j]!.2[7 * (t % 7) + s % 7]! % 5)
    (hKb : ∀ t < 49, KC t < 2 ^ (980 * kg)) (hQM : QM = qmK (49 * kg))
    (hroot : root = dec49 (rowR ET 147 0)) (hE0 : ∀ t < 49, d3 (rowR ET 147 0) t < 5)
    (hPT0 : rowR PT 24 0 = 0)
    (hsort : ∀ i < c, sortB (fun i => rowR ET 147 i) SO SOI c i = true)
    (hc : c < 524288) (hcap : c ≤ cap) (hcov : c ≤ nS * Hh) (hC0 : C 0 = 1)
    (hrun : ∀ q < nS, cRun KC QM ET WT PT kg c (q * Hh) Hh (C q) = C (q + 1)) (hCn : C nS = c) :
    conjBFS root gens cap = (Array.ofFn (n := c) fun i => dec49 (rowR ET 147 i.val),
        Array.ofFn (n := c) fun i => Nat.land (rowR PT 24 i.val) 524287,
        Array.ofFn (n := c) fun i => Nat.shiftRight (rowR PT 24 i.val) 19) ∧
      conjTreeOK root gens (Array.ofFn (n := c) fun i => dec49 (rowR ET 147 i.val),
        Array.ofFn (n := c) fun i => Nat.land (rowR PT 24 i.val) 524287,
        Array.ofFn (n := c) fun i => Nat.shiftRight (rowR PT 24 i.val) 19) = true :=
  CFSG.KS.SporSch.LySvC.cbfs_soundL hg hK hKb hQM hroot hE0 hPT0 hsort hc hcap hcov hC0 hrun hCn

end CFSG.KS.SporSch.LySev

end
