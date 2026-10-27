module

public import Certificates.Data.Kernel.SurjKChain
public import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.Certificates.Kernel.VecKRegs

public section

namespace CFSG.KC.SurjChain

open CFSG.KC.VecK CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.SurjK
open CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native
open CFSG.KS (lget)

variable {d n : Nat} {p : Nat → Nat}

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem lget_eq : ∀ (L : List Nat) (k : Nat), lget L k = L.getD k 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => lget_eq L k

theorem real_ext (hP : VPts d n p) {T T' : Table} {N : Nat} (h : Realizes d n p T N)
    (h' : Realizes d n p T' N) : T = T' := by
  apply Array.ext (by rw [h.1, h'.1])
  intro i h1 h2
  have hi : i < n := by rw [← h.1]; exact h1
  have e : ap T i = ap T' i :=
    hP.inj _ (h.2 i hi).1 _ (h'.2 i hi).1 (by rw [(h.2 i hi).2, (h'.2 i hi).2])
  unfold ap at e
  rw [getElem!_pos T i h1, getElem!_pos T' i h2] at e
  exact UInt32.toNat_inj.1 e

theorem real_word (hP : VPts d n p) (F : Int → Nat) (L : Int → Table) :
    ∀ w : List Int, (∀ z ∈ w, Realizes d n p (L z) (F z)) →
      Realizes d n p (wordT n L w) (wordRF d F w)
  | [], _ => by
    unfold wordT
    exact real_id hP
  | z :: w, h => by
    have e1 : wordT n L (z :: w) = (wordT n L w).map fun t => (L z)[t.toNat]! := by
      unfold wordT
      rfl
    have e2 : wordRF d F (z :: w) = mulF d (wordRF d F w) (F z) := strictN_app _ _
    rw [e1, e2]
    have hw := real_word hP F L w fun y hy => h y (List.mem_cons_of_mem z hy)
    have hz := h z List.mem_cons_self
    refine ⟨by simp [hw.1], fun i hi => ?_⟩
    have e : ap ((wordT n L w).map fun t => (L z)[t.toNat]!) i = ap (L z) (ap (wordT n L w) i) := by
      unfold ap
      rw [getElem!_pos _ i (by simpa [hw.1] using hi), Array.getElem_map,
        ← getElem!_pos (wordT n L w) i (by rw [hw.1]; exact hi)]
    rw [e]
    obtain ⟨q1, q2⟩ := hw.2 i hi
    obtain ⟨p1, p2⟩ := hz.2 _ q1
    exact ⟨p1, by rw [p2, q2, vmF_mulF]⟩

theorem rec_ifN' (c : Bool) (t e : Nat) : (Bool.rec (motive := fun _ => Nat) e t c) = cond c t e := by
  cases c <;> rfl

theorem wordChecks_of_real (hP : VPts d n p) {S : Spec} {G : Array Table} {LMf : Nat → Nat}
    (hG : ∀ l < G.size, Realizes d n p G[l]! (LMf l)) {α β : Table} {NA NB : Nat}
    (hα : Realizes d n p α NA) (hβ : Realizes d n p β NB) {Li Ls : List (List Int)}
    {Ims ImsI : List Nat}
    (hi : S.imgWords = Li.toArray) (hs : S.surjWords = Ls.toArray) (hli : Li.length = S.m)
    (hls : Ls.length = 2)
    (hbase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z.toNat < G.size)) = true)
    (himg : ∀ k < S.m, wordRF d (fun z => LMf z.toNat) (Li.getD k []) = lget Ims k)
    (hinv : ∀ k < S.m, Nat.beq (mulF d (lget Ims k) (lget ImsI k)) (idF d) = true)
    (hrel : S.rels.all (fun r => r.all (fun l => decide (l.1 < S.m)) &&
      Nat.beq (wordRF d (imgF Ims ImsI) (r.map letterOf)) (idF d)) = true)
    (hsl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ S.m)) = true)
    (hsA : wordRF d (imgF Ims ImsI) (Ls.getD 0 []) = NA)
    (hsB : wordRF d (imgF Ims ImsI) (Ls.getD 1 []) = NB) :
    wordChecks n S G α β = true := by
  have hLi : ∀ k < S.m, ∀ z ∈ Li.getD k [], 0 ≤ z ∧ z.toNat < G.size := by
    intro k hk z hz
    have hmem : Li.getD k [] ∈ Li := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 hbase _ hmem) z hz
    simpa using h2
  have hbl : ∀ z : Int, 0 ≤ z → z.toNat < G.size →
      Realizes d n p (baseLetter G z) (LMf z.toNat) := fun z _ hz => hG _ hz
  unfold wordChecks inverseChecks
  have hIeq : S.imgWords.map (wordT n (baseLetter G)) = (Li.map (wordT n (baseLetter G))).toArray := by
    rw [hi, List.map_toArray]
  have hIk : ∀ k < S.m, (S.imgWords.map (wordT n (baseLetter G)))[k]! =
      wordT n (baseLetter G) (Li.getD k []) := by
    intro k hk
    have hk' : k < Li.length := by omega
    rw [hIeq, getElem!_pos _ k (by simp; omega), List.getD_eq_getElem _ _ hk']
    simp
  have hRI : ∀ k < S.m, Realizes d n p (S.imgWords.map (wordT n (baseLetter G)))[k]! (lget Ims k) := by
    intro k hk
    rw [hIk k hk, ← himg k hk]
    exact real_word hP _ _ _ fun z hz => hbl z (hLi k hk z hz).1 (hLi k hk z hz).2
  have hIsize : (S.imgWords.map (wordT n (baseLetter G))).size = S.m := by
    rw [hIeq]
    simpa using hli
  generalize S.imgWords.map (wordT n (baseLetter G)) = I at hRI hIsize ⊢
  have hIv : ∀ k < S.m, Realizes d n p (I.map (invT n))[k]! (lget ImsI k) ∧
      invOK n I[k]! (I.map (invT n))[k]! = true := by
    intro k hk
    have e : (I.map (invT n))[k]! = invT n I[k]! := by
      rw [getElem!_pos _ k (by simp; omega), Array.getElem_map, ← getElem!_pos I k (by omega)]
    rw [e]
    exact real_inv hP (hRI k hk) fun v hv => vmF_inv (hinv k hk) hv
  have hlet : ∀ z : Int, z ≠ 0 → z.natAbs ≤ S.m →
      Realizes d n p (imgLetter I (I.map (invT n)) z) (imgF Ims ImsI z) := by
    intro z hz0 hzm
    unfold imgF imgLetter
    have hb : Nat.blt 0 z.natAbs = true := by simp [Nat.blt_eq]; omega
    simp only [rec_ifN', hb, cond_true]
    by_cases h : 0 < z
    · have e : (z - 1).toNat = z.natAbs - 1 := by omega
      simp only [h, decide_true, cond_true, if_true, e]
      exact hRI _ (by omega)
    · have e : (-z - 1).toNat = z.natAbs - 1 := by omega
      simp only [h, decide_false, cond_false, if_false, e]
      exact (hIv _ (by omega)).1
  have hrels : ∀ r ∈ S.rels, (∀ l ∈ r, l.1 < S.m) ∧
      wordRF d (imgF Ims ImsI) (r.map letterOf) = idF d := by
    intro r hr
    have h := List.all_eq_true.1 hrel r hr
    rw [Bool.and_eq_true] at h
    exact ⟨fun l hl => by simpa using List.all_eq_true.1 h.1 l hl, Nat.eq_of_beq_eq_true h.2⟩
  have hrelL : ∀ r ∈ S.rels, ∀ z ∈ r.map letterOf, z ≠ 0 ∧ z.natAbs ≤ S.m := by
    intro r hr z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    have := (hrels r hr).1 l hl
    unfold letterOf
    split <;> omega
  have hsw : ∀ k, k < 2 → S.surjWords[k]! = Ls.getD k [] := by
    intro k hk
    have hk' : k < Ls.length := by omega
    rw [hs, getElem!_pos _ k (by simp; omega), List.getD_eq_getElem _ _ hk']
    simp
  have hslL : ∀ k, k < 2 → ∀ z ∈ Ls.getD k [], z ≠ 0 ∧ z.natAbs ≤ S.m := by
    intro k hk z hz
    have hmem : Ls.getD k [] ∈ Ls := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 hsl _ hmem) z hz
    simpa using h2
  have hid : Realizes d n p (idT n) (idF d) := real_id hP
  unfold imageChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hi]; simpa using hli
  · rw [hs]; simpa using hls
  · exact List.all_eq_true.2 fun r hr => List.all_eq_true.2 fun l hl => by
      simpa using (hrels r hr).1 l hl
  · rw [hi, List.all_toArray]
    exact hbase
  · rw [hs, List.all_toArray]; exact hsl
  · exact List.all_eq_true.2 fun k hk => (hIv k (List.mem_range.1 hk)).2
  · refine List.all_eq_true.2 fun r hr => ?_
    rw [beq_iff_eq]
    refine real_ext hP (real_word hP (imgF Ims ImsI) (imgLetter I (I.map (invT n))) _
      fun z hz => hlet z (hrelL r hr z hz).1 (hrelL r hr z hz).2) ?_
    rw [(hrels r hr).2]
    exact hid
  · rw [hsw 0 (by omega)]
    refine real_ext hP (real_word hP (imgF Ims ImsI) (imgLetter I (I.map (invT n))) _
      fun z hz => hlet z (hslL 0 (by omega) z hz).1 (hslL 0 (by omega) z hz).2) ?_
    rw [hsA]
    exact hα
  · rw [hsw 1 (by omega)]
    refine real_ext hP (real_word hP (imgF Ims ImsI) (imgLetter I (I.map (invT n))) _
      fun z hz => hlet z (hslL 1 (by omega) z hz).1 (hslL 1 (by omega) z hz).2) ?_
    rw [hsB]
    exact hβ

theorem chainLetter_sound (D : VecData) (S : Spec) {csA csB : List Char}
    {MA MB NA NB NAi NBi kL : Nat} {P AT BT FO Sx IP SP : Nat → Nat} {R V LM : List Nat}
    (hA : D.seedA = String.ofList csA) (hB : D.seedB = String.ofList csB)
    (hseed : seedK csA csB D.d MA MB NA NB D.expA D.expB = true)
    (hAi : Nat.beq (mulF D.d NA NAi) (idF D.d) = true) (hBi : Nat.beq (mulF D.d NB NBi) (idF D.d) = true)
    (hn : andB (Nat.blt (nat_lit 0) D.n) (Nat.blt D.n (pw2 (nat_lit 30))) = true)
    (hP0 : Nat.beq (lk P (nat_lit 32) (nat_lit 0)) D.v0 = true)
    (horb : ∀ h < D.n, orbAt D.d D.n NA NB P AT BT h = true)
    (hbfs : ∀ h < D.n, bfsAt D.n AT BT FO h = true)
    (hsort : ∀ h < D.n, sortAt D.n P Sx IP SP h = true)
    (hregs : andB (Nat.ble (nat_lit 2) D.nregs) (andB (allL (instrLtK D.nregs) D.prog)
      (allL (fun s => Nat.blt s D.nregs) D.sel.toList)) = true)
    (hslp : slpOK D.d D.prog (regs0N D.d D.nregs (wordN D.d NA NAi NB NBi D.w0)
      (wordN D.d NA NAi NB NBi D.w1)) V R = true)
    (hkL : Nat.beq kL (Nat.mul (nat_lit 2) D.sel.size) = true)
    (hlet : lettersK D.d R D.sel.toList LM = true)
    {Li Ls : List (List Int)} {Ims ImsI : List Nat}
    (hi : S.imgWords = Li.toArray) (hs : S.surjWords = Ls.toArray) (hli : Li.length = S.m)
    (hls : Ls.length = 2)
    (hbase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z.toNat < kL)) = true)
    (himg : ∀ k < S.m, wordRF D.d (chainF LM) (Li.getD k []) = lget Ims k)
    (hinv : ∀ k < S.m, Nat.beq (mulF D.d (lget Ims k) (lget ImsI k)) (idF D.d) = true)
    (hrel : S.rels.all (fun r => r.all (fun l => decide (l.1 < S.m)) &&
      Nat.beq (wordRF D.d (imgF Ims ImsI) (r.map letterOf)) (idF D.d)) = true)
    (hsl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ S.m)) = true)
    (hsA : wordRF D.d (imgF Ims ImsI) (Ls.getD 0 []) = NA)
    (hsB : wordRF D.d (imgF Ims ImsI) (Ls.getD 1 []) = NB) :
    chainLetterChecks D S = true := by
  have hP := vpts_of hn horb hsort
  obtain ⟨hsz, hL⟩ := letters_real D hA hB hseed hAi hBi hn hP0 horb hbfs hsort hregs hslp hkL hlet
  obtain ⟨ha, hb⟩ := orbit_real D hA hB hseed hn hP0 horb hbfs hsort
  unfold chainLetterChecks
  dsimp only
  refine wordChecks_of_real hP (LMf := getL 0 LM) (fun l hl => hL l (hsz ▸ hl)) ha hb hi hs hli hls
    ?_ himg hinv hrel hsl hsA hsB
  rw [hsz]
  exact hbase

end CFSG.KC.SurjChain

end
