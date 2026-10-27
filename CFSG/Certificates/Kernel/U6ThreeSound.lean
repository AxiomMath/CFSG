module

public import Certificates.Data.Kernel.U6Three.Defs
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.U6Three

open CFSG.RankThree.PartOne.F106

private theorem dig_enc (x : U6Mon) :
    dig (enc x) 0 = x.d0.val ∧ dig (enc x) 1 = x.d1.val ∧ dig (enc x) 2 = x.d2.val ∧
      dig (enc x) 3 = x.d3.val ∧ dig (enc x) 4 = x.d4.val ∧ dig (enc x) 5 = x.d5.val ∧
      dig (enc x) 6 = x.t0.val ∧ dig (enc x) 7 = x.t1.val := by
  have h0 := ZMod.val_lt x.d0
  have h1 := ZMod.val_lt x.d1
  have h2 := ZMod.val_lt x.d2
  have h3 := ZMod.val_lt x.d3
  have h4 := ZMod.val_lt x.d4
  have h5 := ZMod.val_lt x.d5
  have h6 := ZMod.val_lt x.t0
  have h7 := ZMod.val_lt x.t1
  simp only [dig, enc, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem dig_enc_6 (x : U6Mon) : dig (enc x) 6 = x.t0.val := (dig_enc x).2.2.2.2.2.2.1

theorem dig_enc_7 (x : U6Mon) : dig (enc x) 7 = x.t1.val := (dig_enc x).2.2.2.2.2.2.2

theorem d_val (x : U6Mon) (k : Fin 6) : (x.d k).val = dig (enc x) k.val := by
  obtain ⟨e0, e1, e2, e3, e4, e5, -, -⟩ := dig_enc x
  fin_cases k
  · exact e0.symm
  · exact e1.symm
  · exact e2.symm
  · exact e3.symm
  · exact e4.symm
  · exact e5.symm

private theorem perm_key : ∀ (t₀ t₁ : ZMod 3) (k : Fin 6), (u6Perm (-![t₀, t₁]) k).val =
    3 * (k.val / 3) + (k.val % 3 + 2 * (if k.val < 3 then t₀ else t₁).val) % 3 := by
  decide +kernel

theorem perm_val (x : U6Mon) (k : Fin 6) : (u6Perm (-x.t) k).val = pk (enc x) k.val := by
  have ht : x.t = ![x.t0, x.t1] := rfl
  rw [ht, perm_key]
  unfold pk
  fin_cases k <;> simp [dig_enc_6, dig_enc_7]

private theorem val_sub3 : ∀ a b : ZMod 3, (a - b).val = (a.val + 2 * b.val) % 3 := by
  decide

theorem raw_val (x y : U6Mon) (k : Fin 6) :
    (x.raw y k).val = rawN (enc x) (enc y) k.val := by
  unfold U6Mon.raw
  rw [ZMod.val_add, d_val, d_val, perm_val]
  rfl

theorem enc_mul (x y : U6Mon) : enc (x.mul y) = mulN (enc x) (enc y) := by
  have h : ∀ k : Fin 6, (x.raw y k - x.raw y 0).val = outD (enc x) (enc y) k.val := fun k => by
    rw [val_sub3, raw_val, raw_val]
    rfl
  have h6 : (x.t0 + y.t0).val = (dig (enc x) 6 + dig (enc y) 6) % 3 := by
    rw [ZMod.val_add, dig_enc_6, dig_enc_6]
  have h7 : (x.t1 + y.t1).val = (dig (enc x) 7 + dig (enc y) 7) % 3 := by
    rw [ZMod.val_add, dig_enc_7, dig_enc_7]
  have e : enc (x.mul y) = (x.raw y 0 - x.raw y 0).val + 3 * ((x.raw y 1 - x.raw y 0).val +
      3 * ((x.raw y 2 - x.raw y 0).val + 3 * ((x.raw y 3 - x.raw y 0).val +
      3 * ((x.raw y 4 - x.raw y 0).val + 3 * ((x.raw y 5 - x.raw y 0).val +
      3 * ((x.t0 + y.t0).val + 3 * (x.t1 + y.t1).val)))))) := rfl
  rw [e, h 0, h 1, h 2, h 3, h 4, h 5, h6, h7]
  rfl

theorem enc_inj {x y : U6Mon} (h : enc x = enc y) : x = y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := dig_enc x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := dig_enc y
  rw [h] at a0 a1 a2 a3 a4 a5 a6 a7
  cases x
  cases y
  simp only [U6Mon.mk.injEq]
  exact ⟨ZMod.val_injective _ (a0.symm.trans b0), ZMod.val_injective _ (a1.symm.trans b1),
    ZMod.val_injective _ (a2.symm.trans b2), ZMod.val_injective _ (a3.symm.trans b3),
    ZMod.val_injective _ (a4.symm.trans b4), ZMod.val_injective _ (a5.symm.trans b5),
    ZMod.val_injective _ (a6.symm.trans b6), ZMod.val_injective _ (a7.symm.trans b7)⟩

theorem decide_eq_beq (x y : U6Mon) : decide (x = y) = Nat.beq (enc x) (enc y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Nat.beq_eq]
  exact ⟨fun h => h ▸ rfl, enc_inj⟩

theorem enc_one : enc U6Mon.one = 0 := rfl

theorem enc_gen (k : Nat) : enc (U6Mon.gen k) = genC k := by
  by_cases hk : k < 6
  · interval_cases k <;> decide
  · have hg : U6Mon.gen k = U6Mon.one := by
      rw [U6Mon.gen, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [hg, enc_one, genC, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem enc_word (w : List Nat) (acc : U6Mon) :
    enc ((w.map U6Mon.gen).foldl U6Mon.mul acc) = wordN w (enc acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons k w ih =>
    rw [List.map_cons, List.foldl_cons, ih, enc_mul, enc_gen]
    rfl

theorem allIdx_spec {α : Type} (p : Nat → α → Bool) (L : List α) (n : Nat)
    (h : allIdx p L n = true) : ∀ m (hm : m < L.length), p (n + m) L[m] = true := by
  induction L generalizing n with
  | nil => intro m hm; simp at hm
  | cons a L ih =>
    have h' : (p n a && allIdx p L (n + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    intro m hm
    cases m with
    | zero => exact h'.1
    | succ m =>
      have := ih (n + 1) h'.2 m (by simpa using hm)
      rwa [show n + 1 + m = n + (m + 1) by omega] at this

theorem natAll_spec (p : Nat → Bool) (n : Nat) (h : natAll p n = true) :
    ∀ k, k < n → p k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have h' : (p n && natAll p n) = true := h
    rw [Bool.and_eq_true] at h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact ih h'.2 k hk
    · exact hk ▸ h'.1

private theorem getD_lt {α : Type} {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    l.getD i a = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem getD_ge {α : Type} {l : List α} {i : Nat} {a : α} (h : l.length ≤ i) :
    l.getD i a = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem tabN_lt {TP i : Nat} (h : i < 729) : tabN TP i = lk13 TP i := by
  have hb : Nat.blt i 729 = true := by simpa using h
  rw [tabN, hb]

theorem tabN_ge {TP i : Nat} (h : 729 ≤ i) : tabN TP i = 0 := by
  have hb : Nat.blt i 729 = false := by
    rcases hb : Nat.blt i 729
    · rfl
    · exact absurd (by simpa using hb) (by omega)
  rw [tabN, hb]

theorem invN_lt {IP i : Nat} (h : i < 729) : invN IP i = lk10 IP i := by
  have hb : Nat.blt i 729 = true := by simpa using h
  rw [invN, hb]

theorem invN_ge {IP i : Nat} (h : 729 ≤ i) : invN IP i = 0 := by
  have hb : Nat.blt i 729 = false := by
    rcases hb : Nat.blt i 729
    · rfl
    · exact absurd (by simpa using hb) (by omega)
  rw [invN, hb]

theorem enc_tab {TP : Nat} (hT : chkTab TP u6ThreePaths = true)
    (hP : u6ThreePaths.length = 729) (i : Nat) : enc (u6ThreeCert.tab i) = tabN TP i := by
  have hp : u6ThreeCert.paths = u6ThreePaths := rfl
  rw [U6SylowCert.tab, U6Mon.evalWord, enc_word, enc_one, hp]
  by_cases hi : i < 729
  · rw [tabN_lt hi, getD_lt (by omega)]
    have := allIdx_spec _ _ _ hT i (by omega)
    rw [Nat.zero_add] at this
    exact (Nat.eq_of_beq_eq_true this).symm
  · rw [tabN_ge (by omega), getD_ge (by omega)]
    rfl

theorem invv_eq {TP IP : Nat} (hI : chkInv TP IP u6ThreeInv = true)
    (hL : u6ThreeInv.length = 729) (u : Nat) : u6ThreeCert.invv u = invN IP u := by
  have hp : u6ThreeCert.inv = u6ThreeInv := rfl
  rw [U6SylowCert.invv, hp]
  by_cases hu : u < 729
  · rw [invN_lt hu, getD_lt (by omega)]
    have := allIdx_spec _ _ _ hI u (by omega)
    rw [Nat.zero_add, Bool.and_eq_true, Bool.and_eq_true] at this
    exact (Nat.eq_of_beq_eq_true this.1.1).symm
  · rw [invN_ge (by omega), getD_ge (by omega)]

theorem witOK_eq {TP IP : Nat} (hT : chkTab TP u6ThreePaths = true)
    (hP : u6ThreePaths.length = 729) (hI : chkInv TP IP u6ThreeInv = true)
    (hL : u6ThreeInv.length = 729) (i : Nat) (w : Wit) :
    u6ThreeCert.witOK i w = witN TP IP u6ThreeZl i w := by
  have etab := enc_tab hT hP
  have hcomm : ∀ a b, u6ThreeCert.commB a b = commN TP a b := fun a b => by
    rw [U6SylowCert.commB, decide_eq_beq, enc_mul, enc_mul, etab, etab, commN]
  have hconj : ∀ u, enc (u6ThreeCert.conjC i u) = conjN TP IP i u := fun u => by
    rw [U6SylowCert.conjC, enc_mul, enc_mul, etab, etab, etab, invv_eq hI hL, conjN]
  cases w with
  | exc => rfl
  | conj4 u₀ u₁ u₂ u₃ =>
    have hn : ([u₀, u₁, u₂, u₃].map (u6ThreeCert.conjC i)).Nodup ↔
        [conjN TP IP i u₀, conjN TP IP i u₁, conjN TP IP i u₂, conjN TP IP i u₃].Nodup :=
      (List.nodup_map_iff (f := enc) (l := [u₀, u₁, u₂, u₃].map (u6ThreeCert.conjC i))
        (fun _ _ h => enc_inj h)).symm.trans
        (by simp only [List.map_cons, List.map_nil, hconj])
    have hn' : decide ([u₀, u₁, u₂, u₃].map (u6ThreeCert.conjC i)).Nodup =
        decide [conjN TP IP i u₀, conjN TP IP i u₁, conjN TP IP i u₂, conjN TP IP i u₃].Nodup :=
      decide_eq_decide.mpr hn
    simp only [U6SylowCert.witOK, witN, hn']
  | pair z x y =>
    simp only [U6SylowCert.witOK, witN, hcomm]
  | cube z x =>
    have hc : decide (((u6ThreeCert.tab x).mul (u6ThreeCert.tab x)).mul (u6ThreeCert.tab x) ≠
        U6Mon.one) = !Nat.beq (mulN (mulN (tabN TP x) (tabN TP x)) (tabN TP x)) 0 := by
      simp only [ne_eq, decide_not]
      rw [decide_eq_beq, enc_mul, enc_mul, etab, enc_one]
    simp only [U6SylowCert.witOK, witN, hcomm, hc]

set_option maxRecDepth 4000 in
theorem check_of (TP IP JP : Nat)
    (hA : decide (u6ThreeCert.paths.length = 729) = true)
    (hB : decide (u6ThreeCert.paths.getD 0 [] = []) = true)
    (hC : (u6ThreeCert.paths.all fun p => p.all fun k => decide (k < 6)) = true)
    (hG : decide (u6ThreeCert.zl.length < 243) = true)
    (hL : (u6ThreeRt.length == 4374 && u6ThreeInv.length == 729 &&
      u6ThreeWit.length == 729) = true)
    (hT : chkTab TP u6ThreePaths = true) (hJ : chkInj TP JP = true)
    (hI : chkInv TP IP u6ThreeInv = true) (hR : chkRt TP u6ThreeRt = true)
    (hW : chkWit TP IP u6ThreeZl u6ThreeWit = true) : u6ThreeCert.check = true := by
  have hP : u6ThreePaths.length = 729 := of_decide_eq_true hA
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨⟨hLr, hLi⟩, hLw⟩ := hL
  have etab := enc_tab hT hP
  rw [U6SylowCert.check]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, ?_⟩, ?_⟩, ?_⟩, hG⟩, ?_⟩
  · apply decide_eq_true
    apply List.Nodup.of_map enc
    rw [List.map_map, show enc ∘ u6ThreeCert.tab = tabN TP from funext etab]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb hab
    rw [List.mem_range] at ha hb
    have h1 := Nat.eq_of_beq_eq_true (natAll_spec _ _ hJ a ha)
    have h2 := Nat.eq_of_beq_eq_true (natAll_spec _ _ hJ b hb)
    rw [tabN_lt ha, tabN_lt hb] at hab
    calc a = lk10 JP (lk13 TP a) := h1.symm
      _ = lk10 JP (lk13 TP b) := by rw [hab]
      _ = b := h2
  · simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
    intro i hi g hg
    have hn : 6 * i + g < u6ThreeRt.length := by omega
    have h := allIdx_spec _ _ _ hR _ hn
    rw [Nat.zero_add, Bool.and_eq_true, show (6 * i + g) / 6 = i by omega,
      show (6 * i + g) % 6 = g by omega] at h
    have hr : u6ThreeCert.rtv i g = u6ThreeRt[6 * i + g] := getD_lt hn
    rw [hr]
    refine ⟨decide_eq_true (by simpa using h.1), ?_⟩
    rw [decide_eq_beq, enc_mul, etab, etab, enc_gen]
    exact h.2
  · simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
    intro i hi
    have hn : i < u6ThreeInv.length := by omega
    have h := allIdx_spec _ _ _ hI _ hn
    rw [Nat.zero_add, Bool.and_eq_true, Bool.and_eq_true] at h
    have hv : u6ThreeCert.invv i = u6ThreeInv[i] := getD_lt hn
    rw [hv]
    refine ⟨decide_eq_true (by simpa using h.1.2), ?_⟩
    rw [decide_eq_beq, enc_mul, etab, etab, enc_one]
    exact h.2
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    have hn : i < u6ThreeWit.length := by omega
    have hw : u6ThreeCert.wit.getD i .exc = u6ThreeWit[i] := getD_lt hn
    rw [hw, witOK_eq hT hP hI hLi]
    have := allIdx_spec _ _ _ hW _ hn
    rwa [Nat.zero_add] at this

end CFSG.KC.U6Three
