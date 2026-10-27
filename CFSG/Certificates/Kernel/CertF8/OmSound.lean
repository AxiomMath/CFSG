module

public import Certificates.Data.Kernel.CertF8.Om
public import CFSG.Certificates.Kernel.CertF8.PackSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28OmAlg
public import Certificates.Data.ONanG28OmFacts
public import Certificates.Data.ONanG28Om

public section

namespace CFSG.KC.CertF8.Om

open CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.AGLEmbedding.KFactProofs.G28
open CFSG.KC.G28 (fld letB letB_eq codeP codeP_bit codeP_lt codeP_inj codeP_idCode idP
  testBit_of_lt)
open CFSG.KC.CertF8 (mulS6 wordS6 powS6 fld_lt fld_testBit codeP_mulCode6 codeP_wordCode6
  codeP_powCode6)

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by cases a <;> rfl

theorem allFrom_succ (lo c : ℕ) (f : ℕ → Bool) :
    allFrom lo (c + 1) f = andB (allFrom lo c f) (f (lo + c)) := rfl

theorem allFrom_iff (lo cnt : ℕ) (f : ℕ → Bool) :
    allFrom lo cnt f = true ↔ ∀ d < cnt, f (lo + d) = true := by
  induction cnt with
  | zero => exact ⟨fun _ d hd => absurd hd (Nat.not_lt_zero d), fun _ => rfl⟩
  | succ c ih =>
    rw [allFrom_succ, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ d hd
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with h | rfl
      · exact h1 d h
      · exact h2
    · intro h
      exact ⟨fun d hd => h d (by omega), h c (by omega)⟩

theorem all_of_chunks {c m N : ℕ} {f : ℕ → Bool} (hc : 0 < c) (hN : N ≤ c * m)
    (h : ∀ k < m, allFrom (Nat.mul c k) c f = true) : ∀ n < N, f n = true := by
  intro n hn
  have hk : n / c < m := by
    rw [Nat.div_lt_iff_lt_mul hc]
    rw [Nat.mul_comm] at hN
    omega
  have := (allFrom_iff _ _ _).1 (h (n / c) hk) (n % c) (Nat.mod_lt _ hc)
  rwa [show Nat.mul c (n / c) + n % c = n from Nat.div_add_mod n c] at this

@[expose] noncomputable def unpk (k : ℕ) : Array ℕ :=
  Array.ofFn (n := 36) fun t => fld k (3 * t.val) 3

theorem valid_unpk (k : ℕ) : Valid (unpk k) := by
  refine ⟨by simp [unpk], fun i hi => ?_⟩
  rw [unpk, getElem!_ofFn_nat' _ hi]
  simpa using fld_lt k (3 * i) 3

theorem codeP_unpk {k : ℕ} (hk : k < 2 ^ 108) : codeP (unpk k) = k := by
  apply Nat.eq_of_testBit_eq
  intro q
  have hq : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
  have hs : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases ht : q / 3 < 36
  · rw [hq, codeP_bit (valid_unpk k) _ _ hs, unpk, getElem!_ofFn_nat' _ ht, fld_testBit _ _ _ _ hs]
  · have h108 : 108 ≤ q := by omega
    rw [testBit_of_lt (codeP_lt (valid_unpk k)) h108, testBit_of_lt hk h108]

theorem keyM_eq : keyM = 2 ^ 108 - 1 := by decide +kernel

theorem keyK_lt (r : ℕ) : keyK r < 2 ^ 108 := by
  rw [keyK, keyM_eq]
  change r &&& (2 ^ 108 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem codeP_unpk_key (r : ℕ) : codeP (unpk (keyK r)) = keyK r := codeP_unpk (keyK_lt r)

theorem diagM_eq : diagM = codeP idCode := by
  rw [codeP_idCode]
  rfl

theorem idCode_entry : ∀ t < 36, idCode[t]! = if t % 7 = 0 then 1 else 0 := by decide

theorem codeP_invDiag {u : Array ℕ} (hu : Valid u) : codeP (invDiag u) = codeP u ^^^ diagM := by
  rw [diagM_eq]
  apply Nat.eq_of_testBit_eq
  intro q
  have hq : q = 3 * (q / 3) + q % 3 := (Nat.div_add_mod q 3).symm
  have hs : q % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [Nat.testBit_xor]
  by_cases ht : q / 3 < 36
  · rw [hq, codeP_bit (valid_invDiag hu) _ _ hs, codeP_bit hu _ _ hs,
      codeP_bit valid_idCode _ _ hs, getElem!_invDiag u ht, idCode_entry _ ht]
    split_ifs <;> simp [Nat.testBit_xor]
  · have h108 : 108 ≤ q := by omega
    rw [testBit_of_lt (codeP_lt (valid_invDiag hu)) h108, testBit_of_lt (codeP_lt hu) h108,
      testBit_of_lt (codeP_lt valid_idCode) h108]
    rfl

theorem codeP_canonCode {u : Array ℕ} (hu : Valid u) : codeP (canonCode u) = canonK (codeP u) := by
  have hb : Nat.land (codeP u) 1 = u[0]! % 2 := by
    change codeP u &&& 1 = _
    rw [Nat.and_one_is_mod]
    have h := codeP_bit hu 0 0 (by norm_num)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.testBit_zero, decide_eq_decide] at h
    have h1 := Nat.mod_two_eq_zero_or_one (codeP u)
    have h2 := Nat.mod_two_eq_zero_or_one (u[0]!)
    omega
  unfold canonCode canonK
  rw [hb]
  by_cases h : u[0]! % 2 = 0
  · rw [if_pos h, h]
    rfl
  · have h1 : u[0]! % 2 = 1 := by omega
    rw [if_neg h, h1, codeP_invDiag hu]
    rfl

theorem codeP_conj {G Gi c : Array ℕ} (hG : Valid G) (hGi : Valid Gi) (hc : Valid c) :
    codeP (canonCode (conjCode G Gi c)) = stepK (codeP G) (codeP Gi) (codeP c) := by
  have hv : Valid (conjCode G Gi c) := valid_mulCode (valid_mulCode hG hc) hGi
  rw [codeP_canonCode hv, conjCode, codeP_mulCode6 (valid_mulCode hG hc) hGi,
    codeP_mulCode6 hG hc]
  rfl

theorem codeP_foldl_arr {cs : Array (Array ℕ)} {f : ℕ → ℕ} (w : List ℕ)
    (hw : ∀ s ∈ w, Valid cs[s]! ∧ codeP cs[s]! = f s) {A : Array ℕ} (hA : Valid A) :
    Valid (w.foldl (fun A s => mulCode A cs[s]!) A) ∧
      codeP (w.foldl (fun A s => mulCode A cs[s]!) A) =
        w.foldl (fun x s => mulS6 x (f s)) (codeP A) := by
  induction w generalizing A with
  | nil => exact ⟨hA, rfl⟩
  | cons s w ih =>
    obtain ⟨h1, h2⟩ := hw s (by simp)
    simp only [List.foldl_cons]
    have := ih (fun s' hs' => hw s' (List.mem_cons_of_mem _ hs')) (valid_mulCode hA h1)
    rw [codeP_mulCode6 hA h1, h2] at this
    exact this

theorem rowAt_spec {T G : ℕ → ℕ} {nG wP lo n : ℕ} (h : rowAt T G nG wP lo n = true) :
    lo ≤ fld (T n) 108 wP ∧ fld (T n) 108 wP < n ∧ fld (T n) (108 + wP) 3 < nG ∧
      keyK (T n) = stepK (G (fld (T n) (108 + wP) 3)) (G (fld (T n) (108 + wP) 3 + nG))
        (keyK (T (fld (T n) 108 wP))) := by
  simp only [rowAt, letB_eq, andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq,
    Nat.add_eq] at h
  exact h

theorem sortAt_spec {T S : ℕ → ℕ} {N i : ℕ} (h : sortAt T S N i = true) :
    fld (S i) 108 17 < N ∧ keyK (T (fld (S i) 108 17)) = keyK (S i) ∧
      (i + 1 < N → keyK (S i) < keyK (S (i + 1))) := by
  simp only [sortAt, letB_eq, andB_eq, impB_eq, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq, Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun hi => ?_⟩
  rcases h3 with h3 | h3
  · exfalso
    have h4 : Nat.blt (i + 1) N = true := Nat.blt_eq.mpr hi
    simp_all
  · exact h3

theorem inj_of_sortAt {T S : ℕ → ℕ} {N : ℕ} (h : ∀ i < N, sortAt T S N i = true) :
    ∀ i < N, ∀ j < N, keyK (T i) = keyK (T j) → i = j := by
  classical
  have hs := fun i (hi : i < N) => sortAt_spec (h i hi)
  have hmono : ∀ i j, i < j → j < N → keyK (S i) < keyK (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact lt_trans (ih h' (by omega)) ((hs j (by omega)).2.2 hj)
      · exact (hs i (by omega)).2.2 hj
  have hkinj : ∀ a < N, ∀ b < N, keyK (S a) = keyK (S b) → a = b := by
    intro a ha b hb hab
    rcases Nat.lt_trichotomy a b with h' | h' | h'
    · exact absurd hab (ne_of_lt (hmono a b h' hb))
    · exact h'
    · exact absurd hab.symm (ne_of_lt (hmono b a h' ha))
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range N) (t := Finset.range N)
    (fun a _ => fld (S a) 108 17)
    (fun a ha => Finset.mem_range.2 (hs a (Finset.mem_range.1 ha)).1)
    (fun a b ha hb hab => hkinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) (by
      rw [← (hs a (Finset.mem_range.1 ha)).2.1, ← (hs b (Finset.mem_range.1 hb)).2.1]
      exact congrArg (fun p => keyK (T p)) hab))
    le_rfl
  intro i hi j hj hij
  obtain ⟨a, ha, rfl⟩ := hsurj i (Finset.mem_range.2 hi)
  obtain ⟨b, hb, rfl⟩ := hsurj j (Finset.mem_range.2 hj)
  have ha' := Finset.mem_range.1 ha
  have hb' := Finset.mem_range.1 hb
  rw [(hs a ha').2.1, (hs b hb').2.1] at hij
  rw [hkinj a ha' b hb' hij]

theorem loK_eq {k n : ℕ} (hk : k < 5) (h1 : omLo k ≤ n) (h2 : n < omLo (k + 1)) :
    loK n = omLo k := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := omLo_vals
  have hb : ∀ (b : Bool) (x y : ℕ), Bool.rec (motive := fun _ => ℕ) y x b =
      if b = true then x else y := by
    intro b x y
    cases b <;> rfl
  simp only [loK, hb, Nat.blt_eq]
  interval_cases k <;> simp only [e0, e1, e2, e3, e4, e5, Nat.reduceAdd] at h1 h2 ⊢ <;>
    split_ifs <;> omega

theorem omSc_code (hg : ∀ j < 4, gK j = wordS6 gW[j]! ∧ gK (j + 4) = wordS6 (gW[j]!).reverse)
    {s : ℕ} (hs : s < 8) : Valid omSc[s]! ∧ codeP omSc[s]! = gK s := by
  rw [omSc_getElem hs]
  by_cases h : s < 4
  · rw [if_pos h, codeP_wordCode6, (hg s h).1]
    exact ⟨valid_wordCode _, rfl⟩
  · rw [if_neg h, codeP_wordCode6, ← (hg (s - 4) (by omega)).2, Nat.sub_add_cancel (by omega)]
    exact ⟨valid_wordCode _, rfl⟩

theorem omSic_code (hg : ∀ j < 4, gK j = wordS6 gW[j]! ∧ gK (j + 4) = wordS6 (gW[j]!).reverse)
    {s : ℕ} (hs : s < 8) : Valid omSic[s]! ∧ codeP omSic[s]! = gK (Nat.mod (Nat.add s 4) 8) := by
  rw [omSic_getElem hs]
  by_cases h : s < 4
  · rw [if_pos h, codeP_wordCode6, ← (hg s h).2]
    refine ⟨valid_wordCode _, ?_⟩
    change gK (s + 4) = gK ((s + 4) % 8)
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h, codeP_wordCode6, ← (hg (s - 4) (by omega)).1]
    refine ⟨valid_wordCode _, ?_⟩
    change gK (s - 4) = gK ((s + 4) % 8)
    congr 1
    omega

theorem sch_code (hg : ∀ j < 4, gK j = wordS6 gW[j]! ∧ gK (j + 4) = wordS6 (gW[j]!).reverse)
    {w : List ℕ} (hw : ∀ s ∈ w, s < 8) :
    Valid (schCode omSc w) ∧ codeP (schCode omSc w) = symW w ∧
      Valid (schInv omSic w) ∧ codeP (schInv omSic w) = symWi w := by
  have h1 := codeP_foldl_arr (cs := omSc) (f := gK) w (fun s hs => omSc_code hg (hw s hs))
    valid_idCode
  have h2 := codeP_foldl_arr (cs := omSic) (f := fun s => gK (Nat.mod (Nat.add s 4) 8)) w.reverse
    (fun s hs => omSic_code hg (hw s (List.mem_reverse.1 hs))) valid_idCode
  rw [codeP_idCode] at h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

structure OmChecks (T S H HS : ℕ → ℕ) : Prop where
  gens : ∀ j < 4, gK j = wordS6 gW[j]! ∧ gK (j + 4) = wordS6 (gW[j]!).reverse
  hgens : ∀ t < 8, hK t = symW omSchW[t]! ∧ hK (t + 8) = symWi omSchW[t]!
  root0 : keyK (T 0) = canonK (powS6 (wordS6 tUW) 3)
  roots : ∀ k < 4, keyK (T ([1, 32320, 65152, 97984] : List ℕ)[k]!) =
    stepK (wordS6 omSeedW[k]!) (wordS6 (omSeedW[k]!).reverse) (powS6 (wordS6 tUW) 3)
  quad : Nat.xor (Nat.xor (mulS6 (powS6 (wordS6 tUW) 3) (powS6 (wordS6 tUW) 3))
    (powS6 (wordS6 tUW) 3)) idP = 0
  eps : ∀ j < 4, mulS6 (mulS6 (gK j) (powS6 (wordS6 tUW) 3)) (gK (j + 4)) =
    if j % 2 = 1 then mulS6 (powS6 (wordS6 tUW) 3) (powS6 (wordS6 tUW) 3)
      else powS6 (wordS6 tUW) 3
  seedrev : ∀ k < 4,
    mulS6 (wordS6 omSeedW[k]!) (wordS6 (omSeedW[k]!).reverse) = idP ∧
      mulS6 (wordS6 (omSeedW[k]!).reverse) (wordS6 omSeedW[k]!) = idP
  letters : omSchW.length = 8 ∧ ∀ w ∈ omSchW, ∀ s ∈ w, s < 8
  hroot : keyK (H 0) = keyK (T 3263)
  fix : allFrom 0 8
    (fun t => Nat.beq (stepK (hK t) (hK (Nat.add t 8)) (keyK (T 1))) (keyK (T 1))) = true
  forest : ∀ n < 130816, forestAt T n = true
  sorted : ∀ i < 130816, sortAt T S 130816 i = true
  htree : ∀ n < 1024, hAt H n = true
  hsorted : ∀ i < 1024, sortAt H HS 1024 i = true

@[expose] noncomputable def omCodesOf (T H : ℕ → ℕ) : OmCodes where
  pt n := unpk (keyK (T n))
  par n := fld (T n) 108 17
  sym n := fld (T n) 125 3
  seedW := omSeedW
  schW := omSchW
  c := 3263
  hpt n := unpk (keyK (H n))
  hpar n := fld (H n) 108 10
  hsym n := fld (H n) 118 3

theorem codeP_tzc : codeP tzc = powS6 (wordS6 tUW) 3 := by
  rw [tzc, tU, codeP_powCode6 (valid_wordCode _), codeP_wordCode6]

theorem omCodes_ok {T S H HS : ℕ → ℕ} (hc : OmChecks T S H HS) : (omCodesOf T H).OK := by
  have hz := codeP_tzc
  have hvz : Valid tzc := by
    rw [tzc, tU]
    exact valid_powCode (valid_wordCode _) 3
  have hvzz := valid_mulCode hvz hvz
  have hpt : ∀ (X : ℕ → ℕ) n, codeP (unpk (keyK (X n))) = keyK (X n) := fun X n =>
    codeP_unpk_key _
  have hsch : ∀ t < 8, ∀ c : Array ℕ, Valid c →
      codeP (canonCode (conjCode (schCode omSc omSchW[t]!) (schInv omSic omSchW[t]!) c)) =
        stepK (hK t) (hK (t + 8)) (codeP c) := by
    intro t ht c hcv
    have hmem : omSchW[t]! ∈ omSchW := by
      rw [getElem!_pos omSchW t (by rw [hc.letters.1]; exact ht)]
      exact List.getElem_mem _
    obtain ⟨h1, h2, h3, h4⟩ := sch_code hc.gens (hc.letters.2 _ hmem)
    rw [codeP_conj h1 h3 hcv, h2, h4, ← (hc.hgens t ht).1, ← (hc.hgens t ht).2]
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, hc.letters.1, hc.letters.2, ?_,
    (show (3263 : ℕ) < 130816 by norm_num), congrArg unpk hc.hroot, ?_, ?_⟩
  all_goals try dsimp only [omCodesOf]
  ·
    have hx : codeP (mulCode tzc tzc) ^^^ codeP tzc ^^^ codeP idCode = 0 := by
      rw [codeP_mulCode6 hvz hvz, hz, codeP_idCode]
      exact hc.quad
    intro t ht
    apply Nat.eq_of_testBit_eq
    intro s
    by_cases hs : s < 3
    · have e := congrArg (Nat.testBit · (3 * t + s)) hx
      simp only [Nat.testBit_xor, codeP_bit hvzz _ _ hs, codeP_bit hvz _ _ hs,
        codeP_bit valid_idCode _ _ hs, Nat.zero_testBit] at e
      simpa [Nat.testBit_xor] using e
    · have h8 : (mulCode tzc tzc)[t]! ^^^ tzc[t]! ^^^ idCode[t]! < 2 ^ 3 :=
        Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by simpa using hvzz.2 t ht)
          (by simpa using hvz.2 t ht)) (by simpa using valid_idCode.2 t ht)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h8 (Nat.pow_le_pow_right (by norm_num)
        (by omega))), Nat.zero_testBit]
  ·
    intro j hj
    have hl := valid_mulCode (valid_mulCode (valid_wordCode gW[j]!) hvz)
      (valid_wordCode (gW[j]!).reverse)
    have hr : Valid (if j % 2 = 1 then mulCode tzc tzc else tzc) := by
      split_ifs
      · exact hvzz
      · exact hvz
    apply codeP_inj hl hr
    rw [codeP_mulCode6 (valid_mulCode (valid_wordCode _) hvz) (valid_wordCode _),
      codeP_mulCode6 (valid_wordCode _) hvz, codeP_wordCode6, codeP_wordCode6, hz,
      ← (hc.gens j hj).1, ← (hc.gens j hj).2, hc.eps j hj]
    split_ifs
    · rw [codeP_mulCode6 hvz hvz, hz]
    · rw [hz]
  ·
    intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    have hk4 : k < 4 := by simpa [omSeedW] using hk
    rw [← getElem!_pos omSeedW k hk]
    obtain ⟨h1, h2⟩ := hc.seedrev k hk4
    refine ⟨codeP_inj (valid_mulCode (valid_wordCode _) (valid_wordCode _)) valid_idCode ?_,
      codeP_inj (valid_mulCode (valid_wordCode _) (valid_wordCode _)) valid_idCode ?_⟩
    · rw [codeP_mulCode6 (valid_wordCode _) (valid_wordCode _), codeP_wordCode6,
        codeP_wordCode6, codeP_idCode, h1]
    · rw [codeP_mulCode6 (valid_wordCode _) (valid_wordCode _), codeP_wordCode6,
        codeP_wordCode6, codeP_idCode, h2]
  ·
    apply codeP_inj (valid_unpk _) (valid_canonCode hvz)
    rw [codeP_canonCode hvz, hz]
    exact (hpt T 0).trans hc.root0
  ·
    intro k hk0 hk5
    have hidx : ([1, 32320, 65152, 97984] : List ℕ)[k - 1]! = omLo k := by
      interval_cases k <;> rfl
    have hv : Valid (conjCode (wordCode omSeedW[k - 1]!) (wordCode (omSeedW[k - 1]!).reverse)
        tzc) := valid_mulCode (valid_mulCode (valid_wordCode _) hvz) (valid_wordCode _)
    apply codeP_inj (valid_unpk _) (valid_canonCode hv)
    rw [codeP_conj (valid_wordCode _) (valid_wordCode _) hvz, codeP_wordCode6, codeP_wordCode6, hz,
      ← hc.roots (k - 1) (by omega), hidx]
    exact hpt T _
  ·
    intro k hk n h1 h2
    have hn : n < 130816 := lt_of_lt_of_le h2 (by interval_cases k <;> decide)
    have hf := hc.forest n hn
    have hb : Nat.beq n (omLo k) = false := by
      cases hb : Nat.beq n (omLo k)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
    simp only [forestAt, letB_eq, loK_eq hk (le_of_lt h1) h2, hb] at hf
    obtain ⟨hp1, hp2, hs, he⟩ := rowAt_spec hf
    simp only [Nat.reduceAdd] at hs he
    refine ⟨hp1, hp2, hs, ?_⟩
    have hv : Valid (conjCode (wordCode gW[fld (T n) 125 3]!)
        (wordCode (gW[fld (T n) 125 3]!).reverse) (unpk (keyK (T (fld (T n) 108 17))))) :=
      valid_mulCode (valid_mulCode (valid_wordCode _) (valid_unpk _)) (valid_wordCode _)
    apply codeP_inj (valid_unpk _) (valid_canonCode hv)
    rw [codeP_conj (valid_wordCode _) (valid_wordCode _) (valid_unpk _), codeP_wordCode6,
      codeP_wordCode6, ← (hc.gens _ hs).1, ← (hc.gens _ hs).2]
    change codeP (unpk (keyK (T n))) = stepK _ _ (codeP (unpk (keyK (T (fld (T n) 108 17)))))
    rw [hpt, hpt]
    exact he
  ·
    intro i hi j hj hij
    have e := congrArg codeP hij
    change codeP (unpk (keyK (T i))) = codeP (unpk (keyK (T j))) at e
    rw [hpt, hpt] at e
    exact inj_of_sortAt hc.sorted i hi j hj e
  ·
    intro w hw
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hw
    have ht8 : t < 8 := by rwa [hc.letters.1] at ht
    rw [← getElem!_pos omSchW t ht]
    have hf := (allFrom_iff _ _ _).1 hc.fix t ht8
    simp only [Nat.zero_add, Nat.beq_eq, Nat.add_eq] at hf
    have hw' : ∀ s ∈ omSchW[t]!, s < 8 := hc.letters.2 _ (by
      rw [getElem!_pos omSchW t ht]
      exact List.getElem_mem _)
    obtain ⟨h1, -, h3, -⟩ := sch_code hc.gens hw'
    have hv : Valid (conjCode (schCode omSc omSchW[t]!) (schInv omSic omSchW[t]!)
        (unpk (keyK (T 1)))) := valid_mulCode (valid_mulCode h1 (valid_unpk _)) h3
    apply codeP_inj (valid_canonCode hv) (valid_unpk _)
    rw [hsch t ht8 _ (valid_unpk _)]
    change stepK _ _ (codeP (unpk (keyK (T 1)))) = codeP (unpk (keyK (T 1)))
    rw [hpt]
    exact hf
  ·
    intro n hpos hn
    have hf := hc.htree n hn
    have hb : Nat.beq n 0 = false := by
      cases hb : Nat.beq n 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
    simp only [hAt, hb] at hf
    obtain ⟨-, hp2, hs, he⟩ := rowAt_spec hf
    simp only [Nat.reduceAdd] at hs he
    refine ⟨hp2, hs, ?_⟩
    have hw' : ∀ s ∈ omSchW[fld (H n) 118 3]!, s < 8 := hc.letters.2 _ (by
      rw [getElem!_pos omSchW _ (by rw [hc.letters.1]; exact hs)]
      exact List.getElem_mem _)
    obtain ⟨h1, -, h3, -⟩ := sch_code hc.gens hw'
    have hv : Valid (conjCode (schCode omSc omSchW[fld (H n) 118 3]!)
        (schInv omSic omSchW[fld (H n) 118 3]!) (unpk (keyK (H (fld (H n) 108 10))))) :=
      valid_mulCode (valid_mulCode h1 (valid_unpk _)) h3
    apply codeP_inj (valid_unpk _) (valid_canonCode hv)
    rw [hsch _ hs _ (valid_unpk _)]
    change codeP (unpk (keyK (H n))) = stepK _ _ (codeP (unpk (keyK (H (fld (H n) 108 10)))))
    rw [hpt, hpt]
    exact he
  ·
    intro i hi j hj hij
    have e := congrArg codeP hij
    change codeP (unpk (keyK (H i))) = codeP (unpk (keyK (H j))) at e
    rw [hpt, hpt] at e
    exact inj_of_sortAt hc.hsorted i hi j hj e

end CFSG.KC.CertF8.Om
