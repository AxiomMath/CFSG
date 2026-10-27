module

public import CFSG.Certificates.Kernel.Hall82K.SoundBase

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa CFSG.CGT.Hall82

theorem bitN_ite (m k : ℕ) : bitN m k = if m.testBit k = true then 1 else 0 := by
  have h := bitN_mul m k 1
  have e : Nat.mul (bitN m k) 1 = bitN m k := Nat.mul_one _
  rw [e] at h
  exact h

theorem testBit_eq_of_bitN {m k m' k' : ℕ} (h : bitN m k = bitN m' k') :
    m.testBit k = m'.testBit k' := by
  rw [bitN_ite, bitN_ite] at h
  revert h
  cases m.testBit k <;> cases m'.testBit k' <;> simp

theorem hallQ0_eq_testBit (hq0 : q0BridgeK = true) (k : Fin 64) :
    hallQ0 k = q0K.testBit k.val := by
  have h := beqB_eq_true.1 (allN_iff.1 hq0 k.val k.2)
  rw [nbeq_iff, bitN_eq_one_iff] at h
  exact Bool.eq_iff_iff.2 h

theorem q0_xor_iso (hq0 : q0BridgeK = true) {y : Fin 64 → Fin 64}
    (hy : ∀ k l, y (xorF k l) = xorF (y k) (y l)) (hiso : ∀ k, hallQ0 (y k) = hallQ0 k)
    (u w : Fin 64) : q0K.testBit ((y u).val ^^^ (y w).val) = q0K.testBit (u.val ^^^ w.val) := by
  have h := hiso (xorF u w)
  rw [hy, hallQ0_eq_testBit hq0, hallQ0_eq_testBit hq0, val_xorF, val_xorF] at h
  exact h

def bF (j : ℕ) : Fin 64 := ⟨(1 <<< j) % 64, Nat.mod_lt _ (by norm_num)⟩

theorem bF_facts : ∀ i < 6, bF i ≠ 0 ∧ hallQ0 (bF i) = false := by decide +kernel

theorem bF_xor : ∀ i < 6, ∀ j < 6,
    Nat.xor (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j) = (bF i).val ^^^ (bF j).val := by
  decide +kernel

theorem fullK_bit : ∀ x < 64, fullK.testBit x = true := by decide +kernel

theorem candBase_bit : ∀ x < 64, x ≠ 0 → q0K.testBit x = false →
    (Nat.sub (Nat.xor fullK q0K) 1).testBit x = true := by decide +kernel

theorem rowK_bit (hqt : qtBridgeK = true) {i j a x : ℕ} (ha : a < 64) (hx : x < 64)
    (h : q0K.testBit (x ^^^ a) = q0K.testBit (Nat.xor (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j))) :
    (rowK i j a).testBit x = true := by
  have hl : bitN (Nat.land (Nat.shiftRight qtK (Nat.shiftLeft a 6)) fullK) x =
      bitN q0K (x ^^^ a) := nbeq_iff.1 (allN_iff.1 (allN_iff.1 hqt a ha) x hx)
  have hr : rowK i j a = Nat.land (Nat.shiftRight qtK (Nat.shiftLeft a 6)) fullK ^^^
      (1 - bitN q0K (Nat.xor (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j))) * fullK := rfl
  rw [hr, Nat.testBit_xor, testBit_eq_of_bitN hl, h, bitN_ite]
  have hf := fullK_bit x hx
  cases q0K.testBit (Nat.xor (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j)) <;> simp [hf]

theorem candRec_bit (i P x : ℕ) (hb : (Nat.sub (Nat.xor fullK q0K) 1).testBit x = true) :
    ∀ m, (∀ j < m, (rowK i j (fld P (Nat.mul 6 j))).testBit x = true) →
      (Nat.rec (motive := fun _ => ℕ) (Nat.sub (Nat.xor fullK q0K) 1)
        (fun j ih => Nat.land ih (rowK i j (fld P (Nat.mul 6 j)))) m).testBit x = true := by
  intro m
  induction m with
  | zero => intro _; exact hb
  | succ m ih =>
    intro h
    change (Nat.land (Nat.rec (motive := fun _ => ℕ) (Nat.sub (Nat.xor fullK q0K) 1)
        (fun j ih => Nat.land ih (rowK i j (fld P (Nat.mul 6 j)))) m)
          (rowK i m (fld P (Nat.mul 6 m)))).testBit x = true
    have e : ∀ a b : ℕ, Nat.land a b = a &&& b := fun _ _ => rfl
    rw [e, Nat.testBit_and]
    exact Bool.and_eq_true_iff.2
      ⟨ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)⟩

theorem candRec_lt (i P : ℕ) : ∀ m, (Nat.rec (motive := fun _ => ℕ)
    (Nat.sub (Nat.xor fullK q0K) 1)
    (fun j ih => Nat.land ih (rowK i j (fld P (Nat.mul 6 j)))) m) < 2 ^ 64 := by
  intro m
  induction m with
  | zero =>
    change Nat.sub (Nat.xor fullK q0K) 1 < 2 ^ 64
    decide +kernel
  | succ m ih => exact Nat.lt_of_le_of_lt Nat.and_le_left ih

theorem cand_mem (hq0 : q0BridgeK = true) (hqt : qtBridgeK = true) {y : Fin 64 → Fin 64}
    (hy : ∀ k l, y (xorF k l) = xorF (y k) (y l)) (hiso : ∀ k, hallQ0 (y k) = hallQ0 k)
    (hnz : ∀ k, y k = 0 → k = 0) {i P : ℕ} (hi : i < 6)
    (hP : ∀ j < i, fld P (Nat.mul 6 j) = (y (bF j)).val) :
    bitN (candK i P) (y (bF i)).val = 1 := by
  rw [bitN_eq_one_iff]
  obtain ⟨hne, hq⟩ := bF_facts i hi
  refine candRec_bit i P _ ?_ i ?_
  · refine candBase_bit _ (y (bF i)).2 ?_ ?_
    · intro h0
      exact hne (hnz _ (Fin.ext h0))
    · rw [← hallQ0_eq_testBit hq0, hiso, hq]
  · intro j hj
    rw [hP j hj]
    refine rowK_bit hqt (y (bF j)).2 (y (bF i)).2 ?_
    rw [q0_xor_iso hq0 hy hiso, bF_xor i hi j (by omega)]

theorem srch_step (hidx : idxBridgeK = true) {n P x : ℕ} (h : srchK (n + 1) P = true)
    (hx : x < 64) (hb : bitN (candK (Nat.sub 5 n) P) x = 1) (s : ℕ)
    (hs : Nat.mul 6 (Nat.sub 5 n) = s) : srchK n (P ||| x <<< s) = true := by
  subst hs
  have h' : forBitsK (fun x => srchK n (Nat.lor P (Nat.shiftLeft x (Nat.mul 6 (Nat.sub 5 n)))))
      64 (candK (Nat.sub 5 n) P) = true := h
  exact forBitsK_sound hidx (candRec_lt _ P _) h' x hx hb

theorem lane1 {a0 a1 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) :
    a0 ||| a1 <<< 6 = enc6 a0 a1 0 0 0 0 := by
  rw [← lorTree_eq_enc6 (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0) h0 h1 (by norm_num)
    (by norm_num) (by norm_num)]
  simp only [Nat.zero_shiftLeft, Nat.or_zero, Nat.zero_or, Nat.or_assoc]

theorem lane2 {a0 a1 a2 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64) :
    (a0 ||| a1 <<< 6) ||| a2 <<< 12 = enc6 a0 a1 a2 0 0 0 := by
  rw [← lorTree_eq_enc6 (x3 := 0) (x4 := 0) (x5 := 0) h0 h1 h2 (by norm_num) (by norm_num)]
  simp only [Nat.zero_shiftLeft, Nat.or_zero, Nat.zero_or, Nat.or_assoc]

theorem lane3 {a0 a1 a2 a3 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64) (h3 : a3 < 64) :
    ((a0 ||| a1 <<< 6) ||| a2 <<< 12) ||| a3 <<< 18 = enc6 a0 a1 a2 a3 0 0 := by
  rw [← lorTree_eq_enc6 (x4 := 0) (x5 := 0) h0 h1 h2 h3 (by norm_num)]
  simp only [Nat.zero_shiftLeft, Nat.or_zero, Nat.zero_or, Nat.or_assoc]

theorem lane4 {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64) (h3 : a3 < 64)
    (h4 : a4 < 64) :
    (((a0 ||| a1 <<< 6) ||| a2 <<< 12) ||| a3 <<< 18) ||| a4 <<< 24 = enc6 a0 a1 a2 a3 a4 0 := by
  rw [← lorTree_eq_enc6 (x5 := 0) h0 h1 h2 h3 h4]
  simp only [Nat.zero_shiftLeft, Nat.or_zero, Nat.zero_or, Nat.or_assoc]

theorem lane5 {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 64) (h1 : a1 < 64) (h2 : a2 < 64)
    (h3 : a3 < 64) (h4 : a4 < 64) :
    ((((a0 ||| a1 <<< 6) ||| a2 <<< 12) ||| a3 <<< 18) ||| a4 <<< 24) ||| a5 <<< 30 =
      enc6 a0 a1 a2 a3 a4 a5 := by
  rw [← lorTree_eq_enc6 h0 h1 h2 h3 h4]
  simp only [Nat.or_assoc]

theorem add_comp {f g : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (hg : ∀ v w, g (xorF v w) = xorF (g v) (g w)) :
    ∀ v w, f (g (xorF v w)) = xorF (f (g v)) (f (g w)) := fun v w => by rw [hg, hf]

theorem orb_bit : ∀ l < 64, ¬ (l = 1 ∨ l = 4 ∨ l = 7) → Nat.land 146 (Nat.shiftLeft 1 l) = 0 := by
  decide +kernel

theorem noOrb3K_of {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (h : ∀ p, IsHallOrb p → ¬ IsHallOrb (f p)) :
    noOrb3K (f 1).val (f 2).val (f 4).val = true := by
  have h7e : (7 : Fin 64) = xorF (xorF 1 2) 4 := by decide
  have h1 := orb_bit _ (f 1).2 (h 1 (by decide))
  have h4 := orb_bit _ (f 4).2 (h 4 (by decide))
  have h7 := orb_bit _ (f 7).2 (h 7 (by decide))
  rw [h7e, hf, hf, val_xorF, val_xorF] at h7
  have e : ∀ a b c : ℕ, a = 0 → b = 0 → c = 0 → Nat.beq (Nat.lor a (Nat.lor b c)) 0 = true := by
    intro a b c ha hb hc
    subst ha hb hc
    rfl
  exact e _ _ _ h1 h4 h7

theorem goodK_of (hs40 : zipArrK s40K hallS40Arr = true) {f : Fin 64 → Fin 64}
    (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w)) (h : GoodHall f) : goodK (codeL f) = true := by
  obtain ⟨e0, e1, e2, -, -, -⟩ := fld_enc6 (f 1).2 (f 2).2 (f 4).2 (f 8).2 (f 16).2 (f 32).2
  have hc : codeL f = enc6 (f 1).val (f 2).val (f 4).val (f 8).val (f 16).val (f 32).val := rfl
  unfold goodK
  rw [bor_eq_true]
  rcases h with h | h
  · right
    exact memL_iff.2 ((mem_hallS40_iff hs40 hf).1 h)
  · left
    rw [hc, e0, e1, e2]
    exact noOrb3K_of hf h

theorem goodCK_of (hs40 : zipArrK s40K hallS40Arr = true) {A B : Fin 64 → Fin 64}
    (hA : ∀ v w, A (xorF v w) = xorF (A v) (A w)) (hB : ∀ v w, B (xorF v w) = xorF (B v) (B w))
    (h : GoodHall (fun v => A (B v))) : goodCK (codeL A) (codeL B) = true := by
  obtain ⟨e0, e1, e2, -, -, -⟩ := fld_enc6 (B 1).2 (B 2).2 (B 4).2 (B 8).2 (B 16).2 (B 32).2
  have hc : codeL B = enc6 (B 1).val (B 2).val (B 4).val (B 8).val (B 16).val (B 32).val := rfl
  have hAB := add_comp hA hB
  unfold goodCK
  rw [bor_eq_true]
  rcases h with h | h
  · right
    rw [compL_codeL hA]
    exact memL_iff.2 ((mem_hallS40_iff (z := fun v => A (B v)) hs40 hAB).1 h)
  · left
    rw [hc, e0, e1, e2, apL_codeL hA, apL_codeL hA, apL_codeL hA]
    exact noOrb3K_of (f := fun v => A (B v)) hAB h

theorem inWK_bit : ∀ v < 64, inWK v = true → bitN wK v = 1 := by decide +kernel

theorem inWK_mem (hw : wBridgeK = true) (v : Fin 64) (h : inWK v.val = true) : InHallW v := by
  have hb := beqB_eq_true.1 (allN_iff.1 hw v.val v.2)
  rw [memL_iff, nbeq_iff] at hb
  exact hb.2 (inWK_bit v.val v.2 h)

theorem wclosed : ∀ a ∈ hallWList, ∀ b ∈ hallWList, a ^^^ b ∈ hallWList := by decide +kernel

theorem hallW_cases : ∀ k : Fin 64, InHallW k → k = xorF 3 3 ∨ k = 3 ∨ k = 5 ∨ k = xorF 3 5 ∨
    k = 56 ∨ k = xorF 3 56 ∨ k = xorF 5 56 ∨ k = xorF (xorF 3 5) 56 := by
  decide +kernel

theorem reducible_of_checks (hidx : idxBridgeK = true) (hq0 : q0BridgeK = true)
    (hqt : qtBridgeK = true) (hw : wBridgeK = true)
    (hs40 : zipArrK s40K hallS40Arr = true)
    (hred : ∀ x, 1 ≤ x → x < 64 → bor (Nat.beq (bitN q0K x) 1) (srchK 5 x) = true) :
    ∀ y : Fin 64 → Fin 64, (∀ k l, y (xorF k l) = xorF (y k) (y l)) →
      (∀ k, hallQ0 (y k) = hallQ0 k) → (∀ k, y k = 0 → k = 0) → GoodHall y →
      (∀ t ∈ hallS40, GoodHall (y ∘ t ∘ y)) →
      (∀ t ∈ hallS40, ∀ u ∈ hallS40, GoodHall (y ∘ t ∘ y ∘ u ∘ y)) →
      ∀ k, InHallW k → InHallW (y k) := by
  intro y hy hiso hnz hG h2 h3
  have hl : ∀ j, (y (bF j)).val < 64 := fun j => (y (bF j)).2
  have z64 : (0 : ℕ) < 64 := by norm_num
  have hq00 : q0K.testBit (y (bF 0)).val = false := by
    rw [← hallQ0_eq_testBit hq0, hiso]
    exact (bF_facts 0 (by norm_num)).2
  have hne0 : (y (bF 0)).val ≠ 0 := fun h0 => (bF_facts 0 (by norm_num)).1 (hnz _ (Fin.ext h0))
  have r0 : srchK 5 (y (bF 0)).val = true := by
    rcases bor_eq_true.1 (hred _ (Nat.one_le_iff_ne_zero.2 hne0) (hl 0)) with h | h
    · rw [nbeq_iff, bitN_eq_one_iff, hq00] at h
      exact absurd h (by decide)
    · exact h
  have r1 := srch_step hidx (n := 4) r0 (hl 1)
    (cand_mem hq0 hqt hy hiso hnz (i := 1) (by norm_num) (by
      intro j hj
      obtain rfl : j = 0 := by omega
      exact fld_lt (hl 0))) 6 rfl
  have r2 := srch_step hidx (n := 3) r1 (hl 2)
    (cand_mem hq0 hqt hy hiso hnz (i := 2) (by norm_num) (by
      intro j hj
      rw [lane1 (hl 0) (hl 1)]
      obtain ⟨e0, e1, -, -, -, -⟩ := fld_enc6 (hl 0) (hl 1) z64 z64 z64 z64
      interval_cases j
      · exact e0
      · exact e1)) 12 rfl
  have r3 := srch_step hidx (n := 2) r2 (hl 3)
    (cand_mem hq0 hqt hy hiso hnz (i := 3) (by norm_num) (by
      intro j hj
      rw [lane2 (hl 0) (hl 1) (hl 2)]
      obtain ⟨e0, e1, e2, -, -, -⟩ := fld_enc6 (hl 0) (hl 1) (hl 2) z64 z64 z64
      interval_cases j
      · exact e0
      · exact e1
      · exact e2)) 18 rfl
  have r4 := srch_step hidx (n := 1) r3 (hl 4)
    (cand_mem hq0 hqt hy hiso hnz (i := 4) (by norm_num) (by
      intro j hj
      rw [lane3 (hl 0) (hl 1) (hl 2) (hl 3)]
      obtain ⟨e0, e1, e2, e3, -, -⟩ := fld_enc6 (hl 0) (hl 1) (hl 2) (hl 3) z64 z64
      interval_cases j
      · exact e0
      · exact e1
      · exact e2
      · exact e3)) 24 rfl
  have r5 := srch_step hidx (n := 0) r4 (hl 5)
    (cand_mem hq0 hqt hy hiso hnz (i := 5) (by norm_num) (by
      intro j hj
      rw [lane4 (hl 0) (hl 1) (hl 2) (hl 3) (hl 4)]
      obtain ⟨e0, e1, e2, e3, e4, -⟩ := fld_enc6 (hl 0) (hl 1) (hl 2) (hl 3) (hl 4) z64
      interval_cases j
      · exact e0
      · exact e1
      · exact e2
      · exact e3
      · exact e4)) 30 rfl
  rw [lane5 (hl 0) (hl 1) (hl 2) (hl 3) (hl 4)] at r5
  have hcode : enc6 (y (bF 0)).val (y (bF 1)).val (y (bF 2)).val (y (bF 3)).val (y (bF 4)).val
      (y (bF 5)).val = codeL y := rfl
  have hleaf : leafK (codeL y) = true := by
    rw [← hcode]
    exact r5
  have hgood : goodK (codeL y) = true := goodK_of hs40 hy hG
  have hgood2 : good2K (codeL y) = true := by
    unfold good2K
    rw [allL_iff]
    intro t ht
    have hT := fnL_add t
    rw [← codeL_fnL (s40K_lt t ht), compL_codeL hT]
    exact goodCK_of hs40 (A := y) (B := fun v => fnL t (y v)) hy (add_comp hT hy)
      (h2 (fnL t) (fnL_mem_hallS40 hs40 ht))
  have hgood3 : good3K (codeL y) = true := by
    unfold good3K
    rw [allL_iff]
    intro t ht
    have hT := fnL_add t
    rw [← codeL_fnL (s40K_lt t ht), compL_codeL hT, compL_codeL hy]
    unfold good3RowK
    rw [allL_iff]
    intro u hu
    have hU := fnL_add u
    rw [← codeL_fnL (s40K_lt u hu), compL_codeL hU]
    exact goodCK_of hs40 (A := fun v => y (fnL t (y v))) (B := fun v => fnL u (y v))
      (add_comp (g := fun v => fnL t (y v)) hy (add_comp hT hy)) (add_comp hU hy)
      (h3 (fnL t) (fnL_mem_hallS40 hs40 ht) (fnL u) (fnL_mem_hallS40 hs40 hu))
  have hwi : wInvK (codeL y) = true := by
    rcases bor_eq_true.1 hleaf with h | h
    · exact h
    · rw [bnot_eq_true, band_eq_true.2 ⟨hgood, band_eq_true.2 ⟨hgood2, hgood3⟩⟩] at h
      exact absurd h (by decide)
  have hwi' : inWK (apL (codeL y) 3) = true ∧ inWK (apL (codeL y) 5) = true ∧
      inWK (apL (codeL y) 56) = true := by
    have h := hwi
    unfold wInvK at h
    rw [band_eq_true, band_eq_true] at h
    exact h
  have y3 : InHallW (y 3) := inWK_mem hw (y 3) (by rw [← apL_codeL hy 3]; exact hwi'.1)
  have y5 : InHallW (y 5) := inWK_mem hw (y 5) (by rw [← apL_codeL hy 5]; exact hwi'.2.1)
  have y56 : InHallW (y 56) := inWK_mem hw (y 56) (by rw [← apL_codeL hy 56]; exact hwi'.2.2)
  have hWx : ∀ a b : Fin 64, InHallW a → InHallW b → InHallW (xorF a b) :=
    fun a b ha hb => wclosed a.val ha b.val hb
  intro k hk
  rcases hallW_cases k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hy]
    exact hWx _ _ y3 y3
  · exact y3
  · exact y5
  · rw [hy]
    exact hWx _ _ y3 y5
  · exact y56
  · rw [hy]
    exact hWx _ _ y3 y56
  · rw [hy]
    exact hWx _ _ y5 y56
  · rw [hy, hy]
    exact hWx _ _ (hWx _ _ y3 y5) y56

end CFSG.KC.Hall82K
