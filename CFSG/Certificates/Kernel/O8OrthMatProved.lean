module

public import CFSG.Certificates.Kernel.O8OrthProved

public section

namespace CFSG.KC.O8.OrthPf

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M CFSG.KC.O8
  CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem decR_getD (P : ℕ) {i : ℕ} (hi : i < 6) : (decR P).getD i 0 = frow P i := by
  interval_cases i <;> rfl

theorem xorFold_congr {k : ℕ} {f g : ℕ → Bool} (h : ∀ l < k, f l = g l) :
    xorFold k f = xorFold k g := by
  induction k with
  | zero => rfl
  | succ k ih => rw [xorFold_succ, xorFold_succ, ih (fun l hl => h l (by omega)), h k (by omega)]

theorem popc_mod (n y : ℕ) : popc n y % 2 = (xorFold n fun j => y.testBit j).toNat := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Nat.land (Nat.shiftRight y n) 1 + popc n y) % 2 = _
    rw [xorFold_succ, Nat.add_mod, ih]
    change ((bitN y n) % 2 + _) % 2 = _
    rw [bitN_eq]
    cases y.testBit n <;> cases xorFold n (fun j => y.testBit j) <;> rfl

theorem par6_eq (x : ℕ) : par6 x = (xorFold 6 fun j => x.testBit j).toNat := by
  change Nat.land (popc 6 x) 1 = _
  rw [show Nat.land (popc 6 x) 1 = popc 6 x % 2 from Nat.and_one_is_mod _, popc_mod]

theorem testBit_bvecK (A v i : ℕ) : (bvecK A v).testBit i =
    (decide (i < 6) && xorFold 6 fun j => (frow A i).testBit j && v.testBit j) := by
  rw [Bool.eq_iff_iff]
  unfold bvecK
  rw [testBit_orN_iff]
  change (∃ i' < 6, (par6 (frow A i' &&& v) <<< i').testBit i = true) ↔ _
  simp only [par6_eq, testBit_toNat_shl, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_and]
  constructor
  · rintro ⟨i', hi', h, rfl⟩
    exact ⟨hi', h⟩
  · rintro ⟨hi, h⟩
    exact ⟨i, hi, h, rfl⟩

theorem bvecK_eq (A v : ℕ) : bvecK A v = bmulVec 6 6 (decR A) v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bvecK, bmulVec, testBit_bitsOf]
  by_cases hi : i < 6
  · rw [decR_getD A hi]
  · simp [hi]

theorem bmulVec_lt (A : Array ℕ) (v : ℕ) : bmulVec 6 6 A v < 64 := by
  have : bmulVec 6 6 A v < 2 ^ 6 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [bmulVec, testBit_bitsOf]
    simp
    omega
  simpa using this

theorem testBit_xorN (n : ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (xorN n f).testBit j = xorFold n fun l => (f l).testBit j := by
  induction n with
  | zero =>
    rw [show xorN 0 f = 0 from rfl, Nat.zero_testBit]
    rfl
  | succ n ih =>
    change (Nat.xor (f n) (xorN n f)).testBit j = _
    rw [testBit_nxor, ih, xorFold_succ, Bool.xor_comm]

theorem xorN_lt (n : ℕ) (f : ℕ → ℕ) (h : ∀ l < n, f l < 64) : xorN n f < 64 := by
  induction n with
  | zero =>
    change 0 < 64
    omega
  | succ n ih =>
    change Nat.xor (f n) (xorN n f) < 64
    have h1 : f n < 2 ^ 6 := h n (by omega)
    have h2 : xorN n f < 2 ^ 6 := ih (fun l hl => h l (by omega))
    exact Nat.xor_lt_two_pow h1 h2

theorem testBit_orN_rows {R : ℕ → ℕ} (hR : ∀ i < 6, R i < 64) {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    (orN 6 fun i => R i <<< (6 * i)).testBit (6 * i + j) = (R i).testBit j := by
  rw [Bool.eq_iff_iff, testBit_orN_iff]
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i', hi', hle, h⟩
    rcases Nat.lt_trichotomy i' i with hlt | rfl | hgt
    · have h64 : R i' < 2 ^ 6 := hR i' hi'
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega)
        (by omega : 6 ≤ 6 * i + j - 6 * i')))] at h
      exact absurd h (by decide)
    · rwa [show 6 * i' + j - 6 * i' = j by omega] at h
    · omega
  · intro h
    exact ⟨i, hi, by omega, by rwa [show 6 * i + j - 6 * i = j by omega]⟩

theorem bmul_getD {A B : Array ℕ} {i : ℕ} (hi : i < 6) :
    (bmul 6 6 A B).getD i 0 = rowMul 6 (A.getD i 0) B := by
  rw [bmul]
  exact getD_ofFn _ ⟨i, hi⟩

theorem ID6_bits : ∀ i < 6, ∀ j < 6, ID6.testBit (6 * i + j) = decide (i = j) := by
  decide +kernel

theorem bIsId_of_bmulK {A B : ℕ} (h : bmulK A B = ID6) : bIsId 6 (bmul 6 6 (decR A) (decR B)) = true := by
  have hA : A ≠ 0 := by
    rintro rfl
    have : bmulK 0 B = 0 := rfl
    rw [this] at h
    exact absurd h (by decide)
  have hB : B ≠ 0 := by
    rintro rfl
    have : bmulK A 0 = 0 := by
      change strictN A (fun A => nIf(Nat.beq A (nat_lit 0), nat_lit 0, nat_lit 0)) = 0
      rw [strictN_eq, nIf_eq]
      split <;> rfl
    rw [this] at h
    exact absurd h (by decide)
  have hb : bmulK A B = orN 6 fun i => (xorN 6 fun l =>
      nIf(Nat.beq (bitN (frow A i) l) (nat_lit 1), frow B l, nat_lit 0)) <<< (6 * i) := by
    change strictN A (fun A => nIf(Nat.beq A (nat_lit 0), nat_lit 0, strictN B fun B =>
      nIf(Nat.beq B (nat_lit 0), nat_lit 0, orN (nat_lit 6) fun i => Nat.shiftLeft
        (xorN (nat_lit 6) fun l => nIf(Nat.beq (bitN (frow A i) l) (nat_lit 1), frow B l, nat_lit 0))
        (Nat.mul (nat_lit 6) i)))) = _
    rw [strictN_eq]
    beta_reduce
    rw [nIf_eq, if_neg (fun h' => hA (Nat.eq_of_beq_eq_true h')), strictN_eq]
    beta_reduce
    rw [nIf_eq, if_neg (fun h' => hB (Nat.eq_of_beq_eq_true h'))]
    rfl
  have hrow : ∀ i < 6, ∀ j < 6,
      (xorFold 6 fun l => (frow A i).testBit l && (frow B l).testBit j) = decide (i = j) := by
    intro i hi j hj
    rw [← ID6_bits i hi j hj, ← h, hb, testBit_orN_rows (fun i _ => xorN_lt 6 _ (fun l _ => by
      rw [nIf_eq]
      split
      · exact fget_lt _ _ _
      · omega)) hi hj, testBit_xorN]
    apply xorFold_congr
    intro l _
    rw [nIf_eq, beq_bitN]
    cases (frow A i).testBit l <;> simp
  simp only [bIsId, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro i hi j hj
  rw [bmul_getD hi, testBit_rowMul, decR_getD A hi, ← hrow i hi j hj]
  apply xorFold_congr
  intro l hl
  rw [decR_getD B hl]

theorem bvecK_lt (A v : ℕ) : bvecK A v < 64 := by
  rw [bvecK_eq]
  exact bmulVec_lt _ _

theorem nbeq_toNat (a b : Bool) : Nat.beq a.toNat b.toNat = (a == b) := by
  cases a <;> cases b <;> rfl

theorem qK_bind {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) {x : ℕ} (hx : x < 64) :
    qK Q x = (q x).toNat := by
  rw [qK_eq, hq x hx]

theorem gen_sound_proved {q : ℕ → Bool} {G GI : ℕ → Array ℕ} {Q GP GIP : Nat} (hq : QBind q Q)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hGI : ∀ s < 6, GI s = decR (mat GIP s))
    (h : genOK Q GP GIP = true) : genCheckG q G GI = true := by
  change allN 6 (fun i => andB (Nat.beq (bmulK (mat GP i) (mat GIP i)) ID6)
    (andB (Nat.beq (bmulK (mat GIP i) (mat GP i)) ID6)
      (allN 64 fun x => Nat.beq (qK Q (bvecK (mat GP i) x)) (qK Q x)))) = true at h
  rw [allN_eq, List.all_eq_true] at h
  rw [genCheckG, List.all_eq_true]
  intro i hi
  have hi6 := List.mem_range.1 hi
  have hh := h i hi
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, allN_eq, List.all_eq_true] at hh
  obtain ⟨h1, h2, h3⟩ := hh
  rw [hG i hi6, hGI i hi6, bIsId_of_bmulK (Nat.eq_of_beq_eq_true h1),
    bIsId_of_bmulK (Nat.eq_of_beq_eq_true h2), Bool.true_and, Bool.true_and, List.all_eq_true]
  intro x hx
  have h4 := h3 x hx
  rw [qK_bind hq (bvecK_lt _ _), qK_bind hq (List.mem_range.1 hx), nbeq_toNat, bvecK_eq] at h4
  exact h4

theorem wordActK_eq {GP : ℕ} {G : ℕ → Array ℕ} (hG : ∀ s < 6, G s = decR (mat GP s)) :
    ∀ (w : List ℕ), (∀ s ∈ w, s < 6) → ∀ x, wordActK GP w x = wordActG G w x
  | [], _, _ => rfl
  | s :: w, hw, x => by
    change bvecK (mat GP s) (wordActK GP w x) = bmulVec 6 6 (G s) (wordActG G w x)
    rw [wordActK_eq hG w (fun t ht => hw t (by simp [ht])) x, hG s (hw s (by simp)), bvecK_eq]

theorem wordAt_eq : ∀ (OW : List (List ℕ)) (x : ℕ), wordAt OW x = OW.getD x []
  | [], x => by cases x <;> rfl
  | _ :: _, 0 => rfl
  | w :: OW, x + 1 => by
    change wordAt OW x = _
    rw [wordAt_eq OW x, List.getD_cons_succ]

theorem getD_letters {OWl : List (List ℕ)} (hl : ∀ w ∈ OWl, ∀ s ∈ w, s < 6) (x : ℕ) :
    ∀ s ∈ OWl.getD x [], s < 6 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : OWl[x]? with
  | none => simp
  | some w => simpa using hl w (List.mem_of_getElem? h)

theorem orbit_sound_proved {q : ℕ → Bool} {G : ℕ → Array ℕ} {OW : Array (List ℕ)} {Q GP n : Nat}
    {OWl : List (List ℕ)} (hq : QBind q Q) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hOW : OW = OWl.toArray) (hl : ∀ w ∈ OWl, ∀ s ∈ w, s < 6) (h : orbitOK Q GP n OWl = true) :
    orbitCheckG q G OW n = true := by
  change allN 64 (fun x => orB (Nat.beq x (nat_lit 0)) (Nat.beq (wordActK GP (wordAt OWl x)
    (nIf(Nat.beq (qK Q x) (nat_lit 1), n, nat_lit 1))) x)) = true at h
  rw [allN_eq, List.all_eq_true] at h
  rw [orbitCheckG, List.all_eq_true]
  intro x hx
  have hx64 := List.mem_range.1 hx
  have h' := h x hx
  rw [orB_eq, nIf_eq, qK_eq, beq_toNat_one, ← hq x hx64, wordAt_eq,
    wordActK_eq hG _ (getD_letters hl x)] at h'
  have e : OW.getD x [] = OWl.getD x [] := by
    rw [hOW]
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  exact h'

theorem affK_eq (D x : ℕ) :
    affK D x = affB (decR (Nat.land D (maskN 36)), Nat.shiftRight D 36) x := by
  change Nat.xor (bvecK (Nat.land D (maskN 36)) x) (Nat.shiftRight D 36) = _
  rw [bvecK_eq]
  rfl

theorem affB_lt {D : ℕ} (hD : Nat.shiftRight D 36 < 64) (x : ℕ) :
    affB (decR (Nat.land D (maskN 36)), Nat.shiftRight D 36) x < 64 := by
  have h1 : bmulVec 6 6 (decR (Nat.land D (maskN 36))) x < 2 ^ 6 := bmulVec_lt _ _
  have h2 : Nat.shiftRight D 36 < 2 ^ 6 := hD
  exact Nat.xor_lt_two_pow h1 h2

theorem cone_sound_proved {q : ℕ → Bool} {X Xi Y Yi : Array ℕ × ℕ} {C : List ℕ}
    {Q XP XiP YP YiP CC : Nat} (hq : QBind q Q)
    (hX : X = (decR (Nat.land XP (maskN 36)), Nat.shiftRight XP 36))
    (hXi : Xi = (decR (Nat.land XiP (maskN 36)), Nat.shiftRight XiP 36))
    (hY : Y = (decR (Nat.land YP (maskN 36)), Nat.shiftRight YP 36))
    (hYi : Yi = (decR (Nat.land YiP (maskN 36)), Nat.shiftRight YiP 36))
    (hw : ∀ D ∈ [XP, XiP, YP, YiP], Nat.shiftRight D 36 < 64)
    (hC : C = (List.range 6).map fun j => colAt CC j)
    (h : coneOK Q XP XiP YP YiP CC = true) : coneCheckG q X Xi Y Yi C = true := by
  subst hX hXi hY hYi hC
  have hXb := affB_lt (hw XP (by simp))
  have hYb := affB_lt (hw YP (by simp))
  have hL : ∀ j < 6, ((List.range 6).map fun j => colAt CC j).getD j 0 = colAt CC j := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, hj]
  have hd := dickK_eq_dickC hL
  have e : coneCheckG q (decR (Nat.land XP (maskN 36)), Nat.shiftRight XP 36)
      (decR (Nat.land XiP (maskN 36)), Nat.shiftRight XiP 36)
      (decR (Nat.land YP (maskN 36)), Nat.shiftRight YP 36)
      (decR (Nat.land YiP (maskN 36)), Nat.shiftRight YiP 36)
      ((List.range 6).map fun j => colAt CC j) = coneOK Q XP XiP YP YiP CC := by
    unfold coneOK coneCheckG
    simp only [andB_eq, allN_eq, affK_eq]
    simp only [Bool.and_assoc]
    congr 1
    · apply all_congr_mem
      intro v hv
      have hv64 := List.mem_range.1 hv
      rw [qK_bind hq (hXb v), qK_bind hq (hYb v), qK_bind hq hv64, nbeq_toNat, nbeq_toNat]
      rfl
    · have hdk : Nat.beq (dickK CC) 1 = dickC ((List.range 6).map fun j => colAt CC j) := by
        rw [hd]
        cases dickC ((List.range 6).map fun j => colAt CC j) <;> rfl
      rw [hdk]
      congr 1
      all_goals first
        | rfl
        | (apply all_congr_mem
           intro j hj
           rw [hL j (List.mem_range.1 hj), pw2_eq]
           rfl)
  rw [e, h]

end CFSG.KC.O8.OrthPf

end
