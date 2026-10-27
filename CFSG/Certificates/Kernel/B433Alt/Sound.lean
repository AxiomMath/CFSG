module

public import Certificates.Data.Kernel.B433Alt.Chain
public import CFSG.Certificates.Kernel.B433Alt.StLenWords
public import CFSG.Certificates.Kernel.B433Alt.CovSound
public import CFSG.Certificates.Kernel.B433Alt.OmSound
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.KC.B433Alt

open CFSG.YGroups CFSG.Certificates.CosetEnumeration CFSG.KC.B4A CFSG.KC.Y333

@[expose] noncomputable def wVal {G : Type*} [Group G] (g : ℕ → G) (w : ℕ) : G := evalWord g (wList w)

@[expose] noncomputable def b5 (i : ℕ) : ℕ := fld BASE5 (16 * i) 65535

theorem b5_lt : ∀ i < 5, b5 i < 31671 := by decide +kernel

@[expose] def cbOf' (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cbOf' b k ||| (b k <<< (15 * k))

structure Tables (ρ : YGroup 4 3 2 →* Equiv.Perm (Fin 31671)) (LP : ℕ → ℕ) : Prop where
  letter : ∀ c < 10, ∀ x : Fin 31671, (ρ (yGen 4 3 2 c) x : ℕ) = pget (LP c) x
  pair : ∀ p < 10, ∀ q < 10, ∀ x < 31671,
    pget (LP (10 + (10 * p + q))) x = pget (LP p) (pget (LP q) x)

variable {ρ : YGroup 4 3 2 →* Equiv.Perm (Fin 31671)} {LP : ℕ → ℕ}

private theorem sN_eq' (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

private theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem wAt_lt_of_wAllLt {w m : ℕ} (h : wAllLt w m = true) : ∀ i < wLen w, wAt w i < m := by
  have key : ∀ n, Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (Nat.blt (wAt w i) m)) n = true → ∀ i < n, wAt w i < m := by
    intro n
    induction n with
    | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro hn i hi
      obtain ⟨h1, h2⟩ := andB_true' hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
      · exact ih h1 i hlt
      · simpa using h2
  exact key _ h

theorem wAt_lt_ten {w : ℕ} (hw : wInH w = true) : ∀ i < wLen w, wAt w i < 10 :=
  wAt_lt_of_wAllLt (andB_true' (show andB (wOK w) (wAllLt w 10) = true from hw)).2

private noncomputable def preV {G : Type*} [Group G] (g : ℕ → G) (w k : ℕ) : G :=
  evalWord g ((List.range k).map (wAt w))

private theorem preV_succ {G : Type*} [Group G] (g : ℕ → G) (w k : ℕ) :
    preV g w (k + 1) = preV g w k * g (wAt w k) := by
  simp [preV, evalWord, List.range_succ, List.map_append, List.prod_append]

private theorem preV_zero {G : Type*} [Group G] (g : ℕ → G) (w : ℕ) : preV g w 0 = 1 := by
  simp [preV, evalWord]

private theorem wVal_eq_preV {G : Type*} [Group G] (g : ℕ → G) (w : ℕ) :
    wVal g w = preV g w (wLen w) := rfl

private noncomputable def pairLoop (w : ℕ) (app : ℕ → ℕ → ℕ) (P : ℕ → ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
      (fun i ih x => sN (app (P (Nat.add (nat_lit 10) (Nat.add
          (Nat.mul (nat_lit 10) (wAt w (Nat.mul (nat_lit 2) i)))
          (wAt w (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)))))) x) (fun x' => ih x'))

private theorem pairLoop_succ (w : ℕ) (app : ℕ → ℕ → ℕ) (P : ℕ → ℕ) (m x : ℕ) :
    pairLoop w app P (m + 1) x =
      pairLoop w app P m (app (P (10 + (10 * wAt w (2 * m) + wAt w (2 * m + 1)))) x) := by
  show sN _ _ = _
  rw [sN_eq']
  rfl

private theorem ev1_eq (LP : ℕ → ℕ) (w x : ℕ) :
    ev1 LP w x = pairLoop w pget LP (wLen w / 2)
      (if wLen w % 2 = 1 then pget (LP (wAt w (wLen w - 1))) x else x) := by
  unfold ev1
  rw [sN_eq', sN_eq']
  have h1 : Nat.shiftRight (wLen w) 1 = wLen w / 2 := by
    rw [show Nat.shiftRight (wLen w) 1 = wLen w >>> 1 from rfl, Nat.shiftRight_eq_div_pow, pow_one]
  have h2 : Nat.land (wLen w) 1 = wLen w % 2 := Nat.and_one_is_mod _
  rw [h1, h2]
  by_cases h : wLen w % 2 = 1
  · rw [if_pos h, show Nat.beq (wLen w % 2) 1 = true by rw [h]; rfl]
    rfl
  · rw [if_neg h, show Nat.beq (wLen w % 2) 1 = false by
      cases hb : Nat.beq (wLen w % 2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h]
    rfl

variable (ρ) in
private theorem pairLoop_spec (hT : Tables ρ LP) {w : ℕ} (hl : ∀ i < wLen w, wAt w i < 10) :
    ∀ m, 2 * m ≤ wLen w → ∀ x : Fin 31671,
      pairLoop w pget LP m x = (ρ (preV (yGen 4 3 2) w (2 * m)) x : ℕ)
  | 0, _, x => by simp [pairLoop, preV_zero]
  | m + 1, hm, x => by
    have ha := hl (2 * m) (by omega)
    have hb := hl (2 * m + 1) (by omega)
    rw [pairLoop_succ, hT.pair _ ha _ hb x x.2, ← hT.letter _ hb x,
      ← hT.letter _ ha (ρ (yGen 4 3 2 (wAt w (2 * m + 1))) x),
      pairLoop_spec hT hl m (by omega)]
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, preV_succ, preV_succ, map_mul, map_mul]
    rfl

theorem ev1_spec (hT : Tables ρ LP) {w x : ℕ} (hw : wInH w = true) (hx : x < 31671) :
    (ρ (wVal (yGen 4 3 2) w) ⟨x, hx⟩ : ℕ) = ev1 LP w x := by
  have hl := wAt_lt_ten hw
  rw [ev1_eq, wVal_eq_preV]
  by_cases h : wLen w % 2 = 1
  · rw [if_pos h, ← hT.letter _ (hl _ (by omega)) ⟨x, hx⟩, pairLoop_spec ρ hT hl _ (by omega)]
    have e : wLen w = 2 * (wLen w / 2) + 1 := by omega
    conv_lhs => rw [e]
    rw [preV_succ, map_mul, show 2 * (wLen w / 2) = wLen w - 1 by omega]
    rfl
  · rw [if_neg h, pairLoop_spec ρ hT hl _ (by omega) ⟨x, hx⟩,
      show 2 * (wLen w / 2) = wLen w by omega]


private theorem pget_lt15 (P i : ℕ) : pget P i < 32768 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

private theorem lor_mul_eq {x y M s : ℕ} (hx : x < M) (hM : M = 2 ^ s) :
    Nat.lor x (M * y) = M * y + x := by
  subst hM
  rw [show Nat.lor x (2 ^ s * y) = x ||| 2 ^ s * y from rfl, Nat.lor_comm,
    ← Nat.two_pow_add_eq_or_of_lt hx]

private theorem fld15_eq (X o : ℕ) : fld X o 32767 = X / 2 ^ o % 32768 := by
  show (X >>> o) &&& (2 ^ 15 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

private theorem app5_eq (P c : ℕ) : app5 P c =
    pget P (fld c 0 32767) + 65536 * (pget P (fld c 16 32767) + 65536 * (pget P (fld c 32 32767) +
      65536 * (pget P (fld c 48 32767) + 65536 * pget P (fld c 64 32767)))) := by
  have e0 : fld c 0 32767 = Nat.land c 32767 := rfl
  have h0 := pget_lt15 P (fld c 0 32767)
  have h1 := pget_lt15 P (fld c 16 32767)
  have h2 := pget_lt15 P (fld c 32 32767)
  have h3 := pget_lt15 P (fld c 48 32767)
  have h4 := pget_lt15 P (fld c 64 32767)
  show Nat.lor (pget P (Nat.land c 32767)) (Nat.lor (Nat.shiftLeft (pget P (fld c 16 32767)) 16)
    (Nat.lor (Nat.shiftLeft (pget P (fld c 32 32767)) 32)
      (Nat.lor (Nat.shiftLeft (pget P (fld c 48 32767)) 48)
        (Nat.shiftLeft (pget P (fld c 64 32767)) 64)))) = _
  rw [e0] at h0 ⊢
  generalize pget P (Nat.land c 32767) = a0 at h0 ⊢
  generalize pget P (fld c 16 32767) = a1 at h1 ⊢
  generalize pget P (fld c 32 32767) = a2 at h2 ⊢
  generalize pget P (fld c 48 32767) = a3 at h3 ⊢
  generalize pget P (fld c 64 32767) = a4 at h4 ⊢
  have s1 : Nat.shiftLeft a1 16 = a1 * 65536 := by
    rw [show Nat.shiftLeft a1 16 = a1 <<< 16 from rfl, Nat.shiftLeft_eq]
  have s2 : Nat.shiftLeft a2 32 = a2 * 4294967296 := by
    rw [show Nat.shiftLeft a2 32 = a2 <<< 32 from rfl, Nat.shiftLeft_eq]
  have s3 : Nat.shiftLeft a3 48 = a3 * 281474976710656 := by
    rw [show Nat.shiftLeft a3 48 = a3 <<< 48 from rfl, Nat.shiftLeft_eq]
  have s4 : Nat.shiftLeft a4 64 = 18446744073709551616 * a4 := by
    rw [show Nat.shiftLeft a4 64 = a4 <<< 64 from rfl, Nat.shiftLeft_eq, mul_comm]
  rw [s1, s2, s3, s4, lor_mul_eq (s := 64) (by omega) (by norm_num),
    show 18446744073709551616 * a4 + a3 * 281474976710656 =
      281474976710656 * (65536 * a4 + a3) by ring,
    lor_mul_eq (s := 48) (by omega) (by norm_num),
    show 281474976710656 * (65536 * a4 + a3) + a2 * 4294967296 =
      4294967296 * (65536 * (65536 * a4 + a3) + a2) by ring,
    lor_mul_eq (s := 32) (by omega) (by norm_num),
    show 4294967296 * (65536 * (65536 * a4 + a3) + a2) + a1 * 65536 =
      65536 * (65536 * (65536 * (65536 * a4 + a3) + a2) + a1) by ring,
    lor_mul_eq (s := 16) (by omega) (by norm_num)]
  ring

private theorem fld_app5 (P c : ℕ) : ∀ i < 5,
    fld (app5 P c) (16 * i) 32767 = pget P (fld c (16 * i) 32767) := by
  intro i hi
  have h0 := pget_lt15 P (fld c 0 32767)
  have h1 := pget_lt15 P (fld c 16 32767)
  have h2 := pget_lt15 P (fld c 32 32767)
  have h3 := pget_lt15 P (fld c 48 32767)
  have h4 := pget_lt15 P (fld c 64 32767)
  rw [app5_eq, fld15_eq]
  interval_cases i <;> norm_num <;> omega

private theorem evW_eq (LP : ℕ → ℕ) (w c : ℕ) :
    evW LP w c = pairLoop w app5 LP (wLen w / 2)
      (if wLen w % 2 = 1 then app5 (LP (wAt w (wLen w - 1))) c else c) := by
  unfold evW
  rw [sN_eq', sN_eq']
  have h1 : Nat.shiftRight (wLen w) 1 = wLen w / 2 := by
    rw [show Nat.shiftRight (wLen w) 1 = wLen w >>> 1 from rfl, Nat.shiftRight_eq_div_pow, pow_one]
  have h2 : Nat.land (wLen w) 1 = wLen w % 2 := Nat.and_one_is_mod _
  rw [h1, h2]
  by_cases h : wLen w % 2 = 1
  · rw [if_pos h, show Nat.beq (wLen w % 2) 1 = true by rw [h]; rfl]
    rfl
  · rw [if_neg h, show Nat.beq (wLen w % 2) 1 = false by
      cases hb : Nat.beq (wLen w % 2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h]
    rfl

private theorem fld_pairLoop (w : ℕ) (LP : ℕ → ℕ) {i : ℕ} (hi : i < 5) :
    ∀ m c, fld (pairLoop w app5 LP m c) (16 * i) 32767 = pairLoop w pget LP m (fld c (16 * i) 32767)
  | 0, c => rfl
  | m + 1, c => by
    rw [pairLoop_succ, pairLoop_succ, fld_pairLoop w LP hi m, fld_app5 _ _ i hi]

private theorem fld_evW (LP : ℕ → ℕ) (w c : ℕ) {i : ℕ} (hi : i < 5) :
    fld (evW LP w c) (16 * i) 32767 = ev1 LP w (fld c (16 * i) 32767) := by
  rw [evW_eq, ev1_eq, fld_pairLoop w LP hi]
  split_ifs
  · rw [fld_app5 _ _ i hi]
  · rfl

private theorem fld_BASE5 : ∀ i < 5, fld BASE5 (16 * i) 32767 = b5 i := by decide +kernel

theorem isOne_spec (hT : Tables ρ LP) {w : ℕ} (hw : wInH w = true) (h : isOne LP w = true) :
    ∀ i (hi : i < 5), (ρ (wVal (yGen 4 3 2) w) ⟨b5 i, b5_lt i hi⟩ : ℕ) = b5 i := by
  intro i hi
  have e : evW LP w BASE5 = BASE5 := Nat.eq_of_beq_eq_true h
  rw [ev1_spec hT hw, ← fld_BASE5 i hi, ← fld_evW LP w BASE5 hi, e]

@[expose] noncomputable def genWord (RD RW EL EW : ℕ → ℕ) (j l G nG k : ℕ) : ℕ :=
  genW RD RW EL EW j l G nG k - 1

@[expose] def ChunkRun (CS CT : ℕ → ℕ) (k₀ n S : ℕ) : Prop :=
  (0 < n → CS k₀ = S) ∧ ∀ i < n - 1, CS (k₀ + i + 1) = CT (k₀ + i)


private theorem sB_eq' (v : ℕ) (k : ℕ → Bool) : B4A.sB v k = k v := by cases v <;> rfl

private theorem andB_iff' {a b : Bool} : B4A.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem recAnd_spec {f : ℕ → Bool} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun i acc => B4A.andB acc (f i)) n = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_iff'.1 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact recAnd_spec n h1 i hlt
    · exact h2

private theorem genW_spec' {RD RW EL EW : ℕ → ℕ} {j l G nG k : ℕ}
    (h : 0 < genW RD RW EL EW j l G nG k) : k < nG ∧
    (l = 0 → isStab (dKind (RD (fld G (20 * k) (ones 20)))) = true ∧
      genWord RD RW EL EW j l G nG k = RW (fld G (20 * k) (ones 20))) ∧
    (l ≠ 0 → elJ (EL (fld G (20 * k) (ones 20))) = j ∧ elL (EL (fld G (20 * k) (ones 20))) = l ∧
      genWord RD RW EL EW j l G nG k = EW (fld G (20 * k) (ones 20))) := by
  unfold genWord
  unfold genW at h ⊢
  simp only [sN_eq'] at h ⊢
  cases h1 : Nat.blt k nG
  · simp only [h1] at h
    exact absurd h (lt_irrefl 0)
  · simp only [h1] at h
    refine ⟨Nat.blt_eq.mp h1, ?_⟩
    by_cases hl : l = 0
    · subst hl
      have h2 : Nat.beq 0 0 = true := rfl
      rw [h2] at h ⊢
      cases h3 : B4A.andB (isStab (dKind (RD (fld G (Nat.mul 20 k) (ones 20)))))
          (Nat.beq (dN2 (RD (fld G (Nat.mul 20 k) (ones 20)))) j)
      · rw [h3] at h
        exact absurd h (lt_irrefl 0)
      · rw [andB_iff'] at h3
        refine ⟨fun _ => ⟨h3.1, ?_⟩, fun h => absurd rfl h⟩
        simp only [h1]
        rfl
    · have h2 : Nat.beq l 0 = false := by
        cases e : Nat.beq l 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hl
      rw [h2] at h ⊢
      cases h3 : B4A.andB (Nat.beq (elJ (EL (fld G (Nat.mul 20 k) (ones 20)))) j)
          (Nat.beq (elL (EL (fld G (Nat.mul 20 k) (ones 20)))) l)
      · rw [h3] at h
        exact absurd h (lt_irrefl 0)
      · rw [andB_iff'] at h3
        refine ⟨fun h => absurd h hl, fun _ =>
          ⟨Nat.eq_of_beq_eq_true h3.1, Nat.eq_of_beq_eq_true h3.2, ?_⟩⟩
        simp only [h1]
        rfl

private theorem elOK_facts {RD RW EL EW : ℕ → ℕ} {CB e : ℕ}
    (h : elOK LP RD RW EL EW CB e = true) : 1 ≤ elL (EL e) ∧ wInH (EW e) = true ∧
      ∀ i < elL (EL e), ev1 LP (EW e) (fld CB (15 * i) 32767) = fld CB (15 * i) 32767 := by
  unfold elOK at h
  simp only [sB_eq'] at h
  obtain ⟨h1, -, h3, -, h5⟩ := by simpa only [andB_iff'] using h
  refine ⟨Nat.ble_eq.mp h1, h3, fun i hi => ?_⟩
  exact Nat.eq_of_beq_eq_true (recAnd_spec _ h5 i hi)

private theorem cbOf'_succ (b : ℕ → ℕ) (k : ℕ) :
    cbOf' b (k + 1) = cbOf' b k ||| (b k <<< (15 * k)) :=
  rfl

private theorem cbOf'_spec {b : ℕ → ℕ} : ∀ k, (∀ m < k, b m < 32768) →
    cbOf' b k < 2 ^ (15 * k) ∧ ∀ i < k, fld (cbOf' b k) (15 * i) 32767 = b i
  | 0, _ => ⟨by simp [cbOf'], fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | k + 1, hb => by
    obtain ⟨hlt, hf⟩ := cbOf'_spec k fun m hm => hb m (by omega)
    have hbk := hb k (by omega)
    have e : cbOf' b (k + 1) = 2 ^ (15 * k) * b k + cbOf' b k := by
      rw [cbOf'_succ, Nat.lor_comm, Nat.shiftLeft_eq, mul_comm,
        ← Nat.two_pow_add_eq_or_of_lt hlt]
    have hpow : 2 ^ (15 * (k + 1)) = 2 ^ (15 * k) * 32768 := by
      rw [show 15 * (k + 1) = 15 * k + 15 by ring, pow_add]; norm_num
    refine ⟨?_, fun i hi => ?_⟩
    · rw [e, hpow]
      have h1 : 2 ^ (15 * k) * b k ≤ 2 ^ (15 * k) * 32767 := Nat.mul_le_mul_left _ (by omega)
      linarith
    · rw [fld15_eq, e]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | rfl
      · have h2 := hf i hik
        rw [fld15_eq] at h2
        have hM : 2 ^ (15 * k) * b k = 2 ^ (15 * i) * (32768 * (2 ^ (15 * (k - i - 1)) * b k)) := by
          rw [show (32768 : ℕ) = 2 ^ 15 by norm_num, ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
        rw [hM, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.add_mul_mod_self_left]
        exact h2
      · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt hlt, zero_add, Nat.mod_eq_of_lt hbk]


private theorem nland' (a b : ℕ) : Nat.land a b = a &&& b := rfl
private theorem nlor' (a b : ℕ) : Nat.lor a b = a ||| b := rfl
private theorem nshr' (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
private theorem nadd' (a b : ℕ) : Nat.add a b = a + b := rfl
private theorem nsub' (a b : ℕ) : Nat.sub a b = a - b := rfl
private theorem shl1' (n : ℕ) : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n

private theorem brec_eq_ite (a b : ℕ) (c : Bool) :
    Bool.rec (motive := fun _ => ℕ) a b c = if c = true then b else a := by
  cases c <;> rfl

private theorem land_two_pow' (a n : ℕ) : a &&& 2 ^ n = if a.testBit n then 2 ^ n else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : n = j
  · subst hj
    by_cases h : a.testBit n <;> simp [h, Nat.testBit_two_pow_self]
  · by_cases h : a.testBit n <;> simp [h, hj, Nat.testBit_two_pow_of_ne hj]

private def OrbInv (O : Set (Fin 31671)) (S : ℕ) : Prop :=
  S = 0 ∨ ∃ V : Finset (Fin 31671), (∀ p ∈ V, p ∈ O) ∧ S % 2 ^ 32 = V.card ∧
    ∀ q, (S / 2 ^ 32).testBit q = true ↔ ∃ p ∈ V, (p : ℕ) = q

private theorem orbInv_init {O : Set (Fin 31671)} {b : ℕ} (hb : b < 31671) (hbO : ⟨b, hb⟩ ∈ O) :
    OrbInv O (orbInit b) := by
  right
  refine ⟨{⟨b, hb⟩}, by simpa using hbO, ?_, fun q => ?_⟩
  · show (Nat.lor 1 (Nat.shiftLeft 1 (Nat.add b 32))) % 2 ^ 32 = _
    rw [nlor', shl1', nadd', Nat.or_two_pow_eq_add_of_lt (Nat.one_lt_two_pow (by omega)),
      pow_add, mul_comm, Nat.add_mul_mod_self_left]
    rfl
  · show (Nat.lor 1 (Nat.shiftLeft 1 (Nat.add b 32)) / 2 ^ 32).testBit q = true ↔ _
    rw [nlor', shl1', nadd', Nat.or_two_pow_eq_add_of_lt (Nat.one_lt_two_pow (by omega)),
      pow_add, mul_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 32)]
    rw [show (1 : ℕ) / 2 ^ 32 = 0 by norm_num, zero_add, Nat.testBit_two_pow]
    simp [eq_comm]

private theorem orbInv_step {O : Set (Fin 31671)} {S o q : ℕ} (hS : OrbInv O S) (hS0 : 0 < S)
    (ho : o < 31671) (hq : 0 < S &&& 2 ^ (q + 32)) (hno : S &&& 2 ^ (o + 32) = 0)
    (hmove : ∀ hq' : q < 31671, ⟨q, hq'⟩ ∈ O → (⟨o, ho⟩ : Fin 31671) ∈ O) :
    OrbInv O ((S ||| 2 ^ (o + 32)) + 1) := by
  rcases hS with h0 | ⟨V, hVO, hc, hbits⟩
  · omega
  rw [land_two_pow'] at hq hno
  have hqb : S.testBit (q + 32) = true := by
    by_contra h; simp [h] at hq
  have hob : S.testBit (o + 32) = false := by
    by_contra h; simp [h] at hno
  obtain ⟨p, hpV, hpq⟩ := (hbits q).1 (by rw [Nat.testBit_div_two_pow]; exact hqb)
  have hqlt : q < 31671 := hpq ▸ p.2
  have hpe : p = ⟨q, hqlt⟩ := Fin.ext hpq
  have hoO := hmove hqlt (hpe ▸ hVO p hpV)
  have hoV : (⟨o, ho⟩ : Fin 31671) ∉ V := fun h => by
    have := (hbits o).2 ⟨_, h, rfl⟩
    rw [Nat.testBit_div_two_pow] at this
    rw [hob] at this
    exact absurd this (by decide)
  have hcard : V.card < 31671 := by
    have : V.card + 1 ≤ 31671 := by
      calc V.card + 1 = (insert (⟨o, ho⟩ : Fin 31671) V).card :=
            (Finset.card_insert_of_notMem hoV).symm
        _ ≤ Finset.univ.card := Finset.card_le_univ _
        _ = 31671 := by simp
    omega
  have hm : (S ||| 2 ^ (o + 32)) % 2 ^ 32 = S % 2 ^ 32 := by
    rw [Nat.or_mod_two_pow, show 2 ^ (o + 32) = 2 ^ 32 * 2 ^ o by rw [pow_add, mul_comm],
      Nat.mul_mod_right, Nat.or_zero]
  have hd : (S ||| 2 ^ (o + 32)) / 2 ^ 32 = S / 2 ^ 32 ||| 2 ^ o := by
    rw [Nat.or_div_two_pow, show 2 ^ (o + 32) = 2 ^ 32 * 2 ^ o by rw [pow_add, mul_comm],
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos 32)]
  generalize S ||| 2 ^ (o + 32) = T at hm hd
  have hT : T % 4294967296 + 1 < 4294967296 := by
    rw [show (4294967296 : ℕ) = 2 ^ 32 by norm_num, hm, hc]; omega
  right
  refine ⟨insert ⟨o, ho⟩ V, ?_, ?_, fun q' => ?_⟩
  · intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hoO
    · exact hVO p hp
  · rw [Finset.card_insert_of_notMem hoV, ← hc, ← hm]
    rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at *
    omega
  · have e : (T + 1) / 2 ^ 32 = T / 2 ^ 32 := by
      rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num]; omega
    rw [e, hd, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hbits q']
    simp only [Finset.mem_insert, decide_eq_true_eq]
    constructor
    · rintro (⟨p, hp, rfl⟩ | rfl)
      · exact ⟨p, Or.inr hp, rfl⟩
      · exact ⟨⟨o, ho⟩, Or.inl rfl, rfl⟩
    · rintro ⟨p, rfl | hp, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨p, hp, rfl⟩


private theorem orbRun_succ (RD RW EL EW : ℕ → ℕ) (j l G nG n Rs S : ℕ) :
    orbRun LP RD RW EL EW j l G nG (n + 1) Rs S =
      sN (Nat.land Rs (nat_lit 32767)) (fun o => sN (fld Rs (nat_lit 15) (nat_lit 32767)) (fun q =>
      sN (fld Rs (nat_lit 30) (nat_lit 255)) (fun k => sN (genW RD RW EL EW j l G nG k) (fun gw =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Nat.add (Nat.lor S (Nat.shiftLeft (nat_lit 1) (Nat.add o (nat_lit 32)))) (nat_lit 1))
            (fun S' => orbRun LP RD RW EL EW j l G nG n (Nat.shiftRight Rs (nat_lit 38)) S'))
          (B4A.andB (Nat.blt (nat_lit 0) S) (B4A.andB (Nat.blt (nat_lit 0) gw)
            (B4A.andB (Nat.blt o (nat_lit 31671))
            (B4A.andB
              (Nat.blt (nat_lit 0) (Nat.land S (Nat.shiftLeft (nat_lit 1) (Nat.add q (nat_lit 32)))))
              (B4A.andB (Nat.beq (Nat.land S (Nat.shiftLeft (nat_lit 1) (Nat.add o (nat_lit 32))))
                  (nat_lit 0))
                (Nat.beq (ev1 LP (Nat.sub gw (nat_lit 1)) q) o)))))))))) := rfl

private theorem orbRun_inv (hT : Tables ρ LP) {RD RW EL EW : ℕ → ℕ} {j l G nG : ℕ}
    {O : Set (Fin 31671)}
    (hw : ∀ k < nG, wInH (genWord RD RW EL EW j l G nG k) = true)
    (hO : ∀ k < nG, ∀ x : Fin 31671, x ∈ O →
      ρ (wVal (yGen 4 3 2) (genWord RD RW EL EW j l G nG k)) x ∈ O) :
    ∀ n Rs S, OrbInv O S → OrbInv O (orbRun LP RD RW EL EW j l G nG n Rs S) := by
  intro n
  induction n with
  | zero => intro Rs S h; exact h
  | succ n ih =>
    intro Rs S h
    rw [orbRun_succ]
    simp only [sN_eq', brec_eq_ite, nland', nlor', nadd', nsub', nshr', shl1']
    split_ifs with hc
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := by simpa only [andB_iff'] using hc
      have hS0 : 0 < S := Nat.blt_eq.mp h1
      have hgw := Nat.blt_eq.mp h2
      have ho := Nat.blt_eq.mp h3
      have hq := Nat.blt_eq.mp h4
      have hno := Nat.eq_of_beq_eq_true h5
      have hev := Nat.eq_of_beq_eq_true h6
      refine ih _ _ (orbInv_step h hS0 ho hq hno fun hq' hqO => ?_)
      obtain ⟨hk, -, -⟩ := genW_spec' hgw
      have hk' : genW RD RW EL EW j l G nG (fld Rs 30 255) - 1 =
          genWord RD RW EL EW j l G nG (fld Rs 30 255) := rfl
      rw [hk'] at hev
      have hmv := hO _ hk _ hqO
      have e := ev1_spec hT (hw _ hk) hq'
      rw [hev] at e
      have : (⟨Rs &&& 32767, ho⟩ : Fin 31671) =
          ρ (wVal (yGen 4 3 2) (genWord RD RW EL EW j l G nG (fld Rs 30 255))) ⟨_, hq'⟩ :=
        Fin.ext e.symm
      rw [this]
      exact hmv
    · exact Or.inl rfl

theorem level_sound (hT : Tables ρ LP) {RD RW EL EW : ℕ → ℕ} {j l G nG : ℕ} {bs : ℕ → ℕ}
    {CN CR CS CT : ℕ → ℕ} {k₀ n o : ℕ} (hb : bs l < 31671)
    (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    (hel : ∀ e, elJ (EL e) = j → elL (EL e) = l → l ≠ 0 →
      elOK LP RD RW EL EW (cbOf' bs l) e = true)
    (hgen : ∀ k < nG, 0 < genW RD RW EL EW j l G nG k)
    (horb : ∀ i < n, orbRun LP RD RW EL EW j l G nG (CN (k₀ + i)) (CR (k₀ + i)) (CS (k₀ + i)) =
      CT (k₀ + i))
    (hrun : ChunkRun CS CT k₀ n (orbInit (bs l)))
    (hcount : orbCount (if n = 0 then orbInit (bs l) else CT (k₀ + n - 1)) = o)
    (hbs : ∀ m < l, bs m < 31671) :
    (∀ k < nG, wInH (genWord RD RW EL EW j l G nG k) = true ∧
      ∀ m (hm : m < l), (ρ (wVal (yGen 4 3 2) (genWord RD RW EL EW j l G nG k)) ⟨bs m, hbs m hm⟩ : ℕ) =
        bs m) ∧
    o ≤ (MulAction.orbit (Subgroup.closure ((fun k => ρ (wVal (yGen 4 3 2)
      (genWord RD RW EL EW j l G nG k))) '' {k | k < nG})) (⟨bs l, hb⟩ : Fin 31671)).ncard := by
  have hbs15 : ∀ m < l, bs m < 32768 := fun m hm => by have := hbs m hm; omega
  have hCB := (cbOf'_spec l hbs15).2
  have part1 : ∀ k < nG, wInH (genWord RD RW EL EW j l G nG k) = true ∧
      ∀ m (hm : m < l), (ρ (wVal (yGen 4 3 2) (genWord RD RW EL EW j l G nG k))
        ⟨bs m, hbs m hm⟩ : ℕ) = bs m := by
    intro k hk
    obtain ⟨-, h0, h1⟩ := genW_spec' (hgen k hk)
    by_cases hl : l = 0
    · obtain ⟨hs, he⟩ := h0 hl
      exact ⟨he ▸ hrw _ hs, fun m hm => absurd hm (by omega)⟩
    · obtain ⟨hj, hl', he⟩ := h1 hl
      obtain ⟨-, hwi, hfix⟩ := elOK_facts (hel _ hj hl' hl)
      refine ⟨he ▸ hwi, fun m hm => ?_⟩
      rw [he, ev1_spec hT hwi]
      have := hfix m (hl' ▸ hm)
      rw [hCB m hm] at this
      exact this
  refine ⟨part1, ?_⟩
  set O := MulAction.orbit (Subgroup.closure ((fun k => ρ (wVal (yGen 4 3 2)
    (genWord RD RW EL EW j l G nG k))) '' {k | k < nG})) (⟨bs l, hb⟩ : Fin 31671) with hO
  have hgenO : ∀ k < nG, ∀ x : Fin 31671, x ∈ O →
      ρ (wVal (yGen 4 3 2) (genWord RD RW EL EW j l G nG k)) x ∈ O := fun k hk x hx =>
    MulAction.mem_orbit_of_mem_orbit
      (⟨_, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ : Subgroup.closure ((fun k => ρ (wVal (yGen 4 3 2)
        (genWord RD RW EL EW j l G nG k))) '' {k | k < nG})) hx
  have hinv := orbRun_inv hT (fun k hk => (part1 k hk).1) hgenO
  have hb0 : OrbInv O (orbInit (bs l)) := orbInv_init hb (MulAction.mem_orbit_self _)
  have hchunk : ∀ i < n, OrbInv O (CT (k₀ + i)) := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [← horb 0 hi]
      apply hinv
      rw [add_zero, hrun.1 hi]
      exact hb0
    | succ i ih =>
      intro hi
      rw [← horb (i + 1) hi]
      apply hinv
      rw [show k₀ + (i + 1) = k₀ + i + 1 by ring, hrun.2 i (by omega)]
      exact ih (by omega)
  have hfinal : OrbInv O (if n = 0 then orbInit (bs l) else CT (k₀ + n - 1)) := by
    split_ifs with hn
    · exact hb0
    · have := hchunk (n - 1) (by omega)
      rwa [show k₀ + (n - 1) = k₀ + n - 1 by omega] at this
  have hcnt : ∀ S, orbCount S = S % 2 ^ 32 := fun S => by
    show Nat.land S 4294967295 = _
    rw [nland', show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  rw [hcnt] at hcount
  rcases hfinal with h0 | ⟨V, hVO, hc, -⟩
  · rw [h0] at hcount
    rw [← hcount]
    exact Nat.zero_le _
  · rw [← hcount, hc, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun p hp => hVO p hp) (Set.toFinite _)

private theorem facW_spec {RD RW EL EW : ℕ → ℕ} {j l f : ℕ} (h : 0 < facW RD RW EL EW j l f) :
    (l = 1 → isStab (dKind (RD (f >>> 1))) = true ∧ dN2 (RD (f >>> 1)) = j ∧
      (facW RD RW EL EW j l f - 1 = RW (f >>> 1) ∨
        facW RD RW EL EW j l f - 1 = wRev (RW (f >>> 1)))) ∧
    (l ≠ 1 → elJ (EL (f >>> 1)) = j ∧ elL (EL (f >>> 1)) = l - 1 ∧
      (facW RD RW EL EW j l f - 1 = EW (f >>> 1) ∨
        facW RD RW EL EW j l f - 1 = wRev (EW (f >>> 1)))) := by
  unfold facW at h ⊢
  simp only [sN_eq'] at h ⊢
  cases h1 : Nat.beq l 1
  · have hl : l ≠ 1 := fun e => by rw [e] at h1; exact absurd h1 (by decide)
    simp only [h1] at h
    refine ⟨fun e => absurd e hl, fun _ => ?_⟩
    revert h
    cases h2 : B4A.andB (Nat.beq (elJ (EL (f >>> 1))) j) (Nat.beq (elL (EL (f >>> 1))) (l - 1))
    · exact fun h => absurd h (lt_irrefl 0)
    · intro _
      obtain ⟨e1, e2⟩ := andB_iff'.1 h2
      refine ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, ?_⟩
      cases Nat.beq (Nat.land f 1) 1
      · exact Or.inl rfl
      · exact Or.inr rfl
  · have hl : l = 1 := Nat.eq_of_beq_eq_true h1
    simp only [h1] at h
    refine ⟨fun _ => ?_, fun e => absurd hl e⟩
    revert h
    cases h2 : B4A.andB (isStab (dKind (RD (f >>> 1)))) (Nat.beq (dN2 (RD (f >>> 1))) j)
    · exact fun h => absurd h (lt_irrefl 0)
    · intro _
      obtain ⟨e1, e2⟩ := andB_iff'.1 h2
      refine ⟨e1, Nat.eq_of_beq_eq_true e2, ?_⟩
      cases Nat.beq (Nat.land f 1) 1
      · exact Or.inl rfl
      · exact Or.inr rfl

private noncomputable def elFold (RD RW EL EW : ℕ → ℕ) (j l : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih L acc => sN (facW RD RW EL EW j l (Nat.land L (ones (nat_lit 21)))) (fun fw =>
      Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
        (sN (wCat (Nat.sub acc (nat_lit 1)) (Nat.sub fw (nat_lit 1)))
          (fun a => ih (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
        (B4A.andB (Nat.blt (nat_lit 0) acc) (Nat.blt (nat_lit 0) fw))))

private theorem elFold_succ (RD RW EL EW : ℕ → ℕ) (j l k L acc : ℕ) :
    elFold RD RW EL EW j l (k + 1) L acc =
      if 0 < acc ∧ 0 < facW RD RW EL EW j l (L &&& ones 21) then
        elFold RD RW EL EW j l k (L >>> 21)
          (wCat (acc - 1) (facW RD RW EL EW j l (L &&& ones 21) - 1) + 1)
      else 0 := by
  rw [show elFold RD RW EL EW j l (k + 1) L acc = sN (facW RD RW EL EW j l (L &&& ones 21))
      (fun fw => Bool.rec (motive := fun _ => ℕ) 0 (sN (wCat (acc - 1) (fw - 1))
        (fun a => elFold RD RW EL EW j l k (L >>> 21) (a + 1)))
        (B4A.andB (Nat.blt 0 acc) (Nat.blt 0 fw))) from rfl]
  simp only [sN_eq']
  by_cases ha : 0 < acc
  · by_cases hf : 0 < facW RD RW EL EW j l (L &&& ones 21)
    · rw [Nat.blt_eq.mpr ha, Nat.blt_eq.mpr hf, if_pos ⟨ha, hf⟩]
      rfl
    · have hb : Nat.blt 0 (facW RD RW EL EW j l (L &&& ones 21)) = false := by
        cases e : Nat.blt 0 (facW RD RW EL EW j l (L &&& ones 21))
        · rfl
        · exact absurd (Nat.blt_eq.mp e) hf
      rw [Nat.blt_eq.mpr ha, hb, if_neg fun h => hf h.2]
      rfl
  · have hb : Nat.blt 0 acc = false := by
      cases e : Nat.blt 0 acc
      · rfl
      · exact absurd (Nat.blt_eq.mp e) ha
    rw [hb, if_neg fun h => ha h.1]
    rfl

private theorem elFold_good {RD RW EL EW : ℕ → ℕ} {j l : ℕ}
    {S : Subgroup (Equiv.Perm (Fin 31671))}
    (hfac : ∀ f, 0 < facW RD RW EL EW j l f → wInH (facW RD RW EL EW j l f - 1) = true ∧
      wLen (facW RD RW EL EW j l f - 1) < 2 ^ 16 ∧
      ρ (wVal (yGen 4 3 2) (facW RD RW EL EW j l f - 1)) ∈ S) :
    ∀ k L acc, 0 < elFold RD RW EL EW j l k L acc → wInH (acc - 1) = true →
      ρ (wVal (yGen 4 3 2) (acc - 1)) ∈ S → wLen (acc - 1) + 65535 * k < 2 ^ 32 →
      wInH (elFold RD RW EL EW j l k L acc - 1) = true ∧
      ρ (wVal (yGen 4 3 2) (elFold RD RW EL EW j l k L acc - 1)) ∈ S ∧
      wLen (elFold RD RW EL EW j l k L acc - 1) ≤ wLen (acc - 1) + 65535 * k
  | 0, _, _, _, h1, h2, _ => ⟨h1, h2, Nat.le_add_right _ _⟩
  | k + 1, L, acc, h, h1, h2, hlen => by
    rw [elFold_succ] at h ⊢
    have hc : 0 < acc ∧ 0 < facW RD RW EL EW j l (L &&& ones 21) := by
      by_contra hc
      rw [if_neg hc] at h
      exact lt_irrefl 0 h
    rw [if_pos hc] at h ⊢
    obtain ⟨f1, f2, f3⟩ := hfac _ hc.2
    have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
    have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
    have hl2 : wLen (acc - 1) + wLen (facW RD RW EL EW j l (L &&& ones 21) - 1) < 2 ^ 32 := by
      rw [h32] at hlen ⊢
      rw [h16] at f2
      omega
    have hcl := stL_wLen_wCat hl2
    have hci := stL_wInH_wCat hl2 h1 f1
    have hcv : ρ (wVal (yGen 4 3 2)
        (wCat (acc - 1) (facW RD RW EL EW j l (L &&& ones 21) - 1))) ∈ S := by
      show ρ (evalWord _ (wList (wCat _ _))) ∈ S
      rw [stL_val_wCat _ hl2 (stL_wOK_of_wInH h1), map_mul]
      exact S.mul_mem h2 f3
    obtain ⟨r1, r2, r3⟩ := elFold_good hfac k (L >>> 21) _ h
      (by rw [Nat.add_sub_cancel]; exact hci) (by rw [Nat.add_sub_cancel]; exact hcv)
      (by rw [Nat.add_sub_cancel, hcl, h32]; rw [h32] at hlen; rw [h16] at f2; omega)
    rw [Nat.add_sub_cancel, hcl] at r3
    rw [h16] at f2
    exact ⟨r1, r2, by omega⟩

private theorem elOK_prod {RD RW EL EW : ℕ → ℕ} {CB e : ℕ}
    (h : elOK LP RD RW EL EW CB e = true) :
    0 < elFold RD RW EL EW (elJ (EL e)) (elL (EL e)) (elM (EL e)) (EL e >>> 28) 1 ∧
      isOne LP (wCat (wRev (EW e)) (elFold RD RW EL EW (elJ (EL e)) (elL (EL e)) (elM (EL e))
        (EL e >>> 28) 1 - 1)) = true := by
  unfold elOK at h
  simp only [sB_eq'] at h
  obtain ⟨-, h2, -, h4, -⟩ := by simpa only [andB_iff'] using h
  exact ⟨Nat.blt_eq.mp h2, h4⟩

theorem member_sound_bdd {RD RW EL EW : ℕ → ℕ} {bs : ℕ → ℕ → ℕ}
    (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    (hRWl : ∀ g, isStab (dKind (RD g)) = true → wLen (RW g) < 2 ^ 16)
    (hEWl : ∀ e, EL e ≠ 0 → wLen (EW e) < 2 ^ 16)
    (hone : ∀ w, wInH w = true → isOne LP w = true → ρ (wVal (yGen 4 3 2) w) = 1)
    (hel : ∀ e, EL e ≠ 0 → elOK LP RD RW EL EW (cbOf' (bs (elJ (EL e))) (elL (EL e))) e = true) :
    ∀ e, EL e ≠ 0 → ρ (wVal (yGen 4 3 2) (EW e)) ∈
      (Subgroup.closure ((fun g => wVal (yGen 4 3 2) (RW g)) ''
        {g | isStab (dKind (RD g)) = true ∧ dN2 (RD g) = elJ (EL e)})).map ρ := by
  set S : ℕ → Subgroup (Equiv.Perm (Fin 31671)) := fun j =>
    (Subgroup.closure ((fun g => wVal (yGen 4 3 2) (RW g)) ''
      {g | isStab (dKind (RD g)) = true ∧ dN2 (RD g) = j})).map ρ with hS
  have h32 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have hinv : ∀ c, yGen 4 3 2 c * yGen 4 3 2 c = 1 := yGen_mul_self 4 3 2
  have hrev : ∀ {w j}, wInH w = true → ρ (wVal (yGen 4 3 2) w) ∈ S j →
      wInH (wRev w) = true ∧ wLen (wRev w) = wLen w ∧ ρ (wVal (yGen 4 3 2) (wRev w)) ∈ S j :=
    fun {w j} hw hv => ⟨stL_wInH_wRev (stL_wAt_lt_of_wInH hw), stL_wLen_wRev w, by
      show ρ (evalWord _ (wList (wRev w))) ∈ S j
      rw [stL_val_wRev hinv, map_inv]
      exact (S j).inv_mem hv⟩
  have hel0 : elL 0 = 0 := rfl
  have key : ∀ l e, EL e ≠ 0 → elL (EL e) = l → ρ (wVal (yGen 4 3 2) (EW e)) ∈ S (elJ (EL e)) := by
    intro l
    induction l with
    | zero =>
      intro e he hl
      have := (elOK_facts (hel e he)).1
      omega
    | succ l ih =>
      intro e he hl
      have hok := hel e he
      obtain ⟨-, hwi, -⟩ := elOK_facts hok
      obtain ⟨hP, hP1⟩ := elOK_prod hok
      rw [hl] at hP hP1
      set j := elJ (EL e)
      have hfac : ∀ f, 0 < facW RD RW EL EW j (l + 1) f →
          wInH (facW RD RW EL EW j (l + 1) f - 1) = true ∧
          wLen (facW RD RW EL EW j (l + 1) f - 1) < 2 ^ 16 ∧
          ρ (wVal (yGen 4 3 2) (facW RD RW EL EW j (l + 1) f - 1)) ∈ S j := by
        intro f hf
        obtain ⟨hf1, hf2⟩ := facW_spec hf
        by_cases hl0 : l + 1 = 1
        · obtain ⟨hs, hd, hw⟩ := hf1 hl0
          have hv : ρ (wVal (yGen 4 3 2) (RW (f >>> 1))) ∈ S j :=
            Subgroup.mem_map_of_mem ρ (Subgroup.subset_closure ⟨_, ⟨hs, hd⟩, rfl⟩)
          rcases hw with hw | hw <;> rw [hw]
          · exact ⟨hrw _ hs, hRWl _ hs, hv⟩
          · obtain ⟨r1, r2, r3⟩ := hrev (hrw _ hs) hv
            exact ⟨r1, r2 ▸ hRWl _ hs, r3⟩
        · obtain ⟨hj, hl', hw⟩ := hf2 hl0
          have hg0 : EL (f >>> 1) ≠ 0 := fun h0 => by
            rw [h0, hel0] at hl'
            omega
          have hgi := (elOK_facts (hel _ hg0)).2.1
          have hv := ih _ hg0 (by rw [hl']; omega)
          rw [hj] at hv
          rcases hw with hw | hw <;> rw [hw]
          · exact ⟨hgi, hEWl _ hg0, hv⟩
          · obtain ⟨r1, r2, r3⟩ := hrev hgi hv
            exact ⟨r1, r2 ▸ hEWl _ hg0, r3⟩
      have hm : elM (EL e) ≤ 65535 := Nat.and_le_right
      obtain ⟨p1, p2, p3⟩ := elFold_good hfac (elM (EL e)) (EL e >>> 28) 1 hP (by decide +kernel)
        (by
          show ρ (evalWord _ (wList 0)) ∈ S j
          rw [stL_wList_zero, show evalWord (yGen 4 3 2) [] = 1 from rfl, map_one]
          exact (S j).one_mem)
        (by rw [Nat.sub_self, stL_wLen_zero, h32]; omega)
      rw [Nat.sub_self, stL_wLen_zero] at p3
      have hEl := hEWl e he
      have hlen : wLen (wRev (EW e)) + wLen (elFold RD RW EL EW j (l + 1) (elM (EL e))
          (EL e >>> 28) 1 - 1) < 2 ^ 32 := by
        rw [stL_wLen_wRev, h32]
        rw [h16] at hEl
        omega
      have h1 := hone _ (stL_wInH_wCat hlen (stL_wInH_wRev (stL_wAt_lt_of_wInH hwi)) p1) hP1
      change ρ (evalWord _ (wList (wCat _ _))) = 1 at h1
      rw [stL_val_wCat _ hlen (stL_wOK_wRev _), stL_val_wRev hinv, map_mul, map_inv,
        inv_mul_eq_one] at h1
      change ρ (evalWord _ (wList (EW e))) ∈ S j
      rw [h1]
      exact p2
  intro e he
  exact key _ e he rfl

@[expose] def omSet (E : ℕ) : Set (Fin 412896) := {x | E.testBit x = true}

theorem om_sound {MS CB : ℕ → ℕ} {R : ℕ} (hm : masksOK19 MS = true)
    (hnc : ∀ c < 10, ∀ b < 19, netColOK MS CB c b = true)
    (htag : ∀ c < 10, ∀ b < 128, CB (256 * c + b) >>> 81920 = b)
    (hrel : ∀ w ∈ yRels 4 3 2 ++ [(List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten], relOK MS w = true)
    (horb : omOrbitOK MS R = true) :
    ∃ ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896),
      (∀ c < 10, ∀ x : Fin 412896, (ρΩ (yGen 4 3 2 c) x : ℕ) = colAt CB c x) ∧
      evalWord (yGen 4 3 2) (List.replicate 9 [0, 5, 6, 7, 8, 9, 1]).flatten ∈ ρΩ.ker ∧
      (∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
        omSet (netApp19 MS c E) = ρΩ (yGen 4 3 2 c) '' omSet E) ∧
      ∀ x : Fin 412896, x ∈ MulAction.orbit ρΩ.range (0 : Fin 412896) :=
  om_sound_aux hm hnc htag hrel horb

theorem cover_sound {MS RD RW PW CB RN RL GS GN XO SJ ST SA SN STL : ℕ → ℕ} {LIVE NS j : ℕ}
    (ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896))
    (hrw : ∀ g, isStab (dKind (RD g)) = true → wInH (RW g) = true)
    (hpw : ∀ p, wInH (PW p) = true)
    (hcol : ∀ c < 10, ∀ x : Fin 412896, (ρΩ (yGen 4 3 2 c) x : ℕ) = colAt CB c x)
    (hnet : ∀ c < 10, ∀ E < 2 ^ 412896, netApp19 MS c E < 2 ^ 412896 ∧
      omSet (netApp19 MS c E) = ρΩ (yGen 4 3 2 c) '' omSet E)
    (hsa0 : SA 0 = 0)
    (hseg : ∀ k < NS, segChk MS RD RW PW CB LIVE RN RL GS XO SJ ST SA SN STL NS k = true)
    (hfin : finChk RD RW PW CB LIVE RN RL GS GN XO SJ ST SA SN STL NS j = true)
    (hlive : 0 < LIVE &&& (1 <<< j)) :
    ∀ x : Fin 412896, ∃ i < RN j, entryOK RD LIVE j (fld (RL j) (20 * i) (ones 20)) = true ∧
      ∃ s ∈ Subgroup.closure ((fun t => ρΩ (wVal (yGen 4 3 2) (RW (genOf GS j t)))) '' {t | t < GN j}),
        x = s (ρΩ (wVal (yGen 4 3 2) (PW (dPt (RD (fld (RL j) (20 * i) (ones 20)))))) 0) :=
    cover_sound_aux ρΩ hrw hpw hcol hnet hsa0 hseg hfin hlive

end CFSG.KC.B433Alt

end
