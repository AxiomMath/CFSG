module

public import CFSG.Certificates.Kernel.LceSP.Loops
public import Certificates.Data.Kernel.LceSHeRu
import CFSG.Certificates.Kernel.LceSP.Main
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.KC.LabG

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop
open CFSG.KC.HeB hiding labInv lpush pushFwd pushInv pushLab labGo labWalk labStep labChunk runLab
  cycLab cycRed cycOK

@[expose] noncomputable def lpush (li : Nat → Nat) (K x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (mkK (Nat.succ (kCnt K)) (Nat.add (Nat.mul (kStk K) (nat_lit 256)) (Nat.succ x)))
    (mkK (Nat.sub (kCnt K) (nat_lit 1)) (Nat.shiftRight (kStk K) (nat_lit 8)))
    (andB (Nat.blt (nat_lit 0) (kCnt K))
      (Nat.beq (Nat.land (kStk K) (nat_lit 255)) (Nat.succ (li x))))

@[expose] noncomputable def pushFwd (li : Nat → Nat) (L acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (lpush li a (Nat.sub (kByte L k) (nat_lit 1))) ih) (kCnt L) acc

@[expose] noncomputable def pushInv (li : Nat → Nat) (L acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (lpush li a (li (Nat.sub (kByte L (Nat.sub (Nat.sub (kCnt L) (nat_lit 1)) k))
      (nat_lit 1)))) ih) (kCnt L) acc

@[expose] noncomputable def pushLab (li : Nat → Nat) (L dir acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pushFwd li L acc) (pushInv li L acc) (Nat.beq dir (nat_lit 1))

@[expose] noncomputable def labGo (li : Nat → Nat) (LB : Nat → Nat) (Li ft n : Nat) (k : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun k ih R acc => Bool.rec (motive := fun _ => Nat)
      ((fun e => strictN (pushLab li (LB (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc)
          (ih (Nat.shiftRight R (nat_lit 32))))
        (Nat.land R (nat_lit 4294967295)))
      (strictN (pushFwd li Li acc) (ih R))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def labWalk (li : Nat → Nat) (LB : Nat → Nat) (i J w h : Nat) : Bool :=
  Nat.beq (labGo li LB (LB i) (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w)
      (wLen w) (Nat.shiftRight J (nat_lit 53)) (nat_lit 0))
    (target w h)

@[expose] noncomputable def labStep (li : Nat → Nat) (LB : Nat → Nat) (Hs J S w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (LB (Nat.sub S (nat_lit 1))) (nat_lit 0)))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (labWalk li LB (Nat.sub S (nat_lit 1)) J w
          (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunk (li : Nat → Nat) (WT LB : Nat → Nat) (Hs C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStep li LB Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStep li LB Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLab (li : Nat → Nat) (WT LB : Nat → Nat) (Hs : Nat) (Cs : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunk li WT LB Hs C S) ih) Cs

@[expose] noncomputable def cycLab (li : Nat → Nat) (LB : Nat → Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih R acc => (fun e => strictN (pushLab li (LB (Nat.shiftRight e (nat_lit 1)))
        (Nat.land e (nat_lit 1)) acc) (ih (Nat.shiftRight R (nat_lit 32))))
      (Nat.land R (nat_lit 4294967295))) k

@[expose] noncomputable def cycRed (li : Nat → Nat) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun P => P) (fun _ ih P =>
    Bool.rec (motive := fun _ => Nat) P
      (strictN (mkK (Nat.sub (kCnt P) (nat_lit 2))
        (Nat.shiftRight (Nat.land (kStk P) (Nat.sub (Nat.shiftLeft (nat_lit 1)
          (Nat.mul (nat_lit 8) (Nat.sub (kCnt P) (nat_lit 1)))) (nat_lit 1))) (nat_lit 8))) ih)
      (andB (Nat.ble (nat_lit 2) (kCnt P))
        (Nat.beq (kByte P (Nat.sub (kCnt P) (nat_lit 1)))
          (Nat.succ (li (Nat.sub (kByte P (nat_lit 0)) (nat_lit 1)))))))
    (Nat.shiftRight (kCnt K) (nat_lit 1)) K

@[expose] noncomputable def cycOK (li : Nat → Nat) (blk WT LB : Nat → Nat) (nf c wid R rho : Nat) :
    Bool :=
  letB (WT wid) (fun w => andB (Nat.beq (wKind w) (nat_lit 2))
    (andB (Nat.beq (cycWalk blk nf (wLen w) R (wStart c (wWord w))) (Nat.add c (nat_lit 1048576)))
      (Nat.beq (cycRed li (cycLab li LB (wLen w) R (nat_lit 0))) rho)))

@[expose] noncomputable def coneOk (li : Nat → Nat) (blk WT RT ST LB : Nat → Nat)
    (INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat) (Cs : List Nat) : Bool :=
  andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (invOK INV INV8 L)
  (andB (Nat.beq nC nCa)
  (andB (Nat.ble nCa (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nCa))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq X1 (Nat.succ nf))
  (andB (hintsLt WT m (nat_lit 2) Hs)
  (andB (labsWF LB nf)
  (andB (Nat.beq (LceSR.runIds WT m Cs (nat_lit 1)) (nat_lit 1))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
    (Nat.beq (runLab li WT LB Hs Cs X0) X1)))))))))))))

theorem he_coneOk (blk WT RT ST LB : Nat → Nat) (INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat)
    (Cs : List Nat) :
    CFSG.Certificates.LS.He.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs =
      coneOk HeB.labInv blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs := rfl

theorem ru_coneOk (blk WT RT ST LB : Nat → Nat) (INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : Nat)
    (Cs : List Nat) :
    CFSG.Certificates.LS.Ru.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs =
      coneOk RuB.labInv blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs := rfl

theorem he_cycOK (blk WT LB : Nat → Nat) (nf c wid R rho : Nat) :
    HeB.cycOK blk WT LB nf c wid R rho = cycOK HeB.labInv blk WT LB nf c wid R rho := rfl

theorem ru_cycOK (blk WT LB : Nat → Nat) (nf c wid R rho : Nat) :
    RuB.cycOK blk WT LB nf c wid R rho = cycOK RuB.labInv blk WT LB nf c wid R rho := rfl

theorem ru_entStk (E : Nat) : RuB.entStk E = entStk E := rfl

end CFSG.KC.LabG

namespace CFSG.Certificates.LceP.HeL

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.KC.LabG CFSG.Certificates.LceP
open CFSG.KC.HeB hiding labInv lpush pushFwd pushInv pushLab labGo labWalk labStep labChunk runLab
  cycLab cycRed cycOK

theorem kCnt_eq (K : ℕ) : kCnt K = K % 16777216 := by
  have h := land_lit K 24 16777215 (by norm_num)
  norm_num at h
  exact h

theorem kStk_eq (K : ℕ) : kStk K = K / 16777216 := by
  have h := shr_eq K 24
  norm_num at h
  exact h

theorem kCnt_lt (K : ℕ) : kCnt K < 16777216 := by
  rw [kCnt_eq]
  omega

theorem mkK_eq {c : ℕ} (s : ℕ) (hc : c < 16777216) : mkK c s = c + s * 16777216 := by
  have h := lor_shl (a := c) (b := s) (k := 24) (by norm_num; exact hc)
  norm_num at h
  exact h

theorem kCnt_mkK {c : ℕ} (s : ℕ) (hc : c < 16777216) : kCnt (mkK c s) = c := by
  rw [kCnt_eq, mkK_eq s hc]
  omega

theorem kStk_mkK {c : ℕ} (s : ℕ) (hc : c < 16777216) : kStk (mkK c s) = s := by
  rw [kStk_eq, mkK_eq s hc]
  omega

theorem kByte_eq (K i : ℕ) : kByte K i = kStk K / 256 ^ i % 256 := wLet_eq (kStk K) i

theorem kByte_lt (K i : ℕ) : kByte K i < 256 := by
  rw [kByte_eq]
  omega

@[expose] def digs (s : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => (s / 256 ^ k % 256) :: digs s k

theorem digs_succ' (s : ℕ) : ∀ k, digs s (k + 1) = digs (s / 256) k ++ [s % 256]
  | 0 => by simp [digs]
  | k + 1 => by
    rw [digs, digs_succ' s k, digs, Nat.div_div_eq_div_mul, ← pow_succ']
    rfl

theorem digs_ext {s t : ℕ} : ∀ k, (∀ j < k, s / 256 ^ j % 256 = t / 256 ^ j % 256) →
    digs s k = digs t k
  | 0, _ => rfl
  | k + 1, h => by
    rw [digs, digs, h k (by omega), digs_ext k (fun j hj => h j (by omega))]

theorem digs_mod (s k : ℕ) : digs (s % 256 ^ k) k = digs s k := by
  apply digs_ext
  intro j hj
  conv_rhs => rw [← Nat.mod_add_div s (256 ^ k), Nat.mul_comm]
  rw [byte_add_high hj]

variable {G : Type*} [Group G] (u : ℕ → G)

@[expose] def gv (b : ℕ) : G := lv u (b - 1)

@[expose] noncomputable def labCS (s k : ℕ) : G := ((digs s k).map (gv u)).prod

@[expose] noncomputable def lab (K : ℕ) : G := labCS u (kStk K) (kCnt K)

@[expose] def Clean (K : ℕ) : Prop :=
  kStk K < 256 ^ kCnt K ∧ ∀ b ∈ digs (kStk K) (kCnt K), b ≠ 0

theorem labCS_succ (s k : ℕ) : labCS u s (k + 1) = gv u (s / 256 ^ k % 256) * labCS u s k := by
  simp [labCS, digs]

theorem labCS_succ' (s k : ℕ) : labCS u s (k + 1) = labCS u (s / 256) k * gv u (s % 256) := by
  simp [labCS, digs_succ']

theorem lab_zero : lab u 0 = 1 := by
  simp [lab, labCS, kCnt_eq, digs]

theorem clean_zero : Clean 0 := by
  simp [Clean, kCnt_eq, kStk_eq, digs]

theorem lab_mkK {c : ℕ} (s : ℕ) (hc : c < 16777216) : lab u (mkK c s) = labCS u s c := by
  rw [lab, kCnt_mkK s hc, kStk_mkK s hc]

theorem clean_mkK {c : ℕ} (s : ℕ) (hc : c < 16777216) :
    Clean (mkK c s) ↔ s < 256 ^ c ∧ ∀ b ∈ digs s c, b ≠ 0 := by
  rw [Clean, kCnt_mkK s hc, kStk_mkK s hc]

structure LIOk (li : ℕ → ℕ) : Prop where
  le : ∀ x ≤ 253, li x ≤ 253
  top : li 254 = 255
  inv : ∀ x ≤ 253, lv u (li x) = (lv u x)⁻¹

theorem liOk_of {li : ℕ → ℕ} {a : ℕ} (ha : a ≤ 253)
    (he : ∀ x, li x = if x = a then a else x ^^^ 1) (hu : lv u a * lv u a = 1) : LIOk u li := by
  refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
  · rw [he]
    split_ifs
    · exact ha
    · rw [xor_one_cases x (by omega)]
      split_ifs <;> omega
  · have h254 : ¬(254 = a) := by omega
    rw [he, ite_eq_right h254]
    decide
  · rw [he]
    split_ifs with h0
    · subst h0
      rw [eq_inv_iff_mul_eq_one]
      exact hu
    · exact lv_xor_one u (by omega)

theorem he_labInv (x : ℕ) : HeB.labInv x = if x = 0 then 0 else x ^^^ 1 := by
  unfold HeB.labInv
  rw [brec_eq]
  by_cases hx : x = 0
  · subst hx
    rfl
  · have : Nat.beq x 0 = false := by
      cases h : Nat.beq x 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hx
    rw [this]
    simp [hx]

theorem ru_labInv (x : ℕ) : RuB.labInv x = if x = 2 then 2 else x ^^^ 1 := by
  unfold RuB.labInv
  rw [brec_eq]
  by_cases hx : x = 2
  · subst hx
    rfl
  · have : Nat.beq x 2 = false := by
      cases h : Nat.beq x 2
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hx
    rw [this]
    simp [hx]

theorem he_liOk (hu : u 0 * u 0 = 1) : LIOk u HeB.labInv :=
  liOk_of u (a := 0) (by norm_num) he_labInv (by simpa [lv] using hu)

theorem ru_liOk (hu : u 1 * u 1 = 1) : LIOk u RuB.labInv :=
  liOk_of u (a := 2) (by norm_num) ru_labInv (by simpa [lv] using hu)

variable {li : ℕ → ℕ}

theorem lpush_spec (hli : LIOk u li) {K x : ℕ} (hc : kCnt K + 1 < 16777216) (hx : x ≤ 254)
    (hK : Clean K) :
    Clean (lpush li K x) ∧ kCnt (lpush li K x) ≤ kCnt K + 1 ∧ lab u (lpush li K x) = lab u K * lv u x := by
  obtain ⟨hs, hnz⟩ := hK
  unfold lpush
  rw [brec_eq]
  split_ifs with hcan
  · simp only [andB_iff, Nat.blt_eq, Nat.beq_eq, land8] at hcan
    obtain ⟨hpos, htop⟩ := hcan
    obtain ⟨c, hc'⟩ : ∃ c, kCnt K = c + 1 := ⟨kCnt K - 1, by omega⟩
    have hx' : x ≤ 253 := by
      rcases Nat.lt_or_ge x 254 with h | h
      · omega
      · have : x = 254 := by omega
        subst this
        rw [hli.top] at htop
        omega
    have e1 : Nat.sub (kCnt K) 1 = c := by
      change kCnt K - 1 = c
      omega
    have e2 : Nat.shiftRight (kStk K) 8 = kStk K / 256 := by
      rw [shr_eq]
      norm_num
    rw [e1, e2, clean_mkK _ (by omega), lab_mkK u _ (by omega), kCnt_mkK _ (by omega)]
    rw [hc', digs_succ'] at hnz
    rw [hc'] at hs
    refine ⟨⟨?_, fun b hb => hnz b (List.mem_append_left _ hb)⟩, by omega, ?_⟩
    · rw [pow_succ] at hs
      exact (Nat.div_lt_iff_lt_mul (by norm_num)).2 hs
    · unfold lab
      rw [hc', labCS_succ', htop]
      unfold gv
      rw [Nat.succ_sub_one, mul_assoc, hli.inv _ hx', inv_mul_cancel, mul_one]
  · have hc1 : kCnt K + 1 < 16777216 := hc
    have e1 : Nat.succ (kCnt K) = kCnt K + 1 := rfl
    have e2 : Nat.add (Nat.mul (kStk K) 256) (Nat.succ x) = kStk K * 256 + (x + 1) := rfl
    rw [e1, e2, clean_mkK _ hc1, lab_mkK u _ hc1, kCnt_mkK _ hc1]
    have ed : digs (kStk K * 256 + (x + 1)) (kCnt K + 1) = digs (kStk K) (kCnt K) ++ [x + 1] := by
      rw [digs_succ']
      congr 2
      · omega
      · omega
    refine ⟨⟨?_, ?_⟩, le_rfl, ?_⟩
    · rw [pow_succ]
      have := hs
      generalize 256 ^ kCnt K = P at this ⊢
      omega
    · rw [ed]
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hnz b hb
      · rw [List.mem_singleton] at hb
        omega
    · unfold lab labCS
      rw [ed, List.map_append, List.prod_append]
      simp [gv]

@[expose] noncomputable def pf (li : ℕ → ℕ) (L : ℕ) (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (lpush li a (Nat.sub (kByte L k) (nat_lit 1))) ih) k

theorem pf_succ (li : ℕ → ℕ) (L k a : ℕ) :
    pf li L (k + 1) a = pf li L k (lpush li a (Nat.sub (kByte L k) 1)) :=
  strictN_eq _ _

@[expose] noncomputable def pinv (li : ℕ → ℕ) (L : ℕ) (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (lpush li a (li (Nat.sub (kByte L (Nat.sub (Nat.sub (kCnt L)
      (nat_lit 1)) k)) (nat_lit 1)))) ih) k

theorem pinv_succ (li : ℕ → ℕ) (L k a : ℕ) : pinv li L (k + 1) a =
    pinv li L k (lpush li a (li (Nat.sub (kByte L (Nat.sub (Nat.sub (kCnt L) 1) k)) 1))) :=
  strictN_eq _ _

theorem pushFwd_gen (hli : LIOk u li) (L : ℕ) : ∀ k a, Clean a → kCnt a + k < 16777216 →
    Clean (pf li L k a) ∧ kCnt (pf li L k a) ≤ kCnt a + k ∧
      lab u (pf li L k a) = lab u a * labCS u (kStk L) k
  | 0, a, ha, _ => ⟨ha, le_refl _, by simp [pf, labCS, digs]⟩
  | k + 1, a, ha, hc => by
    rw [pf_succ]
    have hb := kByte_lt L k
    obtain ⟨h1, h2, h3⟩ := lpush_spec u hli (K := a) (x := Nat.sub (kByte L k) 1) (by omega)
      (by change kByte L k - 1 ≤ 254; omega) ha
    obtain ⟨i1, i2, i3⟩ := pushFwd_gen hli L k _ h1 (by omega)
    refine ⟨i1, by omega, ?_⟩
    rw [i3, h3, labCS_succ, mul_assoc, ← kByte_eq]
    rfl

theorem pushFwd_spec (hli : LIOk u li) {L acc : ℕ} (ha : Clean acc)
    (hc : kCnt acc + kCnt L < 16777216) :
    Clean (pushFwd li L acc) ∧ kCnt (pushFwd li L acc) ≤ kCnt acc + kCnt L ∧
      lab u (pushFwd li L acc) = lab u acc * lab u L :=
  pushFwd_gen u hli L (kCnt L) acc ha hc

theorem pushInv_gen (hli : LIOk u li) (L : ℕ) (hW : ∀ j < kCnt L, kByte L j ≠ 255) :
    ∀ k ≤ kCnt L, ∀ a, Clean a → kCnt a + k < 16777216 →
    Clean (pinv li L k a) ∧ kCnt (pinv li L k a) ≤ kCnt a + k ∧
      lab u (pinv li L k a) =lab u a * (labCS u (kStk L / 256 ^ (kCnt L - k)) k)⁻¹
  | 0, _, a, ha, _ => ⟨ha, le_refl _, by simp [pinv, labCS, digs]⟩
  | k + 1, hk, a, ha, hc => by
    rw [pinv_succ]
    have ej : Nat.sub (Nat.sub (kCnt L) 1) k = kCnt L - (k + 1) := by
      change kCnt L - 1 - k = _
      omega
    rw [ej]
    have hb := kByte_lt L (kCnt L - (k + 1))
    have hb' := hW (kCnt L - (k + 1)) (by omega)
    have hy : Nat.sub (kByte L (kCnt L - (k + 1))) 1 ≤ 253 := by
      change kByte L (kCnt L - (k + 1)) - 1 ≤ 253
      omega
    obtain ⟨h1, h2, h3⟩ := lpush_spec u hli (K := a) (by omega)
      (le_trans (hli.le _ hy) (by norm_num)) ha
    obtain ⟨i1, i2, i3⟩ := pushInv_gen hli L hW k (by omega) _ h1 (by omega)
    refine ⟨i1, by omega, ?_⟩
    rw [i3, h3, hli.inv _ hy, labCS_succ', Nat.div_div_eq_div_mul, ← pow_succ,
      show kCnt L - (k + 1) + 1 = kCnt L - k by omega, mul_inv_rev, mul_assoc, ← kByte_eq]
    rfl

theorem pushInv_spec (hli : LIOk u li) {L acc : ℕ} (hW : ∀ j < kCnt L, kByte L j ≠ 255)
    (ha : Clean acc) (hc : kCnt acc + kCnt L < 16777216) :
    Clean (pushInv li L acc) ∧ kCnt (pushInv li L acc) ≤ kCnt acc + kCnt L ∧
      lab u (pushInv li L acc) = lab u acc * (lab u L)⁻¹ := by
  have h := pushInv_gen u hli L hW (kCnt L) le_rfl acc ha hc
  rw [Nat.sub_self, pow_zero, Nat.div_one] at h
  exact h

theorem labWF_spec {K : ℕ} (h : labWF K = true) : kCnt K < 8192 ∧ ∀ j < kCnt K, kByte K j ≠ 255 := by
  unfold labWF at h
  rw [andB_iff, Nat.blt_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  have h1 := (allRec2_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      andB ((fun i => Bool.rec (motive := fun _ => Bool) true
        (notB (Nat.beq (kByte K i) (nat_lit 255))) (Nat.blt i (kCnt K)))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) (Nat.succ (Nat.shiftRight (kCnt K) 6))).1 h.2
      (j / 64) (by
      change j / 64 < (kCnt K >>> 6) + 1
      rw [Nat.shiftRight_eq_div_pow]
      omega)
  have h2 := (allRec2_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true
      (notB (Nat.beq (kByte K i) (nat_lit 255))) (Nat.blt i (kCnt K)))
      (Nat.add (Nat.shiftLeft (j / 64) 6) l)) 64).1 h1 (j % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (j / 64) 6) (j % 64) = j := by
    change (j / 64) <<< 6 + j % 64 = j
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt j (kCnt K) = true := by
    rw [Nat.blt_eq]
    exact hj
  dsimp only at h2
  rw [e, hb] at h2
  intro h255
  rw [h255] at h2
  exact absurd h2 (by decide)

theorem pushLab_spec (hli : LIOk u li) {L dir acc : ℕ} (hL : labWF L = true) (ha : Clean acc)
    (hc : kCnt acc + 8192 < 16777216) :
    Clean (pushLab li L dir acc) ∧ kCnt (pushLab li L dir acc) ≤ kCnt acc + 8192 ∧
      lab u (pushLab li L dir acc) = lab u acc * (if dir = 1 then (lab u L)⁻¹ else lab u L) := by
  obtain ⟨hn, hW⟩ := labWF_spec hL
  unfold pushLab
  rw [brec_eq]
  by_cases hd : dir = 1
  · have hb : Nat.beq dir 1 = true := by
      rw [Nat.beq_eq]
      exact hd
    rw [ite_eq_left hb, ite_eq_left hd]
    obtain ⟨h1, h2, h3⟩ := pushInv_spec u hli (L := L) (acc := acc) hW ha (by omega)
    exact ⟨h1, by omega, h3⟩
  · have hb : ¬Nat.beq dir 1 = true := by
      rw [Nat.beq_eq]
      exact hd
    rw [ite_eq_right hb, ite_eq_right hd]
    obtain ⟨h1, h2, h3⟩ := pushFwd_spec u hli (L := L) (acc := acc) ha (by omega)
    exact ⟨h1, by omega, h3⟩

@[expose] noncomputable def cStep (P : ℕ) : ℕ :=
  mkK (Nat.sub (kCnt P) (nat_lit 2))
    (Nat.shiftRight (Nat.land (kStk P) (Nat.sub (Nat.shiftLeft (nat_lit 1)
      (Nat.mul (nat_lit 8) (Nat.sub (kCnt P) (nat_lit 1)))) (nat_lit 1))) (nat_lit 8))

@[expose] noncomputable def cCond (li : ℕ → ℕ) (P : ℕ) : Bool :=
  andB (Nat.ble (nat_lit 2) (kCnt P))
    (Nat.beq (kByte P (Nat.sub (kCnt P) (nat_lit 1)))
      (Nat.succ (li (Nat.sub (kByte P (nat_lit 0)) (nat_lit 1)))))

@[expose] noncomputable def cRec (li : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun P => P) (fun _ ih P =>
    Bool.rec (motive := fun _ => Nat) P (strictN (cStep P) ih) (cCond li P)) k

theorem cycRed_eq (li : ℕ → ℕ) (K : ℕ) : cycRed li K = cRec li (Nat.shiftRight (kCnt K) 1) K := rfl

theorem cRec_succ (li : ℕ → ℕ) (k P : ℕ) :
    cRec li (k + 1) P = if cCond li P = true then cRec li k (cStep P) else P := by
  change Bool.rec (motive := fun _ => Nat) P (strictN (cStep P) (cRec li k)) (cCond li P) = _
  rw [brec_eq, strictN_eq]

theorem cStep_spec (hli : LIOk u li) {P : ℕ} (hP : Clean P) (h1 : lab u P = 1)
    (hc : cCond li P = true) : Clean (cStep P) ∧ lab u (cStep P) = 1 := by
  obtain ⟨hs, hnz⟩ := hP
  unfold cCond at hc
  rw [andB_iff, Nat.ble_eq, Nat.beq_eq] at hc
  obtain ⟨h2, htop⟩ := hc
  have h2' : 2 ≤ kCnt P := h2
  obtain ⟨c, hcP⟩ : ∃ c, kCnt P = c + 2 := ⟨kCnt P - 2, by omega⟩
  have hcl := kCnt_lt P
  have e1 : Nat.sub (kCnt P) 2 = c := by
    change kCnt P - 2 = c
    omega
  have e2 : Nat.sub (kCnt P) 1 = c + 1 := by
    change kCnt P - 1 = c + 1
    omega
  rw [e2] at htop
  set s := kStk P with hsdef
  have e3 : Nat.shiftRight (Nat.land s (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 (c + 1))) 1)) 8 =
      s % 256 ^ (c + 1) / 256 := by
    rw [land_mask, shr_eq]
    change s % 2 ^ (8 * (c + 1)) / 2 ^ 8 = _
    rw [two_pow_eight_mul]
    norm_num
  unfold cStep
  rw [e1, e2, ← hsdef, e3, clean_mkK _ (by omega), lab_mkK u _ (by omega)]
  have ed : digs s (c + 2) = (s / 256 ^ (c + 1) % 256) ::
      (digs (s % 256 ^ (c + 1) / 256) c ++ [s % 256]) := by
    rw [digs, ← digs_mod s (c + 1), digs_succ', Nat.mod_mod_of_dvd _ (dvd_pow_self 256 (by omega))]
  rw [hcP, ed] at hnz
  rw [hcP] at hs
  have hlast := hnz _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have hmod : s % 256 ^ (c + 1) < 256 ^ c * 256 := by
    rw [← pow_succ]
    exact Nat.mod_lt _ (by positivity)
  refine ⟨⟨(Nat.div_lt_iff_lt_mul (by norm_num)).2 hmod,
    fun b hb => hnz b (List.mem_cons_of_mem _ (List.mem_append_left _ hb))⟩, ?_⟩
  have hb0 : kByte P 0 = s % 256 := by
    rw [kByte_eq, ← hsdef, pow_zero, Nat.div_one]
  have hb1 : kByte P (c + 1) = s / 256 ^ (c + 1) % 256 := by
    rw [kByte_eq]
  rw [hb0, hb1] at htop
  have hy : s % 256 - 1 ≤ 253 := by
    rcases Nat.lt_or_ge (s % 256 - 1) 254 with h | h
    · omega
    · have : s % 256 - 1 = 254 := by omega
      have htop' := htop
      change _ = li (s % 256 - 1) + 1 at htop'
      rw [this, hli.top] at htop'
      omega
  unfold lab at h1
  rw [hcP, ← hsdef] at h1
  unfold labCS at h1
  rw [ed] at h1
  simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append] at h1
  have hg1 : gv u (s / 256 ^ (c + 1) % 256) = (lv u (s % 256 - 1))⁻¹ := by
    unfold gv
    rw [htop]
    change lv u (li (s % 256 - 1) + 1 - 1) = _
    rw [Nat.add_sub_cancel, hli.inv _ hy]
  rw [hg1] at h1
  unfold gv at h1
  simp only [List.map_nil, List.prod_nil, mul_one] at h1
  change (lv u (s % 256 - 1))⁻¹ * (labCS u (s % 256 ^ (c + 1) / 256) c * lv u (s % 256 - 1)) = 1
    at h1
  have : labCS u (s % 256 ^ (c + 1) / 256) c = lv u (s % 256 - 1) *
      ((lv u (s % 256 - 1))⁻¹ * (labCS u (s % 256 ^ (c + 1) / 256) c * lv u (s % 256 - 1))) *
      (lv u (s % 256 - 1))⁻¹ := by group
  rw [this, h1]
  group

theorem cRec_spec (hli : LIOk u li) : ∀ k P, Clean P → lab u P = 1 →
    Clean (cRec li k P) ∧ lab u (cRec li k P) = 1
  | 0, _, h1, h2 => ⟨h1, h2⟩
  | k + 1, P, h1, h2 => by
    rw [cRec_succ]
    split_ifs with hc
    · obtain ⟨i1, i2⟩ := cStep_spec u hli h1 h2 hc
      exact cRec_spec hli k _ i1 i2
    · exact ⟨h1, h2⟩

theorem cycRed_spec (hli : LIOk u li) {P : ℕ} (h1 : Clean P) (h2 : lab u P = 1) :
    Clean (cycRed li P) ∧ lab u (cycRed li P) = 1 := by
  rw [cycRed_eq]
  exact cRec_spec u hli _ P h1 h2

@[expose] noncomputable def eRec (W n : ℕ) (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun k ih s => strictN (Nat.add (Nat.mul s (nat_lit 256))
      (Nat.succ (wLet W (Nat.sub (Nat.sub n (nat_lit 1)) k)))) ih) k

theorem eRec_succ (W n k s : ℕ) :
    eRec W n (k + 1) s = eRec W n k (s * 256 + (wLet W (n - (k + 1)) + 1)) := by
  have h := strictN_eq (Nat.add (Nat.mul s 256) (Nat.succ (wLet W (Nat.sub (Nat.sub n 1) k))))
    (eRec W n k)
  have e : Nat.sub (Nat.sub n 1) k = n - (k + 1) := by
    change n - 1 - k = _
    omega
  refine h.trans ?_
  rw [e]
  rfl

theorem wLen_lt (E : ℕ) : wLen E < 1024 := by
  unfold wLen
  rw [land_lit _ 10 1023 (by norm_num)]
  exact Nat.mod_lt _ (by norm_num)

theorem eRec_gen (W n : ℕ) : ∀ k ≤ n, ∀ s m, eRec W n k s < 256 ^ (m + k) →
    (∀ b ∈ digs (eRec W n k s) (m + k), b ≠ 0) →
    s < 256 ^ m ∧ (∀ b ∈ digs s m, b ≠ 0) ∧ labCS u (eRec W n k s) (m + k) =
      labCS u s m * ((List.range k).map fun i => lv u (wLet W (n - k + i))).prod
  | 0, _, s, m, h1, h2 => ⟨h1, h2, by simp [eRec]⟩
  | k + 1, hk, s, m, h1, h2 => by
    rw [eRec_succ] at h1 h2 ⊢
    rw [show m + (k + 1) = (m + 1) + k by omega] at h1 h2 ⊢
    obtain ⟨i1, i2, i3⟩ := eRec_gen W n k (by omega) _ (m + 1) h1 h2
    have hl := wLet_lt W (n - (k + 1))
    rw [digs_succ'] at i2
    have hz := i2 _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hl' : wLet W (n - (k + 1)) ≤ 254 := by
      by_contra hc
      have : wLet W (n - (k + 1)) = 255 := by omega
      rw [this] at hz
      omega
    have ed : (s * 256 + (wLet W (n - (k + 1)) + 1)) / 256 = s := by omega
    have em : (s * 256 + (wLet W (n - (k + 1)) + 1)) % 256 = wLet W (n - (k + 1)) + 1 := by omega
    rw [ed, em] at i2
    refine ⟨?_, fun b hb => i2 b (List.mem_append_left _ hb), ?_⟩
    · rw [pow_succ] at i1
      generalize 256 ^ m = P at i1 ⊢
      omega
    · rw [i3, labCS_succ', ed, em, List.range_succ_eq_map, List.map_cons, List.prod_cons,
        List.map_map]
      unfold gv
      rw [Nat.add_sub_cancel, mul_assoc]
      congr 2
      refine congrArg List.prod (List.map_congr_left ?_)
      intro i _
      simp only [Function.comp_apply]
      congr 2
      omega

theorem entStk_spec {E : ℕ} (h : Clean (entStk E)) :
    lab u (entStk E) = bv u (wWord E) (wLen E) := by
  have hn := wLen_lt E
  have e : entStk E = mkK (wLen E) (eRec (wWord E) (wLen E) (wLen E) 0) := rfl
  rw [e] at h ⊢
  rw [clean_mkK _ (by omega)] at h
  rw [lab_mkK u _ (by omega)]
  have := eRec_gen u (wWord E) (wLen E) (wLen E) le_rfl 0 0 (by simpa using h.1)
    (by simpa using h.2)
  rw [Nat.zero_add] at this
  rw [this.2.2]
  simp [labCS, digs, bv]

section Walks

variable (gen : ℕ → G)

@[expose] def WL (rep : ℕ → G) (s W ft : ℕ) (a b : G) (p st acc : ℕ) : Prop :=
  st / 1048576 = 0 ∨ (Clean acc ∧ kCnt acc ≤ 8192 * p ∧ ∃ cur < 1048576,
    st = cur + 1048576 * (W / 256 ^ p) ∧
    (p ≤ ft → rep s * bv gen W p * (rep cur)⁻¹ = lab u acc) ∧
    (ft < p → ∃ A B : G, rep s * bv gen W p * (rep cur)⁻¹ = A * a * B ∧ lab u acc = A * b * B))

theorem WL_move {rep : ℕ → G} {s W ft p cur cur' acc acc' : ℕ} {a b g l : G}
    (hX1 : p ≤ ft → rep s * bv gen W p * (rep cur)⁻¹ = lab u acc)
    (hX2 : ft < p → ∃ A B : G, rep s * bv gen W p * (rep cur)⁻¹ = A * a * B ∧
      lab u acc = A * b * B)
    (hacc : lab u acc' = lab u acc * l)
    (hg : rep cur * lv gen (wLet W p) * (rep cur')⁻¹ = g)
    (hb : (p ≠ ft ∧ g = l) ∨ (p = ft ∧ g = a ∧ l = b)) :
    (p + 1 ≤ ft → rep s * bv gen W (p + 1) * (rep cur')⁻¹ = lab u acc') ∧
    (ft < p + 1 → ∃ A B : G, rep s * bv gen W (p + 1) * (rep cur')⁻¹ = A * a * B ∧
      lab u acc' = A * b * B) := by
  have e : rep s * bv gen W (p + 1) * (rep cur')⁻¹ =
      (rep s * bv gen W p * (rep cur)⁻¹) * (rep cur * lv gen (wLet W p) * (rep cur')⁻¹) := by
    rw [bv_succ]
    group
  rw [e, hg, hacc]
  rcases hb with ⟨hp, hgl⟩ | ⟨hp, hga, hlb⟩
  · refine ⟨fun _ => by rw [hX1 (by omega), hgl], fun h => ?_⟩
    obtain ⟨A, B, h1, h2⟩ := hX2 (by omega)
    refine ⟨A, B * g, ?_, ?_⟩
    · rw [h1]
      simp only [mul_assoc]
    · rw [h2, hgl]
      simp only [mul_assoc]
  · refine ⟨fun _ => by omega, fun _ => ⟨lab u acc, 1, ?_, ?_⟩⟩
    · rw [hX1 (le_of_eq hp), hga, mul_one]
    · rw [hlb, mul_one]

theorem WL_sF {rep : ℕ → G} {s W ft p st acc acc' R : ℕ} {a b l : G}
    (hI : WL u gen rep s W ft a b p st acc) (hp : p + 1 < 2048)
    (hacc : Clean acc → kCnt acc + 8192 < 16777216 →
      Clean acc' ∧ kCnt acc' ≤ kCnt acc + 8192 ∧ lab u acc' = lab u acc * l)
    (hb : (p ≠ ft ∧ el gen rep R = l) ∨ (p = ft ∧ el gen rep R = a ∧ l = b)) :
    WL u gen rep s W ft a b (p + 1) (sF R st) acc' := by
  rw [sF_eq]
  split_ifs with hm
  · rcases hI with hd | ⟨hcl, hcnt, cur, hcur, hst, hX1, hX2⟩
    · left
      have := fy_lt R
      omega
    · right
      rw [fxc_eq] at hm
      have hfx := fx_lt R
      have hfc := fc_lt R
      have h1 : cur = fx R := by omega
      have h2 : W / 256 ^ p % 256 = fc R := by omega
      have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
        rw [← div256_succ]
        omega
      obtain ⟨c1, c2, c3⟩ := hacc hcl (by omega)
      refine ⟨c1, by omega, fy R, fy_lt R, by rw [h3]; ring, WL_move u gen hX1 hX2 c3 ?_ hb⟩
      rw [wLet_eq, h2, h1]
      rfl
  · exact Or.inl rfl

theorem WL_sB {rep : ℕ → G} {s W ft p st acc acc' R : ℕ} {a b l : G}
    (hI : WL u gen rep s W ft a b p st acc) (hp : p + 1 < 2048)
    (hacc : Clean acc → kCnt acc + 8192 < 16777216 →
      Clean acc' ∧ kCnt acc' ≤ kCnt acc + 8192 ∧ lab u acc' = lab u acc * l)
    (hpf : p ≠ ft) (hR : (el gen rep R)⁻¹ = l) (hl : lv gen (fic R) = (lv gen (fc R))⁻¹) :
    WL u gen rep s W ft a b (p + 1) (sB R st) acc' := by
  rw [sB_eq]
  split_ifs with hm
  · rcases hI with hd | ⟨hcl, hcnt, cur, hcur, hst, hX1, hX2⟩
    · left
      have := fx_lt R
      omega
    · right
      rw [fyic_eq] at hm
      have hfy := fy_lt R
      have h1 : cur = fy R := by omega
      have h2 : W / 256 ^ p % 256 = fic R := by omega
      have h3 : st / 268435456 = W / 256 ^ (p + 1) := by
        rw [← div256_succ]
        omega
      obtain ⟨c1, c2, c3⟩ := hacc hcl (by omega)
      refine ⟨c1, by omega, fx R, fx_lt R, by rw [h3]; ring,
        WL_move u gen hX1 hX2 c3 ?_ (Or.inl ⟨hpf, hR⟩)⟩
      rw [wLet_eq, h2, h1, hl]
      unfold el
      group
  · exact Or.inl rfl

@[expose] def RefsL (blk LB : ℕ → ℕ) (rep : ℕ → G) (i : ℕ) : Prop :=
  ∀ h < i, el gen rep (fct blk h) = lab u (LB h) ∧
    lv gen (fic (fct blk h)) = (lv gen (fc (fct blk h)))⁻¹ ∧ labWF (LB h) = true

theorem WL_ref (hli : LIOk u li) {blk LB : ℕ → ℕ} {rep : ℕ → G} {s W ft p st acc i e : ℕ}
    {a b : G} (hI : WL u gen rep s W ft a b p st acc) (hp : p + 1 < 2048) (hpf : p ≠ ft)
    (hrefs : RefsL u gen blk LB rep i) :
    WL u gen rep s W ft a b (p + 1) (refStep blk i e st)
      (pushLab li (LB (Nat.shiftRight e 1)) (Nat.land e 1) acc) := by
  unfold refStep
  rw [brec_eq]
  split_ifs with hh
  · rw [Nat.blt_eq] at hh
    simp only [strictN_eq]
    obtain ⟨h1, h2, h3⟩ := hrefs _ hh
    have hpl := fun hcl hc => pushLab_spec u hli (dir := Nat.land e 1) (acc := acc) h3 hcl hc
    rw [brec_eq]
    split_ifs with hd
    · rw [Nat.beq_eq] at hd
      refine WL_sB u gen hI hp (l := (lab u (LB (Nat.shiftRight e 1)))⁻¹) (fun hcl hc => ?_) hpf
        (by rw [h1]) h2
      obtain ⟨c1, c2, c3⟩ := hpl hcl hc
      rw [ite_eq_left hd] at c3
      exact ⟨c1, c2, c3⟩
    · rw [Nat.beq_eq] at hd
      refine WL_sF u gen hI hp (l := lab u (LB (Nat.shiftRight e 1))) (fun hcl hc => ?_)
        (Or.inl ⟨hpf, h1⟩)
      obtain ⟨c1, c2, c3⟩ := hpl hcl hc
      rw [ite_eq_right hd] at c3
      exact ⟨c1, c2, c3⟩
  · exact Or.inl rfl

theorem walkGo_succ' (blk : ℕ → ℕ) (i Ri ft n k J st : ℕ) :
    walkGo blk i Ri ft n (k + 1) J st =
      if Nat.beq (Nat.sub n (Nat.succ k)) ft = true then walkGo blk i Ri ft n k J (sF Ri st)
      else walkGo blk i Ri ft n k (Nat.shiftRight J 32) (refStep blk i (Nat.land J 4294967295) st) :=
  brec_eq _ _ _

theorem labGo_succ' (LB : ℕ → ℕ) (Li ft n k J acc : ℕ) :
    labGo li LB Li ft n (k + 1) J acc =
      if Nat.beq (Nat.sub n (Nat.succ k)) ft = true then labGo li LB Li ft n k J (pushFwd li Li acc)
      else labGo li LB Li ft n k (Nat.shiftRight J 32)
        (pushLab li (LB (Nat.shiftRight (Nat.land J 4294967295) 1))
          (Nat.land (Nat.land J 4294967295) 1) acc) := by
  change Bool.rec (motive := fun _ => ℕ) ((fun e => strictN (pushLab li (LB (Nat.shiftRight e 1))
      (Nat.land e 1) acc) (labGo li LB Li ft n k (Nat.shiftRight J 32))) (Nat.land J 4294967295))
    (strictN (pushFwd li Li acc) (labGo li LB Li ft n k J)) (Nat.beq (Nat.sub n (Nat.succ k)) ft) = _
  rw [brec_eq]
  simp only [strictN_eq]

theorem cycWalk_succ (blk : ℕ → ℕ) (nf k R st : ℕ) :
    cycWalk blk nf (k + 1) R st =
      cycWalk blk nf k (Nat.shiftRight R 32) (refStep blk nf (Nat.land R 4294967295) st) :=
  strictN_eq _ _

theorem cycLab_succ (LB : ℕ → ℕ) (k R acc : ℕ) :
    cycLab li LB (k + 1) R acc = cycLab li LB k (Nat.shiftRight R 32)
      (pushLab li (LB (Nat.shiftRight (Nat.land R 4294967295) 1))
        (Nat.land (Nat.land R 4294967295) 1) acc) :=
  strictN_eq _ _

theorem walk_joint (hli : LIOk u li) {blk LB : ℕ → ℕ} {rep : ℕ → G} {s W ft i Ri Li n : ℕ}
    (hrefs : RefsL u gen blk LB rep i) (hn : n < 1024) (hLi : labWF Li = true) :
    ∀ k ≤ n, ∀ J st acc, WL u gen rep s W ft (el gen rep Ri) (lab u Li) (n - k) st acc →
      WL u gen rep s W ft (el gen rep Ri) (lab u Li) n (walkGo blk i Ri ft n k J st)
        (labGo li LB Li ft n k J acc)
  | 0, _, J, st, acc, hI => by
    change WL u gen rep s W ft (el gen rep Ri) (lab u Li) n st acc
    simpa using hI
  | k + 1, hk, J, st, acc, hI => by
    rw [walkGo_succ', labGo_succ']
    have e : n - k = n - (k + 1) + 1 := by omega
    split_ifs with hp
    · rw [Nat.beq_eq] at hp
      apply walk_joint hli hrefs hn hLi k (by omega)
      rw [e]
      obtain ⟨hn', -⟩ := labWF_spec hLi
      refine WL_sF u gen hI (by omega) (fun hcl hc => ?_) (Or.inr ⟨hp, rfl, rfl⟩)
      obtain ⟨c1, c2, c3⟩ := pushFwd_spec u hli (L := Li) (acc := acc) hcl (by omega)
      exact ⟨c1, by omega, c3⟩
    · rw [Nat.beq_eq] at hp
      apply walk_joint hli hrefs hn hLi k (by omega)
      rw [e]
      exact WL_ref u gen hli hI (by omega) hp hrefs

theorem cyc_joint (hli : LIOk u li) {blk LB : ℕ → ℕ} {rep : ℕ → G} {s W n nf : ℕ}
    (hrefs : RefsL u gen blk LB rep nf) (hn : n < 1024) :
    ∀ k ≤ n, ∀ R st acc, WL u gen rep s W n 1 1 (n - k) st acc →
      WL u gen rep s W n 1 1 n (cycWalk blk nf k R st) (cycLab li LB k R acc)
  | 0, _, R, st, acc, hI => by
    change WL u gen rep s W n 1 1 n st acc
    simpa using hI
  | k + 1, hk, R, st, acc, hI => by
    rw [cycWalk_succ, cycLab_succ]
    apply cyc_joint hli hrefs hn k (by omega)
    rw [show n - k = n - (k + 1) + 1 by omega]
    exact WL_ref u gen hli hI (by omega) (by omega) hrefs

theorem WL_start {rep : ℕ → G} {s W ft : ℕ} {a b : G} (hs : s < 1048576) :
    WL u gen rep s W ft a b 0 (wStart s W) 0 := by
  right
  refine ⟨clean_zero, by simp [kCnt_eq], s, hs, ?_, fun _ => ?_,
    fun h => absurd h (Nat.not_lt_zero _)⟩
  · unfold wStart
    rw [lor20 _ hs, pow_zero, Nat.div_one]
    ring
  · rw [bv_zero, mul_one, mul_inv_cancel, lab_zero]

theorem walk_fact (hli : LIOk u li) {blk LB : ℕ → ℕ} {rep : ℕ → G}
    {INV nC i R w fs ft J hh : ℕ}
    (h : walkOK blk INV nC i R w fs ft J = true)
    (hl : labGo li LB (LB i) ft (wLen w) (wLen w) (Nat.shiftRight J 53) 0 = target w hh)
    (hfs : fs < 1048576) (hrefs : RefsL u gen blk LB rep i) (hrep0 : rep 0 = 1)
    (hLi : labWF (LB i) = true)
    (h2 : wKind w = 2 → bv gen (wWord w) (wLen w) = 1)
    (h3 : wKind w = 3 → bv gen (wWord w) (wLen w) = lab u (target w hh)) :
    recOK INV nC R = true ∧ el gen rep R = lab u (LB i) := by
  unfold walkOK at h
  simp only [andB_iff, orB_iff, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at h
  obtain ⟨hrec, hft, hkind, hwalk⟩ := h
  refine ⟨hrec, ?_⟩
  have hn := wLen_lt w
  have h0 : WL u gen rep fs (wWord w) ft (el gen rep R) (lab u (LB i)) (wLen w - wLen w)
      (wStart fs (wWord w)) 0 := by
    rw [Nat.sub_self]
    exact WL_start u gen hfs
  have hW := walk_joint u gen hli (Ri := R) hrefs hn hLi (wLen w) le_rfl (Nat.shiftRight J 53) _ _ h0
  rw [hwalk, hl] at hW
  rcases hW with hd | ⟨-, -, cur, hcur, hst, -, hX2⟩
  · omega
  · have hc : cur = fs := by omega
    rw [hc] at hX2
    obtain ⟨A, B, e1, e2⟩ := hX2 hft
    have hT : rep fs * bv gen (wWord w) (wLen w) * (rep fs)⁻¹ = lab u (target w hh) := by
      rcases hkind with hk | ⟨hk, hfs0⟩
      · have hb : Nat.beq (wKind w) 3 = false := by
          cases hq : Nat.beq (wKind w) 3
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) (by omega)
        have ht : target w hh = 0 := by
          unfold target
          rw [hb]
        rw [h2 hk, ht, lab_zero, mul_one, mul_inv_cancel]
      · rw [hfs0, hrep0, h3 hk, one_mul, inv_one, mul_one]
    rw [hT, e2] at e1
    exact (mul_left_cancel (mul_right_cancel e1)).symm

@[expose] def LInv (blk LB : ℕ → ℕ) (INV nC i N : ℕ) : Prop :=
  (∀ h < i, recOK INV nC (fct blk h) = true) ∧ ∃ rep : ℕ → G, rep 0 = 1 ∧
    ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) → ∀ h < i, el gen rep' (fct blk h) = lab u (LB h)

@[expose] def Good (blk LB : ℕ → ℕ) (INV nC nf S X I : ℕ) : Prop :=
  S = 0 ∨ I = 0 ∨ X = 0 ∨ nf + 1 < X ∨
    (I = 1 ∧ ∃ i N, X = i + 1 ∧ i ≤ nf ∧ S = mkS i N ∧ 1 ≤ N ∧ LInv u gen blk LB INV nC i N)

theorem labStep_cases (LB : ℕ → ℕ) (Hs J X w : ℕ) :
    labStep li LB Hs J X w = 0 ∨ labStep li LB Hs J X w = X + 1 := by
  unfold labStep
  simp only [brec_eq]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem good_dead {blk LB : ℕ → ℕ} {INV nC nf S I X' : ℕ} (X : ℕ) (hX : nf + 1 ≤ X)
    (h : X' = 0 ∨ X' = X + 1) : Good u gen blk LB INV nC nf S X' I := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))

theorem walk_step (hli : LIOk u li) {blk WT LB : ℕ → ℕ} {INV INV8 L nC nf m Hs : ℕ}
    (hinv : invOK INV INV8 L = true) (hnf : nf < 4294967296)
    (hLB : ∀ h < nf, labWF (LB h) = true)
    (hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → bv gen (wWord (WT k)) (wLen (WT k)) = lab u (target (WT k) (hint Hs k))))
    {S X I J : ℕ} (hJ : Nat.land J 1 = 1) (hS : Good u gen blk LB INV nC nf S X I) :
    Good u gen blk LB INV nC nf
      (factStep blk INV nC L J S (fct blk (sI S)) (WT (Nat.land (Nat.shiftRight J 1) 65535)))
      (labStep li LB Hs J X (WT (Nat.land (Nat.shiftRight J 1) 65535)))
      (Bool.rec (motive := fun _ => ℕ) 0 I (Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m)) := by
  rcases hS with h0 | h0 | h0 | hd | ⟨hI1, i, N, hX, hi, hSd, hN, hrec, rep, hrep0, hfacts⟩
  · left
    rw [h0]
    rfl
  · right
    left
    rw [h0]
    cases Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m <;> rfl
  · right
    right
    left
    rw [h0]
    rfl
  · exact good_dead u gen X (by omega) (labStep_cases LB Hs J X _)
  have hi32 : i < 4294967296 := by omega
  rcases Nat.lt_or_ge i nf with hinf | hinf
  swap
  · exact good_dead u gen X (by omega) (labStep_cases LB Hs J X _)
  rcases Nat.lt_or_ge (Nat.land (Nat.shiftRight J 1) 65535) m with hidm | hidm
  swap
  · right
    left
    have : Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m = false := by
      cases hq : Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m
      · rfl
      · rw [Nat.blt_eq] at hq
        omega
    rw [this]
  have hI' : Bool.rec (motive := fun _ => ℕ) 0 I
      (Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m) = 1 := by
    have : Nat.blt (Nat.land (Nat.shiftRight J 1) 65535) m = true := by
      rw [Nat.blt_eq]
      exact hidm
    rw [this, hI1]
  rw [hI']
  have hsI : sI S = i := by
    rw [sI_eq, hSd, mkS_eq N hi32]
    omega
  have hsN : sN S = N := by
    rw [sN_eq, hSd, mkS_eq N hi32]
    omega
  have hS0 : Nat.blt 0 S = true := by
    rw [Nat.blt_eq, hSd, mkS_eq N hi32]
    omega
  have hX0 : Nat.blt 0 X = true := by
    rw [Nat.blt_eq]
    omega
  have hXi : Nat.sub X 1 = i := by
    change X - 1 = i
    omega
  have hJ' : Nat.beq (Nat.land J 1) 1 = true := by
    rw [Nat.beq_eq]
    exact hJ
  have hfS : factStep blk INV nC L J S (fct blk (sI S)) (WT (Nat.land (Nat.shiftRight J 1) 65535)) =
      Bool.rec (motive := fun _ => ℕ) 0 (mkS (Nat.succ i) N)
        (walkOK blk INV nC i (fct blk i) (WT (Nat.land (Nat.shiftRight J 1) 65535))
          (Nat.land (Nat.shiftRight J 17) 1048575) (Nat.land (Nat.shiftRight J 37) 65535) J) := by
    unfold factStep
    rw [hS0, hJ', hsI, hsN]
  have hlS : labStep li LB Hs J X (WT (Nat.land (Nat.shiftRight J 1) 65535)) =
      Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ X)
        (labWalk li LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
          (hint Hs (Nat.land (Nat.shiftRight J 1) 65535))) := by
    unfold labStep
    rw [hX0, hJ', hXi]
  rw [hfS, hlS]
  cases hw : walkOK blk INV nC i (fct blk i) (WT (Nat.land (Nat.shiftRight J 1) 65535))
      (Nat.land (Nat.shiftRight J 17) 1048575) (Nat.land (Nat.shiftRight J 37) 65535) J
  · exact Or.inl rfl
  cases hlw : labWalk li LB i J (WT (Nat.land (Nat.shiftRight J 1) 65535))
      (hint Hs (Nat.land (Nat.shiftRight J 1) 65535))
  · exact Or.inr (Or.inr (Or.inl rfl))
  have hl := Nat.eq_of_beq_eq_true hlw
  have hfs : Nat.land (Nat.shiftRight J 17) 1048575 < 1048576 := by
    rw [land20]
    omega
  obtain ⟨h2, h3⟩ := hWT _ hidm
  have hwf : ∀ rep' : ℕ → G, (∀ k < N, rep' k = rep k) →
      recOK INV nC (fct blk i) = true ∧ el gen rep' (fct blk i) = lab u (LB i) := by
    intro rep' hag
    refine walk_fact u gen hli hw hl hfs (fun h hh => ⟨hfacts rep' hag h hh,
      (lv_fic gen blk hinv (hrec h hh)).1, hLB h (by omega)⟩) ?_ (hLB i hinf) h2 h3
    rw [hag 0 (by omega), hrep0]
  change Good u gen blk LB INV nC nf (mkS (Nat.succ i) N) (Nat.succ X) 1
  right
  right
  right
  right
  refine ⟨rfl, i + 1, N, by omega, by omega, rfl, hN, fun h hh => ?_, rep, hrep0,
    fun rep' hag h hh => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrec h hh
    · exact (hwf rep (fun _ _ => rfl)).1
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hfacts rep' hag h hh
    · exact (hwf rep' hag).2

theorem tree_step {blk LB : ℕ → ℕ} {INV nC nf L Hs : ℕ} (hnf : nf < 4294967296)
    {S X I J : ℕ} (hJ : ¬Nat.land J 1 = 1) (hS : Good u gen blk LB INV nC nf S X I) :
    Good u gen blk LB INV nC nf (factStep blk INV nC L J S (fct blk (sI S)) 0)
      (labStep li LB Hs J X 0) I := by
  rcases hS with h0 | h0 | h0 | hd | ⟨hI1, i, N, hX, hi, hSd, hN, hrec, rep, hrep0, hfacts⟩
  · left
    rw [h0]
    rfl
  · exact Or.inr (Or.inl h0)
  · right
    right
    left
    rw [h0]
    rfl
  · exact good_dead u gen X (by omega) (labStep_cases LB Hs J X _)
  have hi32 : i < 4294967296 := by omega
  rcases Nat.lt_or_ge i nf with hinf | hinf
  swap
  · exact good_dead u gen X (by omega) (labStep_cases LB Hs J X _)
  have hsI : sI S = i := by
    rw [sI_eq, hSd, mkS_eq N hi32]
    omega
  have hsN : sN S = N := by
    rw [sN_eq, hSd, mkS_eq N hi32]
    omega
  have hS0 : Nat.blt 0 S = true := by
    rw [Nat.blt_eq, hSd, mkS_eq N hi32]
    omega
  have hX0 : Nat.blt 0 X = true := by
    rw [Nat.blt_eq]
    omega
  have hXi : Nat.sub X 1 = i := by
    change X - 1 = i
    omega
  have hJ' : Nat.beq (Nat.land J 1) 1 = false := by
    cases hq : Nat.beq (Nat.land J 1) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hq) hJ
  have hfS : factStep blk INV nC L J S (fct blk (sI S)) 0 =
      Bool.rec (motive := fun _ => ℕ) 0 (mkS (Nat.succ i) (Nat.succ N))
        (fTree INV nC L (fct blk i) N) := by
    unfold factStep
    rw [hS0, hJ', hsI, hsN]
  have hlS : labStep li LB Hs J X 0 =
      Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ X) (Nat.beq (LB i) 0) := by
    unfold labStep
    rw [hX0, hJ', hXi]
  rw [hfS, hlS]
  cases htree : fTree INV nC L (fct blk i) N
  · exact Or.inl rfl
  cases hlb : Nat.beq (LB i) 0
  · exact Or.inr (Or.inr (Or.inl rfl))
  have hLB0 := Nat.eq_of_beq_eq_true hlb
  unfold fTree at htree
  simp only [andB_iff, Nat.beq_eq, Nat.blt_eq] at htree
  obtain ⟨hrR, hfy, hfx, hfc⟩ := htree
  change Good u gen blk LB INV nC nf (mkS (Nat.succ i) (Nat.succ N)) (Nat.succ X) I
  right
  right
  right
  right
  refine ⟨hI1, i + 1, N + 1, by omega, by omega, rfl, by omega, fun h hh => ?_,
    Function.update rep N (rep (fx (fct blk i)) * lv gen (fc (fct blk i))), ?_,
    fun rep' hag h hh => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hrec h hh
    · exact hrR
  · rw [Function.update_of_ne (show (0 : ℕ) ≠ N by omega)]
    exact hrep0
  · have hag' : ∀ k < N, rep' k = rep k := by
      intro k hk
      rw [hag k (by omega), Function.update_of_ne (show k ≠ N by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh | rfl
    · exact hfacts rep' hag' h hh
    · unfold el
      rw [hfy, hag N (by omega), Function.update_self, hag' _ hfx, mul_inv_cancel, hLB0, lab_zero]

@[expose] noncomputable def labRec (li : ℕ → ℕ) (WT LB : ℕ → ℕ) (Hs : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStep li LB Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStep li LB Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

@[expose] noncomputable def idsRec (WT : ℕ → ℕ) (m : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (ih (Nat.shiftRight J (nat_lit 1)) S)
      (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) (fun id =>
        strictN (WT id) (fun w =>
          ih (Nat.shiftRight J (jLen J w))
            (Bool.rec (motive := fun _ => Nat) (nat_lit 0) S (Nat.blt id m)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1))) k

theorem chunk_all (hli : LIOk u li) {blk WT LB : ℕ → ℕ} {INV INV8 L nC nf m Hs : ℕ}
    (hinv : invOK INV INV8 L = true) (hnf : nf < 4294967296)
    (hLB : ∀ h < nf, labWF (LB h) = true)
    (hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → bv gen (wWord (WT k)) (wLen (WT k)) = lab u (target (WT k) (hint Hs k)))) :
    ∀ k J S X I, Good u gen blk LB INV nC nf S X I →
      Good u gen blk LB INV nC nf (chunkRec blk WT INV nC L k J S) (labRec li WT LB Hs k J X)
        (idsRec WT m k J I)
  | 0, _, _, _, _, h => h
  | k + 1, J, S, X, I, h => by
    change Good u gen blk LB INV nC nf
      (Bool.rec (motive := fun _ => Nat)
        (chunkRec blk WT INV nC L k (Nat.shiftRight J 1) (factStep blk INV nC L J S (fct blk (sI S)) 0))
        (strictN (strictN (Nat.land (Nat.shiftRight J 1) 65535) WT) (fun w =>
          chunkRec blk WT INV nC L k (Nat.shiftRight J (jLen J w))
            (factStep blk INV nC L J S (fct blk (sI S)) w)))
        (Nat.beq (Nat.land J 1) 1))
      (Bool.rec (motive := fun _ => Nat)
        (strictN (labStep li LB Hs J X 0) (labRec li WT LB Hs k (Nat.shiftRight J 1)))
        (strictN (strictN (Nat.land (Nat.shiftRight J 1) 65535) WT) (fun w =>
          strictN (labStep li LB Hs J X w) (labRec li WT LB Hs k (Nat.shiftRight J (jLen J w)))))
        (Nat.beq (Nat.land J 1) 1))
      (Bool.rec (motive := fun _ => Nat)
        (idsRec WT m k (Nat.shiftRight J 1) I)
        (strictN (Nat.land (Nat.shiftRight J 1) 65535) (fun id =>
          strictN (WT id) (fun w =>
            idsRec WT m k (Nat.shiftRight J (jLen J w))
              (Bool.rec (motive := fun _ => Nat) 0 I (Nat.blt id m)))))
        (Nat.beq (Nat.land J 1) 1))
    cases hJb : Nat.beq (Nat.land J 1) 1
    · simp only [strictN_eq]
      exact chunk_all hli hinv hnf hLB hWT k _ _ _ _
        (tree_step u gen hnf (Nat.ne_of_beq_eq_false hJb) h)
    · simp only [strictN_eq]
      exact chunk_all hli hinv hnf hLB hWT k _ _ _ _
        (walk_step u gen hli hinv hnf hLB hWT (Nat.eq_of_beq_eq_true hJb) h)

theorem runAll_good (hli : LIOk u li) {blk WT LB : ℕ → ℕ} {INV INV8 L nC nf m Hs : ℕ}
    (hinv : invOK INV INV8 L = true) (hnf : nf < 4294967296)
    (hLB : ∀ h < nf, labWF (LB h) = true)
    (hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → bv gen (wWord (WT k)) (wLen (WT k)) = lab u (target (WT k) (hint Hs k)))) :
    ∀ (Cs : List ℕ) S X I, Good u gen blk LB INV nC nf S X I →
      Good u gen blk LB INV nC nf (runFacts blk WT INV nC L Cs S) (runLab li WT LB Hs Cs X)
        (LceSR.runIds WT m Cs I)
  | [], _, _, _, h => h
  | C :: Cs, S, X, I, h => by
    change Good u gen blk LB INV nC nf (strictN (runChunk blk WT INV nC L C S)
      (runFacts blk WT INV nC L Cs)) (strictN (labChunk li WT LB Hs C X) (runLab li WT LB Hs Cs))
      (strictN (LceSR.idsChunk WT m C I) (LceSR.runIds WT m Cs))
    simp only [strictN_eq]
    exact runAll_good hli hinv hnf hLB hWT Cs _ _ _
      (chunk_all u gen hli hinv hnf hLB hWT (Nat.land C 255) (Nat.shiftRight C 8) S X I h)

end Walks

theorem allBelow_spec' {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true := by
  intro i him
  have h1 := (allRec2_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      andB ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64) hi).1 h (i / 64) (by omega)
  have h2 := (allRec2_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem hintsLt_spec {WT : ℕ → ℕ} {m K Hs : ℕ} (h : hintsLt WT m K Hs = true) :
    ∀ k < m, wKind (WT k) = 3 → hint Hs k < K := by
  intro k hk h3
  have h1 := (allRec_iff (fun k => Bool.rec (motive := fun _ => Bool) true (Nat.blt (hint Hs k) K)
    (Nat.beq (wKind (WT k)) 3)) m).1 h k hk
  have hb : Nat.beq (wKind (WT k)) 3 = true := by
    rw [Nat.beq_eq]
    exact h3
  have h2 : Nat.blt (hint Hs k) K = true := by
    rw [hb] at h1
    exact h1
  rwa [Nat.blt_eq] at h2

theorem subLet_le (h : ℕ) : subLet h ≤ 2 := by
  unfold subLet
  rw [brec_eq]
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

theorem lab_target3 {w hh : ℕ} (hk : wKind w = 3) : lab u (target w hh) = lv u (subLet hh) := by
  have hb : Nat.beq (wKind w) 3 = true := by
    rw [Nat.beq_eq]
    exact hk
  have e : target w hh = mkK 1 (Nat.succ (subLet hh)) := by
    unfold target
    rw [hb]
  have hs := subLet_le hh
  rw [e, lab_mkK u _ (by norm_num), labCS_succ, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt (by omega : Nat.succ (subLet hh) < 256)]
  simp [labCS, digs, gv]

theorem coneOk_gen (gen : ℕ → G) (hli : LIOk u li) {blk WT RT ST LB : ℕ → ℕ}
    {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : coneOk li blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs = true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bv gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST0 : bv gen (wWord (ST 0)) (wLen (ST 0)) = u 0)
    (hST1 : bv gen (wWord (ST 1)) (wLen (ST 1)) = u 1)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : cycOK li blk WT LB nf c wid R (entStk E) = true) :
    bv u (wWord E) (wLen E) = 1 := by
  unfold coneOk at h
  obtain ⟨hwords, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (andB_iff _ _).1 h
  obtain ⟨-, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hnf, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hS1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hX0, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hX1, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hhints, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hlabs, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hids, h⟩ := (andB_iff _ _).1 h
  obtain ⟨hrunF, hrunL⟩ := (andB_iff _ _).1 h
  have hnf' : nf < 4294967296 := blt_true hnf
  have hS0' : S0 = mkS 0 1 := Nat.eq_of_beq_eq_true hS0
  have hS1' : S1 = mkS nf nCa := Nat.eq_of_beq_eq_true hS1
  have hX0' : X0 = 1 := Nat.eq_of_beq_eq_true hX0
  have hX1' : X1 = nf + 1 := Nat.eq_of_beq_eq_true hX1
  have hids' := Nat.eq_of_beq_eq_true hids
  have hrunF' := Nat.eq_of_beq_eq_true hrunF
  have hrunL' := Nat.eq_of_beq_eq_true hrunL
  have hLB : ∀ i < nf, labWF (LB i) = true := allBelow_spec' hlabs (by
    change nf ≤ 64 * ((nf >>> 6) + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega)
  have hWT : ∀ k < m, (wKind (WT k) = 2 → bv gen (wWord (WT k)) (wLen (WT k)) = 1) ∧
      (wKind (WT k) = 3 → bv gen (wWord (WT k)) (wLen (WT k)) =
        lab u (target (WT k) (hint Hs k))) := by
    intro k hk
    have hw := hintLoop (fun j H => (fun w r => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true
          (wSub INV (wWord w) (wLen w) (wWord (ST r)) (wLen (ST r))) (Nat.beq (wKind w) (nat_lit 3)))
        (wRel INV INV8 (wWord w) (wLen w) (wWord (RT r)) (wLen (RT r)))
        (Nat.beq (wKind w) (nat_lit 2))) (WT j) (Nat.land H (nat_lit 65535)))
      m (nat_lit 16) m le_rfl Hs hwords k hk
    rw [Nat.sub_self, Nat.zero_add] at hw
    obtain ⟨hw2, hw3⟩ := word_check hw
    refine ⟨fun hk2 => wRel_sound gen hinv (hw2 hk2) (hRT _).1 (hRT _).2, fun hk3 => ?_⟩
    have er : Nat.land (Hs >>> (16 * k)) 65535 = hint Hs k := rfl
    rw [wSub_sound gen (hw3 hk3), er, lab_target3 u hk3]
    have hlt : hint Hs k < 2 := hintsLt_spec hhints k hk hk3
    have es0 : subLet 0 = 0 := by
      unfold subLet
      rfl
    have es1 : subLet 1 = 2 := by
      unfold subLet
      rfl
    rcases (by omega : hint Hs k = 0 ∨ hint Hs k = 1) with h0 | h1
    · rw [h0, es0, hST0]
      simp [lv]
    · rw [h1, es1, hST1]
      simp [lv]
  have hG0 : Good u gen blk LB INV nC nf S0 X0 1 := by
    right
    right
    right
    right
    exact ⟨rfl, 0, 1, hX0', Nat.zero_le _, hS0', le_rfl,
      fun h hh => absurd hh (Nat.not_lt_zero h), fun _ => 1, rfl,
      fun _ _ h hh => absurd hh (Nat.not_lt_zero h)⟩
  have hG1 := runAll_good u gen hli hinv hnf' hLB hWT Cs S0 X0 1 hG0
  rw [hrunF', hrunL', hids', hS1', hX1'] at hG1
  have hF : ∃ rep : ℕ → G, RefsL u gen blk LB rep nf := by
    rcases hG1 with h0 | h0 | h0 | hd | ⟨-, i, N, hX, -, -, -, hrec, rep, -, hfacts⟩
    · rw [mkS_eq nCa hnf'] at h0
      exact ⟨fun _ => 1, fun h hh => absurd hh (by omega)⟩
    · exact absurd h0 (by norm_num)
    · omega
    · omega
    · have hi' : i = nf := by omega
      subst hi'
      exact ⟨rep, fun h hh => ⟨hfacts rep (fun _ _ => rfl) h hh,
        (lv_fic gen blk hinv (hrec h hh)).1, hLB h hh⟩⟩
  obtain ⟨rep, hrefs⟩ := hF
  unfold cycOK at hc
  rw [letB_eq] at hc
  simp only [andB_iff, Nat.beq_eq, Nat.add_eq] at hc
  obtain ⟨hk2, hwalk, hred⟩ := hc
  have hn := wLen_lt (WT wid)
  have h1 : bv gen (wWord (WT wid)) (wLen (WT wid)) = 1 := (hWT wid hwid).1 hk2
  have hc1 : c < 1048576 := lt_of_lt_of_eq hc0 (by norm_num)
  have h0 : WL u gen rep c (wWord (WT wid)) (wLen (WT wid)) 1 1 (wLen (WT wid) - wLen (WT wid))
      (wStart c (wWord (WT wid))) 0 := by
    rw [Nat.sub_self]
    exact WL_start u gen hc1
  have hW := cyc_joint u gen hli hrefs hn (wLen (WT wid)) le_rfl R _ _ h0
  rw [hwalk] at hW
  rcases hW with hd | ⟨hcl, -, cur, hcur, hst, hY, -⟩
  · omega
  · have hcc : cur = c := by omega
    have hlab := hY le_rfl
    rw [hcc, h1, mul_one, mul_inv_cancel] at hlab
    obtain ⟨r1, r2⟩ := cycRed_spec u hli hcl hlab.symm
    rw [hred] at r1 r2
    rw [← entStk_spec u r1]
    exact r2

theorem coneOk_sound' (gen : ℕ → G) (hu : u 0 * u 0 = 1) {blk WT RT ST LB : ℕ → ℕ}
    {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : CFSG.Certificates.LS.He.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs =
      true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bv gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST0 : bv gen (wWord (ST 0)) (wLen (ST 0)) = u 0)
    (hST1 : bv gen (wWord (ST 1)) (wLen (ST 1)) = u 1)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : HeB.cycOK blk WT LB nf c wid R (HeB.entStk E) = true) :
    bv u (wWord E) (wLen E) = 1 :=
  coneOk_gen u gen (he_liOk u hu) ((he_coneOk ..).symm.trans h) hRT hST0 hST1 hc0 hwid
    ((he_cycOK ..).symm.trans hc)

theorem ruConeOk_sound' (gen : ℕ → G) (hu : u 1 * u 1 = 1) {blk WT RT ST LB : ℕ → ℕ}
    {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : CFSG.Certificates.LS.Ru.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs =
      true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bv gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST0 : bv gen (wWord (ST 0)) (wLen (ST 0)) = u 0)
    (hST1 : bv gen (wWord (ST 1)) (wLen (ST 1)) = u 1)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : RuB.cycOK blk WT LB nf c wid R (RuB.entStk E) = true) :
    bv u (wWord E) (wLen E) = 1 :=
  coneOk_gen u gen (ru_liOk u hu) ((ru_coneOk ..).symm.trans h) hRT hST0 hST1 hc0 hwid (by
    rw [← ru_entStk]
    exact (ru_cycOK ..).symm.trans hc)

end CFSG.Certificates.LceP.HeL

end
