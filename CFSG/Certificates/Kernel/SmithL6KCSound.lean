module

public import Certificates.Data.Kernel.SmithL6KC
public import CFSG.Certificates.Kernel.SmithL6KUSound
public import CFSG.Certificates.Kernel.SmithL6KRSound
public import CFSG.GF2Type.SmithTypeE.LMod.Tv
public import CFSG.GF2Type.SmithTypeE.LMod.Points

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel CFSG.SmithL6.CollK Matrix
open CFSG.GF2Type.SmithTypeE.LMod (dec6 dec6_apply dec6_xor dec6_zero dec6_inj bit_form)
open CFSG.LargeExtraspecial.SMod20 (bit bit_xor bit_and)

@[expose] def toM (A : List Nat) : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun i j => dec6 (A.getD j.val 0) i

theorem dec6_eq_bit (n : Nat) (i : Fin 6) : dec6 n i = bit (n.testBit i.val) := rfl

theorem bit_apK (l : List Nat) (x i : Nat) :
    bit ((apK l x).testBit i) =
      ∑ m ∈ Finset.range l.length, bit (x.testBit m) * bit ((l.getD m 0).testBit i) := by
  induction l generalizing x with
  | nil => simp [apK, bit]
  | cons c l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    have e : ∀ m ∈ Finset.range l.length, bit (x.testBit (m + 1)) *
        bit (((c :: l).getD (m + 1) 0).testBit i) =
        bit ((x / 2).testBit m) * bit ((l.getD m 0).testBit i) := fun m _ => by
      rw [Nat.testBit_succ, List.getD_cons_succ]
    rw [Finset.sum_congr rfl e, ← ih, List.getD_cons_zero, Nat.testBit_zero]
    have hk : apK (c :: l) x = if x % 2 = 1 then c ^^^ apK l (x / 2) else apK l (x / 2) := rfl
    rw [hk]
    by_cases h : x % 2 = 1
    · rw [if_pos h, Nat.testBit_xor, bit_xor, decide_eq_true h]
      simp only [bit, if_true, one_mul]
      exact add_comm _ _
    · rw [if_neg h, decide_eq_false h]
      simp [bit]

theorem dec6_apK {A : List Nat} (hA : A.length = 6) (x : Nat) :
    dec6 (apK A x) = toM A *ᵥ dec6 x := by
  funext i
  rw [dec6_eq_bit, bit_apK, hA, mulVec, dotProduct, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [toM, dec6_eq_bit, dec6_eq_bit, mul_comm]

theorem toM_mulM {A : List Nat} (hA : A.length = 6) (B : List Nat) :
    toM (mulM A B) = toM A * toM B := by
  ext i j
  have e : (B.map (apK A)).getD j.val 0 = apK A (B.getD j.val 0) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases B[j.val]? <;> simp [apK_zero]
  rw [toM, mulM, e, dec6_apK hA, mulVec, dotProduct, Matrix.mul_apply]
  rfl

theorem zipIdx_or_testBit (r i : Nat) : ∀ (l : List Nat) (k S : Nat),
    ((l.zipIdx k).foldl (fun acc p => if p.1.testBit r then acc ||| 2 ^ p.2 else acc) S).testBit i =
      (S.testBit i || (decide (k ≤ i) && (l.getD (i - k) 0).testBit r))
  | [], k, S => by simp
  | c :: l, k, S => by
    rw [List.zipIdx_cons, List.foldl_cons, zipIdx_or_testBit r i l (k + 1)]
    rcases Nat.lt_trichotomy i k with h | h | h
    · have h1 : decide (k ≤ i) = false := by simp; omega
      have h2 : decide (k + 1 ≤ i) = false := by simp; omega
      rw [h1, h2]
      split <;> simp [Nat.testBit_or, Nat.testBit_two_pow, show k ≠ i by omega]
    · subst h
      have h2 : decide (i + 1 ≤ i) = false := by simp
      rw [h2, Nat.sub_self, List.getD_cons_zero]
      split <;> simp_all [Nat.testBit_or, Nat.testBit_two_pow]
    · have h1 : decide (k ≤ i) = true := by simp; omega
      have h2 : decide (k + 1 ≤ i) = true := by simp; omega
      have h3 : i - k = (i - (k + 1)) + 1 := by omega
      rw [h1, h2, h3, List.getD_cons_succ]
      split <;> simp [Nat.testBit_or, Nat.testBit_two_pow, show k ≠ i by omega]

theorem toM_trM (A : List Nat) : toM (trM A) = (toM A)ᵀ := by
  ext i j
  rw [transpose_apply, toM, toM, trM, getD_of_lt (by simp), List.getElem_map, List.getElem_range,
    dec6_eq_bit, dec6_eq_bit, zipIdx_or_testBit]
  simp

theorem toM_idM : toM idM = 1 := by
  ext i j
  rw [Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> decide

theorem length_tvM (p : Nat) : (tvM p).length = 6 := by simp [tvM]

@[expose] noncomputable def tvMat (p : Nat) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  1 + vecMulVec (dec6 (p / 64)) (dec6 (p % 64))

theorem toM_tvM (p : Nat) : toM (tvM p) = tvMat p := by
  ext i j
  simp only [toM, tvM, tvMat, Matrix.add_apply, Matrix.one_apply, vecMulVec_apply]
  rw [getD_of_lt (by simp), List.getElem_map, List.getElem_range, dec6_eq_bit, dec6_eq_bit,
    dec6_eq_bit]
  have hne : i ≠ j → (j : Nat) ≠ i := fun hij e => hij (Fin.ext e.symm)
  split
  · rename_i h
    rw [Nat.testBit_xor, bit_xor, Nat.testBit_two_pow, h]
    by_cases hij : i = j
    · subst hij
      rcases Bool.eq_false_or_eq_true ((p / 64).testBit i) with hb | hb <;> simp [bit, hb]
    · rcases Bool.eq_false_or_eq_true ((p / 64).testBit i) with hb | hb <;>
        simp [bit, hb, hij, hne hij]
  · rename_i h
    simp only [Bool.not_eq_true] at h
    rw [Nat.testBit_two_pow, h]
    by_cases hij : i = j
    · subst hij
      simp [bit]
    · simp [bit, hij, hne hij]

theorem tvMat_mulVec (p : Nat) (x : Fin 6 → ZMod 2) :
    tvMat p *ᵥ x = x + (dec6 (p % 64) ⬝ᵥ x) • dec6 (p / 64) := by
  rw [tvMat, add_mulVec, one_mulVec]
  congr 1
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem tvMat_tr_mulVec (p : Nat) (x : Fin 6 → ZMod 2) :
    (tvMat p)ᵀ *ᵥ x = x + (dec6 (p / 64) ⬝ᵥ x) • dec6 (p % 64) := by
  rw [tvMat, transpose_add, transpose_one, add_mulVec, one_mulVec]
  congr 1
  funext i
  simp only [mulVec, dotProduct, transpose_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem add_self_mat (X : Matrix (Fin 6) (Fin 6) (ZMod 2)) : X + X = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize X i j = a
  revert a
  decide

theorem tvMat_mul_self {p : Nat} (hp : form (p % 64) (p / 64) = false) :
    tvMat p * tvMat p = 1 := by
  have h0 : dec6 (p % 64) ⬝ᵥ dec6 (p / 64) = 0 := by rw [← bit_form, hp]; rfl
  have hsq : vecMulVec (dec6 (p / 64)) (dec6 (p % 64)) * vecMulVec (dec6 (p / 64)) (dec6 (p % 64))
      = 0 := by
    ext i j
    simp only [mul_apply, vecMulVec_apply, Matrix.zero_apply]
    have e : ∑ k, dec6 (p / 64) i * dec6 (p % 64) k * (dec6 (p / 64) k * dec6 (p % 64) j) =
        dec6 (p / 64) i * dec6 (p % 64) j * (dec6 (p % 64) ⬝ᵥ dec6 (p / 64)) := by
      rw [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, h0, mul_zero]
  rw [tvMat, add_mul, mul_add, mul_add, mul_one, one_mul, mul_one, hsq, add_zero, add_assoc,
    add_self_mat, add_zero]

@[expose] def vP (c : Nat) : Fin 6 → ZMod 2 := dec6 (c / 64)

@[expose] def fP (c : Nat) : Fin 6 → ZMod 2 := dec6 (c % 64)

theorem dec6_ite (b : Bool) (x w : Nat) :
    dec6 (if b = true then x ^^^ w else x) = dec6 x + bit b • dec6 w := by
  cases b <;> simp [dec6_xor, bit]

theorem lt64_ite (b : Bool) {x w : Nat} (hx : x < 64) (hw : w < 64) :
    (if b = true then x ^^^ w else x) < 64 := by
  split
  · exact Nat.xor_lt_two_pow (n := 6) hx hw
  · exact hx

theorem conjF_parts (p q : Nat) :
    conjF p q / 64 = (if form (p % 64) (q / 64) then q / 64 ^^^ p / 64 else q / 64) ∧
    conjF p q % 64 = (if form (q % 64) (p / 64) then q % 64 ^^^ p % 64 else q % 64) := by
  have hB := lt64_ite (form (q % 64) (p / 64)) (Nat.mod_lt q (by decide)) (Nat.mod_lt p (by decide))
  rw [conjF_eq, conjC]
  omega

theorem vP_conjF (p q : Nat) : vP (conjF p q) = tvMat p *ᵥ vP q := by
  rw [vP, (conjF_parts p q).1, dec6_ite, bit_form, tvMat_mulVec]
  rfl

theorem fP_conjF (p q : Nat) : fP (conjF p q) = (tvMat p)ᵀ *ᵥ fP q := by
  rw [fP, (conjF_parts p q).2, dec6_ite, bit_form, tvMat_tr_mulVec, dotProduct_comm]
  rfl

theorem conjF_lt {p q : Nat} (hp : p < 4096) (hq : q < 4096) : conjF p q < 4096 := by
  have hA := lt64_ite (form (p % 64) (q / 64)) (show q / 64 < 64 by omega) (show p / 64 < 64 by omega)
  have hB := lt64_ite (form (q % 64) (p / 64)) (Nat.mod_lt q (by decide)) (Nat.mod_lt p (by decide))
  rw [conjF_eq, conjC]
  omega

@[expose] noncomputable def psiV : List Nat → Nat → Matrix (Fin 6) (Fin 6) (ZMod 2)
  | [], _ => 1
  | g :: G, a => if a.testBit 0 then tvMat g * psiV G (a / 2) else psiV G (a / 2)

@[expose] noncomputable def psiF : List Nat → Nat → Matrix (Fin 6) (Fin 6) (ZMod 2)
  | [], _ => 1
  | g :: G, a => if a.testBit 0 then (tvMat g)ᵀ * psiF G (a / 2) else psiF G (a / 2)

theorem uaWC_act (G : List Nat) : ∀ a c, vP (uaWC G a c) = psiV G a *ᵥ vP c ∧
    fP (uaWC G a c) = psiF G a *ᵥ fP c := by
  induction G with
  | nil => intro a c; simp [uaWC, psiV, psiF]
  | cons g G ih =>
    intro a c
    rw [uaWC_cons, psiV, psiF]
    cases a.testBit 0
    · exact ih (a / 2) c
    · simp only [cond_true, if_true]
      rw [vP_conjF, fP_conjF, (ih (a / 2) c).1, (ih (a / 2) c).2, mulVec_mulVec, mulVec_mulVec]
      exact ⟨rfl, rfl⟩

theorem uaWC_lt {G : List Nat} (hG : ∀ g ∈ G, g < 4096) : ∀ a {c}, c < 4096 → uaWC G a c < 4096 := by
  induction G with
  | nil => intro a c hc; exact hc
  | cons g G ih =>
    intro a c hc
    rw [uaWC_cons]
    have h := ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')) (a / 2) hc
    cases a.testBit 0
    · exact h
    · exact conjF_lt (hG g (List.mem_cons_self ..)) h

theorem psiF_psiV {G : List Nat} (hG : ∀ g ∈ G, form (g % 64) (g / 64) = false) :
    ∀ a, (psiF G a)ᵀ * psiV G a = 1 := by
  induction G with
  | nil => intro a; simp [psiV, psiF]
  | cons g G ih =>
    intro a
    have ih' := ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')) (a / 2)
    rw [psiV, psiF]
    split
    · rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (tvMat g),
        tvMat_mul_self (hG g (List.mem_cons_self ..)), Matrix.one_mul, ih']
    · exact ih'

theorem length_psiM (G : List Nat) : ∀ a, (psiM G a).length = 6 := by
  induction G with
  | nil => intro a; rfl
  | cons g G ih =>
    intro a
    show (bif a.testBit 0 then mulM (tvM g) (psiM G (a / 2)) else psiM G (a / 2)).length = 6
    cases a.testBit 0
    · exact ih _
    · simp [mulM, ih]

theorem toM_psiM (G : List Nat) : ∀ a, toM (psiM G a) = psiV G a := by
  induction G with
  | nil => intro a; exact toM_idM
  | cons g G ih =>
    intro a
    show toM (bif a.testBit 0 then mulM (tvM g) (psiM G (a / 2)) else psiM G (a / 2)) = _
    rw [psiV]
    cases a.testBit 0
    · exact ih _
    · simp only [cond_true, if_true]
      rw [toM_mulM (length_tvM g), toM_tvM, ih]

@[expose] noncomputable def liftV (L : List Nat) : Nat → Matrix (Fin 6) (Fin 6) (ZMod 2)
  | 0 => 1
  | 1 => tvMat (L.getD 0 0)
  | 2 => tvMat (L.getD 1 0)
  | 3 => tvMat (L.getD 0 0) * tvMat (L.getD 1 0)
  | _ => 1

@[expose] noncomputable def liftF (L : List Nat) : Nat → Matrix (Fin 6) (Fin 6) (ZMod 2)
  | 0 => 1
  | 1 => (tvMat (L.getD 0 0))ᵀ
  | 2 => (tvMat (L.getD 1 0))ᵀ
  | 3 => (tvMat (L.getD 0 0))ᵀ * (tvMat (L.getD 1 0))ᵀ
  | _ => 1

theorem liftC_act (L : List Nat) {j : Nat} (hj : j < 4) (c : Nat) :
    vP (liftC L j c) = liftV L j *ᵥ vP c ∧ fP (liftC L j c) = liftF L j *ᵥ fP c := by
  match j, hj with
  | 0, _ => simp [liftC, liftV, liftF]
  | 1, _ => exact ⟨vP_conjF _ _, fP_conjF _ _⟩
  | 2, _ => exact ⟨vP_conjF _ _, fP_conjF _ _⟩
  | 3, _ =>
    refine ⟨?_, ?_⟩
    · show vP (conjF _ (conjF _ c)) = _
      rw [vP_conjF, vP_conjF, liftV, mulVec_mulVec]
    · show fP (conjF _ (conjF _ c)) = _
      rw [fP_conjF, fP_conjF, liftF, mulVec_mulVec]

theorem toM_liftM (L : List Nat) {j : Nat} (hj : j < 4) : toM (liftM L j) = liftV L j := by
  match j, hj with
  | 0, _ => exact toM_idM
  | 1, _ => exact toM_tvM _
  | 2, _ => exact toM_tvM _
  | 3, _ => show toM (mulM _ _) = _; rw [toM_mulM (length_tvM _), toM_tvM, toM_tvM]; rfl

theorem length_candM (U L : List Nat) (j a : Nat) : (candM U L j a).length = 6 := by
  rw [candM, mulM, List.length_map]
  match j with
  | 0 => rfl
  | 1 => exact length_tvM _
  | 2 => exact length_tvM _
  | 3 => simp [liftM, mulM, length_tvM]
  | _ + 4 => rfl

theorem liftF_liftV {L : List Nat} (hL : ∀ i, form (L.getD i 0 % 64) (L.getD i 0 / 64) = false)
    {j : Nat} (hj : j < 4) : (liftF L j)ᵀ * liftV L j = 1 := by
  match j, hj with
  | 0, _ => simp [liftF, liftV]
  | 1, _ => rw [liftF, liftV, transpose_transpose, tvMat_mul_self (hL 0)]
  | 2, _ => rw [liftF, liftV, transpose_transpose, tvMat_mul_self (hL 1)]
  | 3, _ =>
    rw [liftF, liftV, transpose_mul, transpose_transpose, transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (tvMat (L.getD 0 0)), tvMat_mul_self (hL 0), Matrix.one_mul,
      tvMat_mul_self (hL 1)]

theorem trSw_apK : ∀ x < 64, apK swM x = trSw x ∧ trSw x < 64 := by decide +kernel

theorem dec6_trSw {x : Nat} (hx : x < 64) : dec6 (trSw x) = toM swM *ᵥ dec6 x := by
  rw [← (trSw_apK x hx).1, dec6_apK rfl]

theorem toM_swM_mul_self : toM swM * toM swM = 1 := by
  rw [← toM_mulM rfl, show mulM swM swM = idM by decide, toM_idM]

theorem toM_swM_tr : (toM swM)ᵀ = toM swM := by
  rw [← toM_trM, show trM swM = swM by decide]

theorem liftC4_act (L : List Nat) {c : Nat} (hc : c < 4096) :
    vP (liftC L 4 c) = toM swM *ᵥ fP c ∧ fP (liftC L 4 c) = toM swM *ᵥ vP c := by
  have h1 := trSw_apK (c % 64) (Nat.mod_lt c (by decide))
  have h2 := trSw_apK (c / 64) (by omega)
  have e1 : liftC L 4 c / 64 = trSw (c % 64) := by show (64 * _ + _) / 64 = _; omega
  have e2 : liftC L 4 c % 64 = trSw (c / 64) := by show (64 * _ + _) % 64 = _; omega
  rw [vP, fP, vP, fP, e1, e2, dec6_trSw (Nat.mod_lt c (by decide)), dec6_trSw (by omega)]
  exact ⟨rfl, rfl⟩

theorem liftC_lt {L : List Nat} (hL : ∀ i, L.getD i 0 < 4096) {j c : Nat} (hc : c < 4096) :
    liftC L j c < 4096 := by
  match j with
  | 0 => exact hc
  | 1 => exact conjF_lt (hL 0) hc
  | 2 => exact conjF_lt (hL 1) hc
  | 3 => exact conjF_lt (hL 0) (conjF_lt (hL 1) hc)
  | _ + 4 =>
    have h1 := (trSw_apK (c % 64) (Nat.mod_lt c (by decide))).2
    have h2 := (trSw_apK (c / 64) (by omega)).2
    show 64 * _ + _ < 4096
    omega

theorem candC_act {U L : List Nat} (hU : ∀ g ∈ U, form (g % 64) (g / 64) = false)
    (hL : ∀ i, form (L.getD i 0 % 64) (L.getD i 0 / 64) = false) {j : Nat} (hj : j < 5)
    (a : Nat) : ∃ N, Nᵀ * toM (candM U L j a) = 1 ∧ ∀ c < 4096,
      (j < 4 → vP (candC U L j a c) = toM (candM U L j a) *ᵥ vP c ∧
        fP (candC U L j a c) = N *ᵥ fP c) ∧
      (j = 4 → vP (candC U L j a c) = toM (candM U L j a) *ᵥ (toM swM *ᵥ fP c) ∧
        fP (candC U L j a c) = N *ᵥ (toM swM *ᵥ vP c)) := by
  by_cases h4 : j < 4
  · refine ⟨psiF U a * liftF L j, ?_, fun c _ => ⟨fun _ => ?_, fun h => absurd h (by omega)⟩⟩
    · rw [candM, toM_mulM (length_psiM U a), toM_psiM, toM_liftM L h4, transpose_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc (psiF U a)ᵀ, psiF_psiV hU, Matrix.one_mul,
        liftF_liftV hL h4]
    · rw [candC, (uaWC_act U a _).1, (uaWC_act U a _).2, (liftC_act L h4 c).1, (liftC_act L h4 c).2,
        mulVec_mulVec, mulVec_mulVec, candM, toM_mulM (length_psiM U a), toM_psiM, toM_liftM L h4]
      exact ⟨rfl, rfl⟩
  · have hj4 : j = 4 := by omega
    subst hj4
    refine ⟨psiF U a, ?_, fun c hc => ⟨fun h => absurd h (by omega), fun _ => ?_⟩⟩
    · rw [candM, toM_mulM (length_psiM U a), toM_psiM, show liftM L 4 = idM from rfl, toM_idM,
        Matrix.mul_one, psiF_psiV hU]
    · rw [candC, (uaWC_act U a _).1, (uaWC_act U a _).2, (liftC4_act L hc).1, (liftC4_act L hc).2,
        candM, toM_mulM (length_psiM U a), toM_psiM, show liftM L 4 = idM from rfl, toM_idM,
        Matrix.mul_one]
      exact ⟨rfl, rfl⟩

theorem candC_lt {U L : List Nat} (hU : ∀ g ∈ U, g < 4096) (hL : ∀ i, L.getD i 0 < 4096)
    (j a : Nat) {c : Nat} (hc : c < 4096) : candC U L j a c < 4096 :=
  uaWC_lt hU a (liftC_lt hL hc)

section Codes

variable {T : List Nat} (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k))
include hT

theorem liftC_code {j : Nat} (hj : j < 5) {x : Nat} (hx : x < 1953) :
    liftC [T.getD 0 0, T.getD 224 0] j (codeOf (tvPair x)) = codeOf (tvPair (trLift j)[x]!) ∧
      (trLift j)[x]! < 1953 := by
  have h0 : T.getD 0 0 = codeOf (tvPair 0) := hT 0 (by decide)
  have h224 : T.getD 224 0 = codeOf (tvPair 224) := hT 224 (by decide)
  match j, hj with
  | 0, _ =>
    change codeOf (tvPair x) = codeOf (tvPair trIdT[x]!) ∧ trIdT[x]! < 1953
    rw [trIdT, ofFn_get! _ hx]
    exact ⟨rfl, hx⟩
  | 1, _ =>
    change conjF (T.getD 0 0) _ = codeOf (tvPair (tvTab[0]!)[x]!) ∧ (tvTab[0]!)[x]! < 1953
    rw [h0, conjF_code (by decide) hx, tvTab_get (by decide) hx]
    exact ⟨rfl, tvImg_lt (by decide) hx⟩
  | 2, _ =>
    change conjF (T.getD 224 0) _ = codeOf (tvPair (tvTab[224]!)[x]!) ∧ (tvTab[224]!)[x]! < 1953
    rw [h224, conjF_code (by decide) hx, tvTab_get (by decide) hx]
    exact ⟨rfl, tvImg_lt (by decide) hx⟩
  | 3, _ =>
    change conjF (T.getD 0 0) (conjF (T.getD 224 0) _) =
      codeOf (tvPair (trCompT (trTvT 0) (trTvT 224))[x]!) ∧ (trCompT (trTvT 0) (trTvT 224))[x]! < 1953
    have h1 := tvImg_lt (j := 224) (by decide) hx
    rw [trCompT, ofFn_get! _ hx, h0, h224, conjF_code (by decide) hx, conjF_code (by decide) h1]
    simp only [trTvT]
    rw [tvTab_get (by decide) hx, tvTab_get (by decide) h1]
    exact ⟨rfl, tvImg_lt (by decide) h1⟩
  | 4, _ =>
    have hp := tvP_tvPair hx
    obtain ⟨h1, h2⟩ := trTauT_spec hx
    change 64 * trSw (codeOf (tvPair x) % 64) + trSw (codeOf (tvPair x) / 64) =
      codeOf (tvPair trTauT[x]!) ∧ trTauT[x]! < 1953
    rw [codeOf_div hp, codeOf_mod hp, h2]
    exact ⟨rfl, h1⟩

theorem candC_code {j : Nat} (hj : j < 5) (a : Nat) {x : Nat} (hx : x < 1953) :
    candC (ugC T) [T.getD 0 0, T.getD 224 0] j a (codeOf (tvPair x)) =
      codeOf (tvPair (trCandT (trLift j) a)[x]!) ∧ (trCandT (trLift j) a)[x]! < 1953 := by
  obtain ⟨e, hlt⟩ := liftC_code hT hj hx
  rw [candC, e, trCandT, ofFn_get! _ hx]
  exact uaWC_code hT a hlt

theorem ugC_tv : ∀ g ∈ ugC T, g < 4096 ∧ form (g % 64) (g / 64) = false := by
  intro g hg
  unfold ugC at hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hg
  have hall : ∀ u ∈ ugens.toList, u < 1953 := by decide
  have hlt := hall u hu
  have hp := tvP_tvPair hlt
  rw [hT _ hlt, codeOf_div hp, codeOf_mod hp]
  exact ⟨codeOf_lt hp, hp.2.2.2.2⟩

theorem cxL_tv : ∀ i, [T.getD 0 0, T.getD 224 0].getD i 0 < 4096 ∧
    form ([T.getD 0 0, T.getD 224 0].getD i 0 % 64) ([T.getD 0 0, T.getD 224 0].getD i 0 / 64)
      = false := by
  have key : ∀ k < 1953, T.getD k 0 < 4096 ∧ form (T.getD k 0 % 64) (T.getD k 0 / 64) = false :=
    fun k hk => by
      have hp := tvP_tvPair hk
      rw [hT k hk, codeOf_div hp, codeOf_mod hp]
      exact ⟨codeOf_lt hp, hp.2.2.2.2⟩
  intro i
  match i with
  | 0 => exact key 0 (by decide)
  | 1 => exact key 224 (by decide)
  | n + 2 =>
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_nil]
    exact ⟨by decide, by decide⟩

end Codes

theorem left_inv_unique {X Y Z : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hX : X * Z = 1) (hY : Y * Z = 1) :
    X = Y := by
  have hZ : Z * Y = 1 := mul_eq_one_comm.1 hY
  calc X = X * (Z * Y) := by rw [hZ, Matrix.mul_one]
    _ = Y := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

theorem length_take6 {e : List Nat} (he : e.length = 13) (s : Nat) (hs : s ≤ 7) :
    ((e.drop s).take 6).length = 6 := by
  simp only [List.length_take, List.length_drop, he]
  omega

theorem repsC_fst : ∀ k < 5, (k < 3 → (repsC.getD k (0, 0)).1 < 4) ∧
    (3 ≤ k → (repsC.getD k (0, 0)).1 = 4) := by decide

theorem recOK_conj {U L : List Nat} (hU : ∀ g ∈ U, form (g % 64) (g / 64) = false)
    (hL : ∀ i, form (L.getD i 0 % 64) (L.getD i 0 / 64) = false) {RM : List (List Nat)}
    (hRM : RM = repsC.map fun r => candM U L r.1 r.2) {j a : Nat} (hj : j < 5) {e : List Nat}
    (h : recOK RM j (candM U L j a) e = true) :
    e.headD 0 < 5 ∧ (toM ((e.drop 7).take 6))ᵀ * toM ((e.drop 1).take 6) = 1 ∧
      ∀ c < 4096, ∀ c' < 4096, vP c' = toM ((e.drop 1).take 6) *ᵥ vP c →
        fP c' = toM ((e.drop 7).take 6) *ᵥ fP c →
        vP (candC U L (repsC.getD (e.headD 0) (0, 0)).1 (repsC.getD (e.headD 0) (0, 0)).2 c') =
            toM ((e.drop 1).take 6) *ᵥ vP (candC U L j a c) ∧
          fP (candC U L (repsC.getD (e.headD 0) (0, 0)).1 (repsC.getD (e.headD 0) (0, 0)).2 c') =
            toM ((e.drop 7).take 6) *ᵥ fP (candC U L j a c) := by
  unfold recOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hk⟩, hHG⟩, hcase⟩ := h
  set k := e.headD 0
  set G := (e.drop 1).take 6
  set H := (e.drop 7).take 6
  have hG6 : G.length = 6 := length_take6 hlen 1 (by omega)
  have hH6 : H.length = 6 := length_take6 hlen 7 (by omega)
  have hHG' : (toM H)ᵀ * toM G = 1 := by
    rw [← toM_trM, ← toM_mulM (by simp [trM]), hHG, toM_idM]
  have hGH : (toM G)ᵀ * toM H = 1 := by
    have := congrArg transpose hHG'
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have hR : RM.getD k [] = candM U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2 := by
    subst hRM
    interval_cases hk' : k <;> rfl
  obtain ⟨N, hN, hact⟩ := candC_act hU hL hj a
  obtain ⟨NR, hNR, hactR⟩ := candC_act hU hL (j := (repsC.getD k (0, 0)).1)
    (by have := repsC_fst k hk; by_cases h3 : k < 3 <;> omega) (repsC.getD k (0, 0)).2
  generalize hRg : toM (candM U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2) = R
    at hNR hactR
  refine ⟨hk, hHG', fun c hc c' hc' hv hf => ?_⟩
  split at hcase
  · rename_i hj4
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcase
    obtain ⟨hk3, hGM⟩ := hcase
    have hr4 := (repsC_fst k hk).1 hk3
    have hGM' : toM G * toM (candM U L j a) = toM (RM.getD k []) * toM G := by
      rw [← toM_mulM hG6, ← toM_mulM (by rw [hR]; exact length_candM ..), hGM]
    rw [hR, hRg] at hGM'
    obtain ⟨hv1, hf1⟩ := (hact c hc).1 hj4
    obtain ⟨hv2, hf2⟩ := (hactR c' hc').1 hr4
    refine ⟨by rw [hv2, hv, hv1, mulVec_mulVec, mulVec_mulVec, hGM'], ?_⟩
    rw [hf2, hf, hf1, mulVec_mulVec, mulVec_mulVec]
    congr 1
    have e1 : ((toM H)ᵀ * NRᵀ) * (R * toM G) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc NRᵀ, hNR, Matrix.one_mul, hHG']
    have e2 : (Nᵀ * (toM H)ᵀ) * (R * toM G) = 1 := by
      rw [← hGM', Matrix.mul_assoc, ← Matrix.mul_assoc (toM H)ᵀ, hHG', Matrix.one_mul, hN]
    have := congrArg transpose (left_inv_unique e1 e2)
    simp only [transpose_mul, transpose_transpose] at this
    exact this
  · rename_i hj4
    have hj4' : j = 4 := by omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcase
    obtain ⟨hk3, hGM⟩ := hcase
    have hr4 := (repsC_fst k hk).2 hk3
    have hGM' : toM G * (toM (candM U L j a) * toM swM) =
        (toM (RM.getD k []) * toM swM) * toM H := by
      rw [← toM_mulM (length_candM ..),
        ← toM_mulM hG6, ← toM_mulM (by rw [hR]; exact length_candM ..),
        ← toM_mulM (by simp [mulM, swM]), hGM]
    rw [hR, hRg] at hGM'
    obtain ⟨hv1, hf1⟩ := (hact c hc).2 hj4'
    obtain ⟨hv2, hf2⟩ := (hactR c' hc').2 hr4
    refine ⟨?_, ?_⟩
    · rw [hv2, hf, hv1, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, ← hGM',
        Matrix.mul_assoc]
    · rw [hf2, hv, hf1, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
      congr 1
      have hJ := toM_swM_mul_self
      have e1 : ((toM G)ᵀ * toM swM * NRᵀ) * (R * toM swM * toM H) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc NRᵀ, ← Matrix.mul_assoc NRᵀ, hNR, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.mul_assoc (toM swM), hJ, Matrix.one_mul, hGH]
      have e2 : (toM swM * Nᵀ * (toM H)ᵀ) * (R * toM swM * toM H) = 1 := by
        rw [← hGM', Matrix.mul_assoc,
          ← Matrix.mul_assoc (toM H)ᵀ, hHG', Matrix.one_mul, ← Matrix.mul_assoc,
          Matrix.mul_assoc (toM swM), hN, Matrix.mul_one, hJ]
      have := congrArg transpose (left_inv_unique e1 e2)
      simp only [transpose_mul, transpose_transpose, toM_swM_tr, Matrix.mul_assoc] at this
      simp only [Matrix.mul_assoc]
      exact this

theorem scanC_sound {T : List Nat} {C : Nat} {U L : List Nat} {RM : List (List Nat)} {j : Nat} :
    ∀ (S : List (List Nat)) (a : Nat), scanC T C U L RM j S a = true →
      ∀ b, a ≤ b → b < 512 → entryOK T C U L RM j b (S.getD (b - a) []) = true := by
  intro S
  induction S with
  | nil =>
    intro a h b hab hb
    have h' : (a == 512) = true := h
    rw [beq_iff_eq] at h'
    omega
  | cons e S ih =>
    intro a h b hab hb
    have h' : (entryOK T C U L RM j a e && scanC T C U L RM j S (a + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · rw [Nat.sub_self, List.getD_cons_zero]
      exact h'.1
    · have e1 : b - a = (b - (a + 1)) + 1 := by omega
      rw [e1, List.getD_cons_succ]
      exact ih (a + 1) h'.2 b hlt hb

theorem entryOK_cases {T : List Nat} {C : Nat} {U L : List Nat} {RM : List (List Nat)}
    {j a : Nat} {e : List Nat} (h : entryOK T C U L RM j a e = true) :
    (∀ c ∈ T, candC U L j a c = c) ∨
      (∃ x < 1953, candC U L j a (candC U L j a (fldW 12 C x)) ≠ fldW 12 C x) ∨
      recOK RM j (candM U L j a) e = true := by
  match e with
  | [] =>
    left
    intro c hc
    exact beq_iff_eq.1 (List.all_eq_true.1 h c hc)
  | [x] =>
    right; left
    have h' : (decide (x < 1953) && candC U L j a (candC U L j a (fldW 12 C x)) != fldW 12 C x) =
      true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h'
    exact ⟨x, h'⟩
  | x :: y :: e =>
    right; right
    exact h

theorem cand_cases {T : List Nat} {C : Nat} (hl : T.length = 1953)
    (hT : ∀ k < 1953, T.getD k 0 = codeOf (tvPair k)) (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
    {RM : List (List Nat)}
    (hRM : RM = repsC.map fun r => candM (ugC T) [T.getD 0 0, T.getD 224 0] r.1 r.2) {j : Nat}
    (hj : j < 5) {S : List (List Nat)}
    (hS : scanC T C (ugC T) [T.getD 0 0, T.getD 224 0] RM j S 0 = true) {a : Nat} (ha : a < 512) :
    (∀ x < 1953, (trCandT (trLift j) a)[x]! = x) ∨
      (∃ x < 1953, (trCandT (trLift j) a)[(trCandT (trLift j) a)[x]!]! ≠ x) ∨
      ∃ k < 5, ∃ G H : Matrix (Fin 6) (Fin 6) (ZMod 2), Hᵀ * G = 1 ∧
        ∀ x < 1953, ∀ y < 1953, vP (codeOf (tvPair y)) = G *ᵥ vP (codeOf (tvPair x)) →
          fP (codeOf (tvPair y)) = H *ᵥ fP (codeOf (tvPair x)) →
          vP (codeOf (tvPair (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[y]!))
              = G *ᵥ vP (codeOf (tvPair (trCandT (trLift j) a)[x]!)) ∧
            fP (codeOf (tvPair (trCandT (trLift (repsC.getD k (0, 0)).1) (repsC.getD k (0, 0)).2)[y]!))
              = H *ᵥ fP (codeOf (tvPair (trCandT (trLift j) a)[x]!)) := by
  have hU := ugC_tv hT
  have hLt := cxL_tv hT
  have hE := scanC_sound S 0 hS a (Nat.zero_le a) ha
  rw [Nat.sub_zero] at hE
  rcases entryOK_cases hE with h | h | h
  · left
    intro x hx
    obtain ⟨e, hlt⟩ := candC_code hT hj a hx
    have h1 := h _ (code_mem hl hT hx)
    rw [e] at h1
    exact codeOf_tvPair_inj hlt hx h1
  · right; left
    obtain ⟨x, hx, hne⟩ := h
    refine ⟨x, hx, fun he => hne ?_⟩
    obtain ⟨e1, hlt1⟩ := candC_code hT hj a hx
    obtain ⟨e2, _⟩ := candC_code hT hj a hlt1
    rw [hC x hx, e1, e2, he]
  · right; right
    obtain ⟨hk, hHG, hconj⟩ := recOK_conj (fun g hg => (hU g hg).2) (fun i => (hLt i).2) hRM hj h
    refine ⟨_, hk, _, _, hHG, fun x hx y hy hv hf => ?_⟩
    have hr : (repsC.getD ((S.getD a []).headD 0) (0, 0)).1 < 5 := by
      have := repsC_fst _ hk
      by_cases h3 : (S.getD a []).headD 0 < 3 <;> omega
    obtain ⟨e1, _⟩ := candC_code hT hj a hx
    obtain ⟨e2, _⟩ := candC_code hT hr (repsC.getD ((S.getD a []).headD 0) (0, 0)).2 hy
    have hc := hconj _ (codeOf_lt (tvP_tvPair hx)) _ (codeOf_lt (tvP_tvPair hy)) hv hf
    rw [e1, e2] at hc
    exact hc

theorem mem_bitsM {m x : Nat} : x ∈ bitsM m ↔ x < 64 ∧ x ≠ 0 ∧ m.testBit x = true := by
  simp [bitsM, and_assoc]

theorem planeK_sound {f : Nat → Nat} {M A i i' : Nat} (h : planeK f M A i i' = true) :
    i < 1395 ∧ i' < 1395 ∧ ∀ v < 64, ∀ φ < 64, v ≠ 0 → φ ≠ 0 → (fldW 64 M i).testBit v = true →
      (fldW 64 A i).testBit φ = true → (fldW 64 M i').testBit (f (64 * v + φ) / 64) = true ∧
        (fldW 64 A i').testBit (f (64 * v + φ) % 64) = true := by
  unfold planeK planeMapC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hi, hi'⟩, h⟩ := h
  exact ⟨hi, hi', fun v hv φ hφ hv0 hφ0 hvm hφm =>
    h v (mem_bitsM.2 ⟨hv, hv0, hvm⟩) φ (mem_bitsM.2 ⟨hφ, hφ0, hφm⟩)⟩

theorem fixPlaneC_sound {f : Nat → Nat} {m n : Nat} (h : fixPlaneC f m n = true) :
    ∀ v < 64, ∀ φ < 64, v ≠ 0 → φ ≠ 0 → m.testBit v = true → n.testBit φ = true →
      f (64 * v + φ) = 64 * v + φ := by
  intro v hv φ hφ hv0 hφ0 hvm hφn
  unfold fixPlaneC at h
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact h v (mem_bitsM.2 ⟨hv, hv0, hvm⟩) φ (mem_bitsM.2 ⟨hφ, hφ0, hφn⟩)

theorem indep6_sound {vs : List Nat} (h : indep6 vs = true) :
    vs.length = 6 ∧ ∀ m, 0 < m → m < 64 → trXorSel vs m ≠ 0 := by
  unfold indep6 at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, bne_iff_ne] at h
  refine ⟨h.1, fun m hm0 hm => ?_⟩
  have := h.2 (m - 1) (by omega)
  rwa [Nat.sub_add_cancel hm0] at this

theorem mem_pairsOf : ∀ {l : List Nat} {p : Nat × Nat}, p ∈ pairsOf l →
    ∃ s, 2 * s + 1 < l.length ∧ l.getD (2 * s) 0 = p.1 ∧ l.getD (2 * s + 1) 0 = p.2
  | i :: i' :: l, p, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl, rfl⟩
    · obtain ⟨s, hs, h1, h2⟩ := mem_pairsOf h
      refine ⟨s + 1, by simp; omega, ?_, ?_⟩
      · rw [show 2 * (s + 1) = 2 * s + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
        exact h1
      · rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 1 + 1 by omega, List.getD_cons_succ,
          List.getD_cons_succ]
        exact h2
  | [], _, h => by simp [pairsOf] at h
  | [_], _, h => by simp [pairsOf] at h

theorem repOK_sound {U L : List Nat} {W M A k : Nat} {e : List Nat}
    (h : repOK U L W M A k e = true) :
    e.length = 15 ∧
      (∀ p ∈ pairsOf (e.drop 3),
        planeK (candC U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2) M A p.1 p.2 = true) ∧
      indep6 (dVecK W (pairsOf (e.drop 3))) = true ∧
      ((planeK (candC U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2) M A (e.getD 1 0)
          (e.getD 2 0) = true ∧ fB (fldW 20 W (e.getD 2 0)) (fldW 20 W (e.getD 1 0)) = true) ∨
        (e.getD 1 0 < 1395 ∧
          fixPlaneC (candC U L (repsC.getD k (0, 0)).1 (repsC.getD k (0, 0)).2)
            (fldW 64 M (e.getD 1 0)) (fldW 64 A (e.getD 1 0)) = true) ∨
        k = 3) := by
  unfold repOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hpl⟩, hind⟩, hbr⟩ := h
  refine ⟨hlen, hpl, hind, ?_⟩
  rcases hbr with (⟨⟨_, h1⟩, h2⟩ | ⟨⟨_, h1⟩, h2⟩) | ⟨_, h1⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr h1)

theorem mem_fixIdx {f : Nat → Nat} {T : List Nat} {q : Nat} :
    q ∈ (T.zipIdx.filter fun p => f p.1 == p.1).map (·.2) ↔
      ∃ hq : q < T.length, f T[q] = T[q] := by
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨c, i⟩, ⟨hm, hf⟩, rfl⟩
    obtain ⟨-, hi, hc⟩ := List.mem_zipIdx hm
    simp only [Nat.zero_add, Nat.sub_zero] at hi hc
    refine ⟨hi, ?_⟩
    simp only at hf ⊢
    rw [← hc]
    exact hf
  · rintro ⟨hq, hf⟩
    refine ⟨(T[q], q), ⟨?_, hf⟩, rfl⟩
    have hq' : q < T.zipIdx.length := by simpa using hq
    have := List.getElem_mem hq'
    simpa using this

theorem nodup_fixIdx (f : Nat → Nat) (T : List Nat) :
    ((T.zipIdx.filter fun p => f p.1 == p.1).map (·.2)).Nodup := by
  have h : (T.zipIdx.map (·.2)).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  exact h.sublist (List.filter_sublist.map _)

theorem fpOK_sound {f : Nat → Nat} {T : List Nat} {C W M A : Nat} {bs : List Nat}
    {pl : List (Nat × Nat)} {pm um fx : List Nat} {ft : List (Nat × Nat × Nat)} {b6 : List Nat}
    (h : fpOK f T C W M A bs pl pm um fx ft b6 = true) :
    bs.length ≤ 8 ∧ pl.length = 20 ∧
      (∀ q ∈ pl, planeK f M A q.1 q.2 = true ∧ ∃ m, trXorSel bs m = fldW 20 W q.2 ^^^ fldW 20 W q.1) ∧
      (∀ t < 20, trXorSel (pl.map fun p => fldW 20 W p.1) (um.getD t 0) = 2 ^ t) ∧
      (∀ q, q ∈ fx ↔ ∃ hq : q < T.length, f T[q] = T[q]) ∧ fx.Nodup ∧ fx.length % 2 = 1 ∧
      Reach fx.length fx.length (· == 0) (fxEdge C fx) ∧
      (∀ x ∈ b6, x ∈ fx) ∧ indep6 (b6.map fun x => fldW 12 C x / 64) = true := by
  unfold fpOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbs, hpl⟩, hpm⟩, hzip⟩, hum⟩, hfx⟩, hodd⟩, htree⟩, hb6⟩, hind⟩ := h
  refine ⟨hbs, hpl, fun q hq => ?_, hum, fun q => by rw [← hfx]; exact mem_fixIdx,
    by rw [← hfx]; exact nodup_fixIdx f T, hodd, reach_of_treeK htree, hb6, hind⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  have hi' : i < (pl.zip pm).length := by simp [hpl, hpm] at hi ⊢; omega
  have h1 := hzip _ (List.getElem_mem hi')
  simp only [List.getElem_zip, beq_iff_eq] at h1
  exact ⟨h1.1, _, h1.2⟩

end CFSG.SmithL6.K
