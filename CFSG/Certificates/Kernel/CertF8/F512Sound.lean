module

public import Certificates.Data.Kernel.CertF8.Pack512
public import CFSG.Certificates.Kernel.CertF8.LaneSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Pair

public section

namespace CFSG.KC.CertF8

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuterD48
open CFSG.KC.Misc.G2U (pk pk_cons_eq pk_nil testBit_pk)
open CFSG.KC.G28 (fld)

@[expose] def enc512 (a : GF512) : ℕ := a.c0.toNat + 8 * a.c1.toNat + 64 * a.c2.toNat

@[expose] def xE : GF512 := ⟨GF8.ofNat' 2, 0, 0⟩

@[expose] def sE : GF512 := ⟨0, 1, 0⟩

theorem enc512_lt : ∀ a : GF512, enc512 a < 2 ^ 9 := by decide +kernel

@[expose] def dec512 (n : ℕ) : GF512 := ⟨GF8.ofNat' n, GF8.ofNat' (n / 8), GF8.ofNat' (n / 64)⟩

theorem dec_enc512 : ∀ a : GF512, dec512 (enc512 a) = a := by decide +kernel

theorem enc512_inj {a b : GF512} (h : enc512 a = enc512 b) : a = b := by
  rw [← dec_enc512 a, h, dec_enc512]

theorem lin_PX9 : ∀ a : GF512, lin M9 PX9 (enc512 a) = enc512 (xE * a) := by decide +kernel

theorem lin_PS9 : ∀ a : GF512, lin M9 PS9 (enc512 a) = enc512 (sE * a) := by decide +kernel

theorem lin_PF9 : ∀ a : GF512, lin M9 PF9 (enc512 a) = enc512 (frobF a) := by decide +kernel

theorem toNat_add8 : ∀ u v : GF8, (u + v).toNat = u.toNat ^^^ v.toNat := by decide +kernel

theorem enc_pk (a : GF512) : enc512 a = pk 3 [a.c0.toNat, a.c1.toNat, a.c2.toNat] := by
  rw [pk_cons_eq a.c0.val.isLt, pk_cons_eq a.c1.val.isLt, pk_cons_eq a.c2.val.isLt, pk_nil, enc512]
  ring

theorem lt_enc (a : GF512) : ∀ x ∈ [a.c0.toNat, a.c1.toNat, a.c2.toNat], x < 2 ^ 3 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact a.c0.val.isLt
  · exact a.c1.val.isLt
  · exact a.c2.val.isLt

theorem enc512_bit_add (u v : GF512) {q : ℕ} (hq : q < 9) :
    (enc512 (u + v)).testBit q = ((enc512 u).testBit q ^^ (enc512 v).testBit q) := by
  obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < 3 ∧ k < 3 ∧ q = 3 * i + k :=
    ⟨q / 3, q % 3, by omega, by omega, by omega⟩
  rw [enc_pk, enc_pk, enc_pk, testBit_pk (lt_enc _) _ hk, testBit_pk (lt_enc _) _ hk,
    testBit_pk (lt_enc _) _ hk]
  interval_cases i <;>
    simp [GF512.c0_add, GF512.c1_add, GF512.c2_add, toNat_add8, Nat.testBit_xor]

@[expose] def bas (b : ℕ) : GF512 := xE ^ (b % 3) * sE ^ (b / 3)

theorem eq_sum_basis : ∀ a : GF512,
    a = ∑ b : Fin 9, if (enc512 a).testBit b then bas b else 0 := by decide +kernel

theorem enc512_zero : enc512 0 = 0 := rfl

theorem bit_hi_of_lt {x n p : ℕ} (h : x < 2 ^ n) (hp : n ≤ p) : x.testBit p = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hp))

theorem enc_sum_bit {q : ℕ} (hq : q < 9) (f : ℕ → GF512) : ∀ n : ℕ,
    (enc512 (∑ i : Fin n, f i)).testBit q = bxr (fun i => (enc512 (f i)).testBit q) n
  | 0 => by simp [enc512_zero, bxr]
  | n + 1 => by
    rw [Fin.sum_univ_castSucc, enc512_bit_add _ _ hq]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [enc_sum_bit hq f n]
    rfl

theorem enc_ite_bit (c : Bool) (w : GF512) (q : ℕ) :
    (enc512 (if c then w else 0)).testBit q = (c && (enc512 w).testBit q) := by
  cases c <;> simp [enc512_zero]

theorem enc512_mul_bit (a v : GF512) {q : ℕ} (hq : q < 9) :
    (enc512 (a * v)).testBit q =
      bxr (fun b => ((enc512 a).testBit b && (enc512 (bas b * v)).testBit q)) 9 := by
  have e : a * v = ∑ b : Fin 9, if (enc512 a).testBit b then bas b * v else 0 := by
    nth_rewrite 1 [eq_sum_basis a]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [e, enc_sum_bit hq (fun b => if (enc512 a).testBit b then bas b * v else 0)]
  simp only [enc_ite_bit]

@[expose] noncomputable def codeA (A : Array GF512) : ℕ :=
  pk 9 ((List.range 64).map fun t => enc512 (A.getD t 0))

theorem codeA_lt_list (A : Array GF512) :
    ∀ x ∈ (List.range 64).map (fun t => enc512 (A.getD t 0)), x < 2 ^ 9 := by
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
  exact enc512_lt _

theorem rep_codeA (A : Array GF512) : Rep 9 64 (codeA A) (fun t => enc512 (A.getD t 0)) := by
  intro t ht q hq
  rw [codeA, testBit_pk (codeA_lt_list A) t hq, List.getD_eq_getElem _ _ (by simpa using ht),
    List.getElem_map, List.getElem_range]

theorem M9_eq : M9 = pk 9 (List.replicate 64 1) := by decide +kernel

theorem L8_eq : L8 = pk 72 (List.replicate 8 1) := by decide +kernel

theorem F72_eq : F72 = 2 ^ 72 - 1 := by decide +kernel

theorem PX9_lt : ∀ p ∈ PX9, p.1 < 9 ∧ p.2 < 9 := by decide +kernel

theorem PS9_lt : ∀ p ∈ PS9, p.1 < 9 ∧ p.2 < 9 := by decide +kernel

theorem PF9_lt : ∀ p ∈ PF9, p.1 < 9 ∧ p.2 < 9 := by decide +kernel

theorem rep_lin {P : List (ℕ × ℕ)} (hP : ∀ p ∈ P, p.1 < 9 ∧ p.2 < 9) (g : GF512 → GF512)
    (hg : ∀ a : GF512, lin M9 P (enc512 a) = enc512 (g a)) {x : ℕ} {E : ℕ → GF512}
    (h : Rep 9 64 x (fun t => enc512 (E t))) : Rep 9 64 (lin M9 P x) (fun t => enc512 (g (E t))) := by
  have h2 := lin_rep (by norm_num) (by norm_num) M9_eq P hP h
  intro t ht q hq
  rw [h2 t ht q hq]
  simp only [hg]

theorem bas_steps : bas 0 = 1 ∧ bas 1 = xE * bas 0 ∧ bas 2 = xE * bas 1 ∧ bas 3 = sE * bas 0 ∧
    bas 4 = xE * bas 3 ∧ bas 5 = xE * bas 4 ∧ bas 6 = sE * bas 3 ∧ bas 7 = xE * bas 6 ∧
    bas 8 = xE * bas 7 := by decide +kernel

theorem rep_step {P : List (ℕ × ℕ)} (hP : ∀ p ∈ P, p.1 < 9 ∧ p.2 < 9) (g : GF512)
    (hg : ∀ a : GF512, lin M9 P (enc512 a) = enc512 (g * a)) {x : ℕ} {B : ℕ → GF512} {b b' : ℕ}
    (hb : bas b' = g * bas b) (h : Rep 9 64 x (fun t => enc512 (bas b * B t))) :
    Rep 9 64 (lin M9 P x) (fun t => enc512 (bas b' * B t)) := by
  have h2 := rep_lin hP (fun a => g * a) hg h
  intro t ht q hq
  rw [h2 t ht q hq]
  simp only [hb, mul_assoc]

@[expose] def bxl : List ℕ → ℕ → (ℕ → ℕ → Bool) → Bool
  | [], _, _ => false
  | X :: Xs, b, g => g b X ^^ bxl Xs (b + 1) g

theorem termsL_bit (a k e W L F q : ℕ) : ∀ (Xs : List ℕ) (b : ℕ),
    (termsL a k e W L F Xs b).testBit q =
      bxl Xs b (fun b X => (Nat.land (spr a (e * k + b) L F) (Nat.mul (fld X (W * k) W) L)).testBit q)
  | [], _ => by simp [termsL, bxl]
  | X :: Xs, b => by
    change (Nat.land (spr a (Nat.add (Nat.mul e k) b) L F) (Nat.mul (fld X (Nat.mul W k) W) L) ^^^
      termsL a k e W L F Xs (Nat.succ b)).testBit q = _
    rw [Nat.testBit_xor, termsL_bit a k e W L F q Xs (Nat.succ b)]
    rfl

theorem codeA_mulArr (A B : Array GF512) : codeA (mulArr A B) = mulS512 (codeA A) (codeA B) := by
  simp only [mulS512, CFSG.KC.G28.letN_eq]
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := bas_steps
  have r0 : Rep 9 64 (codeA B) (fun t => enc512 (bas 0 * B.getD t 0)) := by
    intro t ht q hq
    rw [rep_codeA B t ht q hq]
    simp only [b0, one_mul]
  have r1 := rep_step PX9_lt xE lin_PX9 b1 r0
  have r2 := rep_step PX9_lt xE lin_PX9 b2 r1
  have r3 := rep_step PS9_lt sE lin_PS9 b3 r0
  have r4 := rep_step PX9_lt xE lin_PX9 b4 r3
  have r5 := rep_step PX9_lt xE lin_PX9 b5 r4
  have r6 := rep_step PS9_lt sE lin_PS9 b6 r3
  have r7 := rep_step PX9_lt xE lin_PX9 b7 r6
  have r8 := rep_step PX9_lt xE lin_PX9 b8 r7
  have rA := rep_codeA A
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 576
  · obtain ⟨i, j, s, hi, hj, hs, rfl⟩ : ∃ i j s, i < 8 ∧ j < 8 ∧ s < 9 ∧ p = 72 * i + (9 * j + s) :=
      ⟨p / 72, p % 72 / 9, p % 9, by omega, by omega, by omega, by omega⟩
    have hT : ∀ k < 8, (termsL (codeA A) k 9 72 L8 F72 [codeA B, lin M9 PX9 (codeA B),
        lin M9 PX9 (lin M9 PX9 (codeA B)), lin M9 PS9 (codeA B), lin M9 PX9 (lin M9 PS9 (codeA B)),
        lin M9 PX9 (lin M9 PX9 (lin M9 PS9 (codeA B))), lin M9 PS9 (lin M9 PS9 (codeA B)),
        lin M9 PX9 (lin M9 PS9 (lin M9 PS9 (codeA B))),
        lin M9 PX9 (lin M9 PX9 (lin M9 PS9 (lin M9 PS9 (codeA B))))] 0).testBit
          (72 * i + (9 * j + s)) =
        (enc512 (A.getD (8 * i + k) 0 * B.getD (8 * k + j) 0)).testBit s := by
      intro k hk
      have hq : 9 * j + s < 72 := by omega
      rw [termsL_bit, enc512_mul_bit _ _ hs]
      simp only [bxl, bxr]
      have tb := fun X o' (b : ℕ) => term_bit (n := 8) (by norm_num) L8_eq F72_eq (codeA A)
        (9 * k + b) X o' hi hq
      rw [tb, tb, tb, tb, tb, tb, tb, tb, tb]
      have ea : ∀ b < 9, (codeA A).testBit (9 * k + b + 72 * i) =
          (enc512 (A.getD (8 * i + k) 0)).testBit b := by
        intro b hb
        have e : 9 * k + b + 72 * i = 9 * (8 * i + k) + b := by omega
        rw [e, rA _ (by omega) b hb]
      have ex : 72 * k + (9 * j + s) = 9 * (8 * k + j) + s := by omega
      rw [ea 0 (by omega), ea 1 (by omega), ea 2 (by omega), ea 3 (by omega), ea 4 (by omega),
        ea 5 (by omega), ea 6 (by omega), ea 7 (by omega), ea 8 (by omega), ex,
        r0 _ (by omega) s hs, r1 _ (by omega) s hs, r2 _ (by omega) s hs, r3 _ (by omega) s hs,
        r4 _ (by omega) s hs, r5 _ (by omega) s hs, r6 _ (by omega) s hs, r7 _ (by omega) s hs,
        r8 _ (by omega) s hs]
      simp only [Nat.add_zero, Bool.xor_false, Bool.false_xor, Bool.xor_assoc]
    rw [mulG_bit]
    have e : 72 * i + (9 * j + s) = 9 * (8 * i + j) + s := by omega
    rw [e, rep_codeA (mulArr A B) _ (by omega) s hs, ← e]
    simp only [bxr]
    rw [hT 0 (by omega), hT 1 (by omega), hT 2 (by omega), hT 3 (by omega), hT 4 (by omega),
      hT 5 (by omega), hT 6 (by omega), hT 7 (by omega)]
    rw [mulArr, getD_ofFn _ _ (by omega)]
    have e1 : (8 * i + j) / 8 = i := by omega
    have e2 : (8 * i + j) % 8 = j := by omega
    simp only [e1, e2, enc512_bit_add _ _ hs, Bool.false_xor, Bool.xor_assoc, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.zero_add, Nat.reduceMul]
  · have hc := CFSG.KC.Misc.G2U.pk_lt (codeA_lt_list (mulArr A B))
    rw [List.length_map, List.length_range] at hc
    rw [codeA, bit_hi_of_lt hc (by omega), mulG_bit_hi (by norm_num) L8_eq _ _ (by omega)]

theorem codeA_ext {x y : ℕ} {E : ℕ → ℕ} (hx : Rep 9 64 x E) (hy : Rep 9 64 y E)
    (hx' : ∀ p, 9 * 64 ≤ p → x.testBit p = false) (hy' : ∀ p, 9 * 64 ≤ p → y.testBit p = false) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 9 * 64
  · obtain ⟨t, q, ht, hq, rfl⟩ := decomp (by norm_num : 0 < 9) hp
    rw [hx t ht q hq, hy t ht q hq]
  · rw [hx' p (by omega), hy' p (by omega)]

theorem codeA_hi (A : Array GF512) (p : ℕ) (hp : 9 * 64 ≤ p) : (codeA A).testBit p = false := by
  have hc := CFSG.KC.Misc.G2U.pk_lt (codeA_lt_list A)
  rw [List.length_map, List.length_range] at hc
  exact bit_hi_of_lt hc hp

theorem linT_hi (y b b' : ℕ) (hb' : b' < 9) (p : ℕ) (hp : 9 * 64 ≤ p) :
    (Nat.shiftLeft (Nat.land (Nat.shiftRight y b) M9) b').testBit p = false := by
  change ((y >>> b &&& M9) <<< b').testBit p = false
  rw [Nat.testBit_shiftLeft, Nat.testBit_and]
  by_cases h : 9 * 64 ≤ p - b'
  · rw [M_bit_hi (by norm_num) M9_eq h]
    simp
  · have e : p - b' = 9 * 63 + (p - b' - 567) := by omega
    rw [e, M_bit (by norm_num) M9_eq (by norm_num) (by omega)]
    simp
    omega

theorem lin_hi (P : List (ℕ × ℕ)) (hP : ∀ p ∈ P, p.1 < 9 ∧ p.2 < 9) (y : ℕ) (p : ℕ)
    (hp : 9 * 64 ≤ p) : (lin M9 P y).testBit p = false := by
  induction P with
  | nil => simp [lin]
  | cons a P ih =>
    change (Nat.shiftLeft (Nat.land (Nat.shiftRight y a.1) M9) a.2 ^^^ lin M9 P y).testBit p = false
    rw [Nat.testBit_xor, linT_hi y a.1 a.2 (hP a (List.mem_cons_self ..)).2 p hp,
      ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))]
    rfl

theorem codeA_frobArr (A : Array GF512) : codeA (frobArr A) = frobS (codeA A) := by
  rw [frobS, CFSG.KC.G28.letN_eq]
  have h1 := rep_lin PF9_lt frobF lin_PF9 (rep_codeA A)
  have h2 : Rep 9 64 (codeA (frobArr A)) (fun t => enc512 (frobF (A.getD t 0))) := by
    intro t ht q hq
    rw [rep_codeA (frobArr A) t ht q hq]
    simp only [getD_frobArr]
  exact codeA_ext h2 h1 (codeA_hi _) (lin_hi PF9 PF9_lt _)

theorem codeA_frobPow (n : ℕ) (A : Array GF512) : codeA (frobPow n A) = frobK n (codeA A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [frobPow, codeA_frobArr, ih]
    rfl

@[expose] noncomputable def codePr (p : Pr) : ℕ × ℕ := (codeA p.1, p.2)

theorem codePr_mulP (p q : Pr) : codePr (mulP p q) = mulPr (codePr p) (codePr q) := by
  simp only [codePr, mulP, mulPr, codeA_mulArr, codeA_frobPow]
  rfl

theorem codeA_inj {A B : Array GF512} (hA : A.size = 64) (hB : B.size = 64)
    (h : codeA A = codeA B) : A = B := by
  refine eq_of_toMat_eq hA hB (Matrix.ext fun i j => ?_)
  have hl := CFSG.KC.Misc.G2U.pk_inj (codeA_lt_list A) (codeA_lt_list B) (by simp) h
  have e := congrArg (fun l => l.getD (8 * i.val + j.val) 0) hl
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_map, List.getElem_map, List.getElem_range] at e
  exact enc512_inj e

theorem codePr_inj {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64)
    (h : codePr p = codePr q) : p = q := by
  simp only [codePr, Prod.mk.injEq] at h
  exact Prod.ext (codeA_inj hp hq h.1) h.2

end CFSG.KC.CertF8

end
