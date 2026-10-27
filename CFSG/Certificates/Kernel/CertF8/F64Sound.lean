module

public import Certificates.Data.Kernel.CertF8.Pack64
public import CFSG.Certificates.Kernel.CertF8.F512Sound
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Pair

public section

namespace CFSG.KC.CertF8

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
open CFSG.KC.Misc.G2U (pk pk_cons_eq pk_nil testBit_pk)
open CFSG.KC.G28 (fld)

@[expose] def x64E : GF64 := ⟨GF8.ofNat' 2, 0⟩

@[expose] def w64E : GF64 := ⟨0, 1⟩

theorem toNat64_lt : ∀ a : GF64, a.toNat < 2 ^ 6 := by decide +kernel

theorem toNat64_inj {a b : GF64} (h : a.toNat = b.toNat) : a = b := by
  rw [← GF64.ofNat'_toNat a, h, GF64.ofNat'_toNat]

theorem lin_PX6 : ∀ a : GF64, lin M6 PX6 a.toNat = (x64E * a).toNat := by decide +kernel

theorem lin_PW6 : ∀ a : GF64, lin M6 PW6 a.toNat = (w64E * a).toNat := by decide +kernel

theorem lin_PF6 : ∀ a : GF64, lin M6 PF6 a.toNat = (frobF a).toNat := by decide +kernel

theorem enc64_pk (a : GF64) : a.toNat = pk 3 [a.lo.toNat, a.hi.toNat] := by
  rw [pk_cons_eq a.lo.val.isLt, pk_cons_eq a.hi.val.isLt, pk_nil, GF64.toNat]
  ring

theorem lt_enc64 (a : GF64) : ∀ x ∈ [a.lo.toNat, a.hi.toNat], x < 2 ^ 3 := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact a.lo.val.isLt
  · exact a.hi.val.isLt

theorem enc64_bit_add (u v : GF64) {q : ℕ} (hq : q < 6) :
    (u + v).toNat.testBit q = (u.toNat.testBit q ^^ v.toNat.testBit q) := by
  obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < 2 ∧ k < 3 ∧ q = 3 * i + k :=
    ⟨q / 3, q % 3, by omega, by omega, by omega⟩
  rw [enc64_pk, enc64_pk, enc64_pk, testBit_pk (lt_enc64 _) _ hk, testBit_pk (lt_enc64 _) _ hk,
    testBit_pk (lt_enc64 _) _ hk]
  interval_cases i <;> simp [GF64.lo_add, GF64.hi_add, toNat_add8, Nat.testBit_xor]

@[expose] def bas64 (b : ℕ) : GF64 := x64E ^ (b % 3) * w64E ^ (b / 3)

theorem eq_sum_basis64 : ∀ a : GF64,
    a = ∑ b : Fin 6, if a.toNat.testBit b then bas64 b else 0 := by decide +kernel

theorem enc64_zero : (0 : GF64).toNat = 0 := rfl

theorem enc64_sum_bit {q : ℕ} (hq : q < 6) (f : ℕ → GF64) : ∀ n : ℕ,
    (∑ i : Fin n, f i).toNat.testBit q = bxr (fun i => (f i).toNat.testBit q) n
  | 0 => by simp [enc64_zero, bxr]
  | n + 1 => by
    rw [Fin.sum_univ_castSucc, enc64_bit_add _ _ hq]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [enc64_sum_bit hq f n]
    rfl

theorem enc64_ite_bit (c : Bool) (w : GF64) (q : ℕ) :
    (if c then w else 0).toNat.testBit q = (c && w.toNat.testBit q) := by
  cases c <;> simp [enc64_zero]

theorem enc64_mul_bit (a v : GF64) {q : ℕ} (hq : q < 6) :
    (a * v).toNat.testBit q =
      bxr (fun b => (a.toNat.testBit b && (bas64 b * v).toNat.testBit q)) 6 := by
  have e : a * v = ∑ b : Fin 6, if a.toNat.testBit b then bas64 b * v else 0 := by
    nth_rewrite 1 [eq_sum_basis64 a]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [e, enc64_sum_bit hq (fun b => if a.toNat.testBit b then bas64 b * v else 0)]
  simp only [enc64_ite_bit]

@[expose] noncomputable def codeA64 (A : Array GF64) : ℕ :=
  pk 6 ((List.range 64).map fun t => (A.getD t 0).toNat)

theorem codeA64_lt_list (A : Array GF64) :
    ∀ x ∈ (List.range 64).map (fun t => (A.getD t 0).toNat), x < 2 ^ 6 := by
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
  exact toNat64_lt _

theorem rep_codeA64 (A : Array GF64) : Rep 6 64 (codeA64 A) (fun t => (A.getD t 0).toNat) := by
  intro t ht q hq
  rw [codeA64, testBit_pk (codeA64_lt_list A) t hq, List.getD_eq_getElem _ _ (by simpa using ht),
    List.getElem_map, List.getElem_range]

theorem M6_eq : M6 = pk 6 (List.replicate 64 1) := by decide +kernel

theorem L8w_eq : L8w = pk 48 (List.replicate 8 1) := by decide +kernel

theorem F48_eq : F48 = 2 ^ 48 - 1 := by decide +kernel

theorem PX6_lt : ∀ p ∈ PX6, p.1 < 6 ∧ p.2 < 6 := by decide +kernel

theorem PW6_lt : ∀ p ∈ PW6, p.1 < 6 ∧ p.2 < 6 := by decide +kernel

theorem PF6_lt : ∀ p ∈ PF6, p.1 < 6 ∧ p.2 < 6 := by decide +kernel

theorem rep_lin64 {P : List (ℕ × ℕ)} (hP : ∀ p ∈ P, p.1 < 6 ∧ p.2 < 6) (g : GF64 → GF64)
    (hg : ∀ a : GF64, lin M6 P a.toNat = (g a).toNat) {x : ℕ} {E : ℕ → GF64}
    (h : Rep 6 64 x (fun t => (E t).toNat)) : Rep 6 64 (lin M6 P x) (fun t => (g (E t)).toNat) := by
  have h2 := lin_rep (by norm_num) (by norm_num) M6_eq P hP h
  intro t ht q hq
  rw [h2 t ht q hq]
  simp only [hg]

theorem bas64_steps : bas64 0 = 1 ∧ bas64 1 = x64E * bas64 0 ∧ bas64 2 = x64E * bas64 1 ∧
    bas64 3 = w64E * bas64 0 ∧ bas64 4 = x64E * bas64 3 ∧ bas64 5 = x64E * bas64 4 := by
  decide +kernel

theorem rep_step64 {P : List (ℕ × ℕ)} (hP : ∀ p ∈ P, p.1 < 6 ∧ p.2 < 6) (g : GF64)
    (hg : ∀ a : GF64, lin M6 P a.toNat = (g * a).toNat) {x : ℕ} {B : ℕ → GF64} {b b' : ℕ}
    (hb : bas64 b' = g * bas64 b) (h : Rep 6 64 x (fun t => (bas64 b * B t).toNat)) :
    Rep 6 64 (lin M6 P x) (fun t => (bas64 b' * B t).toNat) := by
  have h2 := rep_lin64 hP (fun a => g * a) hg h
  intro t ht q hq
  rw [h2 t ht q hq]
  simp only [hb, mul_assoc]

theorem codeA64_mulArr (A B : Array GF64) :
    codeA64 (mulArr A B) = mulS64 (codeA64 A) (codeA64 B) := by
  simp only [mulS64, CFSG.KC.G28.letN_eq]
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := bas64_steps
  have r0 : Rep 6 64 (codeA64 B) (fun t => (bas64 0 * B.getD t 0).toNat) := by
    intro t ht q hq
    rw [rep_codeA64 B t ht q hq]
    simp only [b0, one_mul]
  have r1 := rep_step64 PX6_lt x64E lin_PX6 b1 r0
  have r2 := rep_step64 PX6_lt x64E lin_PX6 b2 r1
  have r3 := rep_step64 PW6_lt w64E lin_PW6 b3 r0
  have r4 := rep_step64 PX6_lt x64E lin_PX6 b4 r3
  have r5 := rep_step64 PX6_lt x64E lin_PX6 b5 r4
  have rA := rep_codeA64 A
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 384
  · obtain ⟨i, j, s, hi, hj, hs, rfl⟩ : ∃ i j s, i < 8 ∧ j < 8 ∧ s < 6 ∧ p = 48 * i + (6 * j + s) :=
      ⟨p / 48, p % 48 / 6, p % 6, by omega, by omega, by omega, by omega⟩
    have hT : ∀ k < 8, (termsL (codeA64 A) k 6 48 L8w F48 [codeA64 B, lin M6 PX6 (codeA64 B),
        lin M6 PX6 (lin M6 PX6 (codeA64 B)), lin M6 PW6 (codeA64 B),
        lin M6 PX6 (lin M6 PW6 (codeA64 B)), lin M6 PX6 (lin M6 PX6 (lin M6 PW6 (codeA64 B)))]
          0).testBit (48 * i + (6 * j + s)) =
        (A.getD (8 * i + k) 0 * B.getD (8 * k + j) 0).toNat.testBit s := by
      intro k hk
      have hq : 6 * j + s < 48 := by omega
      rw [termsL_bit, enc64_mul_bit _ _ hs]
      simp only [bxl, bxr]
      have tb := fun X o' (b : ℕ) => term_bit (n := 8) (by norm_num) L8w_eq F48_eq (codeA64 A)
        (6 * k + b) X o' hi hq
      rw [tb, tb, tb, tb, tb, tb]
      have ea : ∀ b < 6, (codeA64 A).testBit (6 * k + b + 48 * i) =
          (A.getD (8 * i + k) 0).toNat.testBit b := by
        intro b hb
        have e : 6 * k + b + 48 * i = 6 * (8 * i + k) + b := by omega
        rw [e, rA _ (by omega) b hb]
      have ex : 48 * k + (6 * j + s) = 6 * (8 * k + j) + s := by omega
      rw [ea 0 (by omega), ea 1 (by omega), ea 2 (by omega), ea 3 (by omega), ea 4 (by omega),
        ea 5 (by omega), ex, r0 _ (by omega) s hs, r1 _ (by omega) s hs, r2 _ (by omega) s hs,
        r3 _ (by omega) s hs, r4 _ (by omega) s hs, r5 _ (by omega) s hs]
      simp only [Nat.add_zero, Bool.xor_false, Bool.false_xor, Bool.xor_assoc]
    rw [mulG_bit]
    have e : 48 * i + (6 * j + s) = 6 * (8 * i + j) + s := by omega
    rw [e, rep_codeA64 (mulArr A B) _ (by omega) s hs, ← e]
    simp only [bxr]
    rw [hT 0 (by omega), hT 1 (by omega), hT 2 (by omega), hT 3 (by omega), hT 4 (by omega),
      hT 5 (by omega), hT 6 (by omega), hT 7 (by omega)]
    rw [mulArr, getD_ofFn _ _ (by omega)]
    have e1 : (8 * i + j) / 8 = i := by omega
    have e2 : (8 * i + j) % 8 = j := by omega
    simp only [e1, e2, enc64_bit_add _ _ hs, Bool.false_xor, Bool.xor_assoc, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.zero_add, Nat.reduceMul]
  · have hc := CFSG.KC.Misc.G2U.pk_lt (codeA64_lt_list (mulArr A B))
    rw [List.length_map, List.length_range] at hc
    rw [codeA64, bit_hi_of_lt hc (by omega), mulG_bit_hi (by norm_num) L8w_eq _ _ (by omega)]

theorem codeA64_ext {x y : ℕ} {E : ℕ → ℕ} (hx : Rep 6 64 x E) (hy : Rep 6 64 y E)
    (hx' : ∀ p, 6 * 64 ≤ p → x.testBit p = false) (hy' : ∀ p, 6 * 64 ≤ p → y.testBit p = false) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 6 * 64
  · obtain ⟨t, q, ht, hq, rfl⟩ := decomp (by norm_num : 0 < 6) hp
    rw [hx t ht q hq, hy t ht q hq]
  · rw [hx' p (by omega), hy' p (by omega)]

theorem codeA64_hi (A : Array GF64) (p : ℕ) (hp : 6 * 64 ≤ p) :
    (codeA64 A).testBit p = false := by
  have hc := CFSG.KC.Misc.G2U.pk_lt (codeA64_lt_list A)
  rw [List.length_map, List.length_range] at hc
  exact bit_hi_of_lt hc hp

theorem linT64_hi (y b b' : ℕ) (hb' : b' < 6) (p : ℕ) (hp : 6 * 64 ≤ p) :
    (Nat.shiftLeft (Nat.land (Nat.shiftRight y b) M6) b').testBit p = false := by
  change ((y >>> b &&& M6) <<< b').testBit p = false
  rw [Nat.testBit_shiftLeft, Nat.testBit_and]
  by_cases h : 6 * 64 ≤ p - b'
  · rw [M_bit_hi (by norm_num) M6_eq h]
    simp
  · have e : p - b' = 6 * 63 + (p - b' - 378) := by omega
    rw [e, M_bit (by norm_num) M6_eq (by norm_num) (by omega)]
    simp
    omega

theorem lin64_hi (P : List (ℕ × ℕ)) (hP : ∀ p ∈ P, p.1 < 6 ∧ p.2 < 6) (y : ℕ) (p : ℕ)
    (hp : 6 * 64 ≤ p) : (lin M6 P y).testBit p = false := by
  induction P with
  | nil => simp [lin]
  | cons a P ih =>
    change (Nat.shiftLeft (Nat.land (Nat.shiftRight y a.1) M6) a.2 ^^^ lin M6 P y).testBit p = false
    rw [Nat.testBit_xor, linT64_hi y a.1 a.2 (hP a (List.mem_cons_self ..)).2 p hp,
      ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))]
    rfl

theorem codeA64_frobArr (A : Array GF64) : codeA64 (frobArr A) = frobS64 (codeA64 A) := by
  rw [frobS64, CFSG.KC.G28.letN_eq]
  have h1 := rep_lin64 PF6_lt frobF lin_PF6 (rep_codeA64 A)
  have h2 : Rep 6 64 (codeA64 (frobArr A)) (fun t => (frobF (A.getD t 0)).toNat) := by
    intro t ht q hq
    rw [rep_codeA64 (frobArr A) t ht q hq]
    simp only [getD_frobArr]
  exact codeA64_ext h2 h1 (codeA64_hi _) (lin64_hi PF6 PF6_lt _)

theorem codeA64_frobPow (n : ℕ) (A : Array GF64) :
    codeA64 (frobPow n A) = frobK64 n (codeA64 A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [frobPow, codeA64_frobArr, ih]
    rfl

@[expose] noncomputable def codePr64 (p : Pr) : ℕ × ℕ := (codeA64 p.1, p.2)

theorem codePr64_mulP (p q : Pr) : codePr64 (mulP p q) = mulPr64 (codePr64 p) (codePr64 q) := by
  simp only [codePr64, mulP, mulPr64, codeA64_mulArr, codeA64_frobPow]
  rfl

theorem codeA64_inj {A B : Array GF64} (hA : A.size = 64) (hB : B.size = 64)
    (h : codeA64 A = codeA64 B) : A = B := by
  refine eq_of_toMat_eq hA hB (Matrix.ext fun i j => ?_)
  have hl := CFSG.KC.Misc.G2U.pk_inj (codeA64_lt_list A) (codeA64_lt_list B) (by simp) h
  have e := congrArg (fun l => l.getD (8 * i.val + j.val) 0) hl
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_map, List.getElem_map, List.getElem_range] at e
  exact toNat64_inj e

theorem codePr64_inj {p q : Pr} (hp : p.1.size = 64) (hq : q.1.size = 64)
    (h : codePr64 p = codePr64 q) : p = q := by
  simp only [codePr64, Prod.mk.injEq] at h
  exact Prod.ext (codeA64_inj hp hq h.1) h.2

end CFSG.KC.CertF8

end
