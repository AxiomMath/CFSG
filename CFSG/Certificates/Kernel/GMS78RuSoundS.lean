module

public import Certificates.Data.Kernel.GMS78Ru
public import CFSG.Certificates.Kernel.GMS78RuGen
public import CFSG.Certificates.Kernel.GMS78RuSoundBase
public import CFSG.Certificates.Kernel.GMS78RuSoundC3

public section

namespace CFSG.KC.GMS.Snd

open CFSG.KLie.CT CFSG.KC.Loop CFSG.GMS78Ru CFSG.GMS78RuSim

theorem linAppK_eq (R t : Nat) : linAppK R t =
    (if t.testBit 2 then fget R 2 3 else 0) ^^^ ((if t.testBit 1 then fget R 1 3 else 0) ^^^
      (if t.testBit 0 then fget R 0 3 else 0)) := by
  simp only [linAppK, xorN_succ, xorN_zero, nIf_eq, bit_eq, Nat.xor_zero]

theorem linAppK_lt (R t : Nat) : linAppK R t < 8 := by
  rw [linAppK_eq]
  refine xor_lt8 ?_ (xor_lt8 ?_ ?_) <;> split <;> simp [fget3_lt]

theorem linAppK_xor (R t t' : Nat) : linAppK R (t ^^^ t') = linAppK R t ^^^ linAppK R t' := by
  simp only [linAppK_eq, Nat.testBit_xor]
  cases t.testBit 0 <;> cases t'.testBit 0 <;> cases t.testBit 1 <;> cases t'.testBit 1 <;>
    cases t.testBit 2 <;> cases t'.testBit 2 <;> simp <;> xsimp

theorem linAppK_zero (R : Nat) : linAppK R 0 = 0 := by simp [linAppK_eq]

theorem fin8_ite_val (b : Bool) (x : Fin 8) :
    (if b = true then x else 0).val = if b = true then x.val else 0 := by
  cases b <;> rfl

theorem linApply_val (r : Lin8) (t : Fin 8) : (linApply r t).val = linAppK (packV r) t.val := by
  rw [linAppK_eq, fget_packV0, fget_packV1, fget_packV2, linApply, fin8_xor_val, fin8_xor_val]
  simp only [fin8_ite_val]
  xsimp

theorem linCompK_field (R S : Nat) {k : Nat} (hk : k < 3) :
    fget (linCompK R S) k 3 = linAppK R (fget S k 3) := by
  have : linCompK R S = orN 3 (fun k => linAppK R (fget S k 3) <<< (3 * k)) := rfl
  rw [this, orN_field (fun i _ => linAppK_lt _ _) hk]

theorem linCompK_lt (R S : Nat) : linCompK R S < 512 := by
  have : linCompK R S = orN 3 (fun k => linAppK R (fget S k 3) <<< (3 * k)) := rfl
  rw [this]
  exact orN_field_lt (w := 3) (n := 3) (fun i _ => linAppK_lt _ _)

theorem packV_linComp (r s : Lin8) : packV (linComp r s) = linCompK (packV r) (packV s) := by
  apply eq_of_fget3 (packV_lt _) (linCompK_lt _ _)
  · rw [linCompK_field _ _ (by omega), fget_packV0, fget_packV0, linComp, linApply_val]
  · rw [linCompK_field _ _ (by omega), fget_packV1, fget_packV1, linComp, linApply_val]
  · rw [linCompK_field _ _ (by omega), fget_packV2, fget_packV2, linComp, linApply_val]

theorem glK_packV (r : Lin8) : glK (packV r) = indep3 r.1 r.2.1 r.2.2 := by
  rw [glK, fget_packV0, fget_packV1, fget_packV2, indep3_eq]

theorem LINID_eq : LINID = packV linId := rfl

@[expose] noncomputable def unpackV (I : Nat) : V3 :=
  (⟨fget I 0 3, fget3_lt _ _⟩, ⟨fget I 1 3, fget3_lt _ _⟩, ⟨fget I 2 3, fget3_lt _ _⟩)

theorem packV_unpackV {I : Nat} (hI : I < 512) : packV (unpackV I) = I := by
  apply eq_of_fget3 (packV_lt _) hI
  · rw [fget_packV0]; rfl
  · rw [fget_packV1]; rfl
  · rw [fget_packV2]; rfl

theorem mem_glList (r : Lin8) : r ∈ glList ↔ indep3 r.1 r.2.1 r.2.2 = true := by
  obtain ⟨a, b, c⟩ := r
  simp [glList, List.mem_filter, List.mem_flatMap, List.mem_map, all8, List.mem_finRange]

theorem linAppK_comp (A B t : Nat) : linAppK (linCompK A B) t = linAppK A (linAppK B t) := by
  rw [linAppK_eq, linCompK_field _ _ (by omega), linCompK_field _ _ (by omega),
    linCompK_field _ _ (by omega), linAppK_eq B]
  have h : ∀ (b : Bool) (x : Nat),
      (if b then linAppK A x else 0) = linAppK A (if b then x else 0) :=
    fun b x => by cases b <;> simp [linAppK_zero]
  rw [h, h, h, ← linAppK_xor, ← linAppK_xor]

theorem linApply_comp (a b : Lin8) (t : Fin 8) :
    linApply (linComp a b) t = linApply a (linApply b t) := by
  apply Fin.ext
  rw [linApply_val, linApply_val, linApply_val, packV_linComp, linAppK_comp]

theorem linComp_assoc (a b c : Lin8) : linComp (linComp a b) c = linComp a (linComp b c) :=
  Prod.ext (linApply_comp a b c.1) (Prod.ext (linApply_comp a b c.2.1) (linApply_comp a b c.2.2))

theorem linApply_id : ∀ t : Fin 8, linApply linId t = t := by decide

theorem linComp_id_left (s : Lin8) : linComp linId s = s := by
  obtain ⟨a, b, c⟩ := s
  simp only [linComp, linApply_id]

theorem linComp_id_right (r : Lin8) : linComp r linId = r := by
  obtain ⟨a, b, c⟩ := r
  apply Prod.ext <;> [skip; apply Prod.ext] <;> apply Fin.ext <;>
    simp (config := { decide := true }) [linComp, linId, linApply_val, linAppK_eq, fget_packV0,
      fget_packV1, fget_packV2]

theorem linInv_eq {r i : Lin8} (hi : i ∈ glList) (h1 : linComp r i = linId)
    (h2 : linComp i r = linId) : linInv r = i := by
  have hs : (glList.find? fun s => linComp r s == linId).isSome = true :=
    List.find?_isSome.mpr ⟨i, hi, by rw [h1]; rfl⟩
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.mp hs
  have hps := List.find?_some hs'
  rw [beq_iff_eq] at hps
  rw [linInv, hs', Option.getD_some]
  calc s = linComp linId s := (linComp_id_left s).symm
    _ = linComp (linComp i r) s := by rw [h2]
    _ = linComp i (linComp r s) := linComp_assoc _ _ _
    _ = i := by rw [hps, linComp_id_right]

@[expose] def fin3 (n : Nat) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by omega)⟩

@[expose] noncomputable def encM (A : M3) : Nat :=
  orN 9 fun k => if A (fin3 (k / 3)) (fin3 (k % 3)) then 2 ^ k else 0

theorem testBit_encM (A : M3) (k : Nat) :
    (encM A).testBit k = (decide (k < 9) && A (fin3 (k / 3)) (fin3 (k % 3))) := by
  unfold encM
  rw [Bool.eq_iff_iff, orN_testBit]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    split at h
    · rw [Nat.testBit_two_pow] at h
      have : i = k := by simpa using h
      subst this; exact ⟨hi, by assumption⟩
    · simp at h
  · rintro ⟨hk, h⟩
    exact ⟨k, hk, by simp [h]⟩

theorem fin3_eq (i : Fin 3) : fin3 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem testBit_encM' (A : M3) (i j : Fin 3) : (encM A).testBit (3 * i.val + j.val) = A i j := by
  rw [testBit_encM]
  have h1 : (3 * i.val + j.val) / 3 = i.val := by omega
  have h2 : (3 * i.val + j.val) % 3 = j.val := by omega
  have h3 : 3 * i.val + j.val < 9 := by omega
  simp [h1, h2, h3, fin3_eq]

theorem encM_lt (A : M3) : encM A < 512 :=
  orN_lt (w := 9) fun k hk => by
    split
    · exact Nat.pow_lt_pow_right (by omega) hk
    · exact Nat.two_pow_pos _

theorem encM_inj {A B : M3} (h : encM A = encM B) (i j : Fin 3) : A i j = B i j := by
  have h1 := testBit_encM' A i j
  have h2 := testBit_encM' B i j
  rw [h] at h1
  exact h1.symm.trans h2

theorem fin3_0 : fin3 0 = 0 := rfl
theorem fin3_1 : fin3 1 = 1 := rfl
theorem fin3_2 : fin3 2 = 2 := rfl

theorem m3Eq_of {A B : M3} (h : encM A = encM B) : m3Eq A B = true := by
  simp only [m3Eq, List.all_eq_true, beq_iff_eq]
  exact fun i _ j _ => encM_inj h i j

@[expose] def madd (A B : M3) : M3 := fun i j => A i j ^^ B i j

theorem encM_madd (A B : M3) : encM (madd A B) = encM A ^^^ encM B := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, testBit_encM, testBit_encM, testBit_encM, madd]
  cases decide (k < 9) <;> simp

theorem encM_zero : encM (fun _ _ => false) = 0 := by
  apply Nat.eq_of_testBit_eq; intro k; simp [testBit_encM]

theorem bmul_madd_left (A B C : M3) : bmul (madd A B) C = madd (bmul A C) (bmul B C) := by
  funext i j
  simp only [bmul, madd]
  cases A i 0 <;> cases A i 1 <;> cases A i 2 <;> cases B i 0 <;> cases B i 1 <;> cases B i 2 <;>
    cases C 0 j <;> cases C 1 j <;> cases C 2 j <;> rfl

theorem bmul_madd_right (A B C : M3) : bmul A (madd B C) = madd (bmul A B) (bmul A C) := by
  funext i j
  simp only [bmul, madd]
  cases A i 0 <;> cases A i 1 <;> cases A i 2 <;> cases B 0 j <;> cases B 1 j <;> cases B 2 j <;>
    cases C 0 j <;> cases C 1 j <;> cases C 2 j <;> rfl

theorem bmul_zero_left (C : M3) : bmul (fun _ _ => false) C = fun _ _ => false := by
  funext i j; simp [bmul]

theorem bmul_zero_right (A : M3) : bmul A (fun _ _ => false) = fun _ _ => false := by
  funext i j; simp [bmul]

theorem slToMat_xor (m m' : Nat) : slToMat (m ^^^ m') = madd (slToMat m) (slToMat m') := by
  funext i j
  simp only [madd]
  match i, j with
  | 0, 0 => exact Nat.testBit_xor m m' 6
  | 0, 1 => exact Nat.testBit_xor m m' 0
  | 0, 2 => exact Nat.testBit_xor m m' 1
  | 1, 0 => exact Nat.testBit_xor m m' 2
  | 1, 1 =>
    change ((m ^^^ m').testBit 6 ^^ (m ^^^ m').testBit 7) =
      ((m.testBit 6 ^^ m.testBit 7) ^^ (m'.testBit 6 ^^ m'.testBit 7))
    rw [Nat.testBit_xor, Nat.testBit_xor]
    cases m.testBit 6 <;> cases m.testBit 7 <;> cases m'.testBit 6 <;> cases m'.testBit 7 <;> rfl
  | 1, 2 => exact Nat.testBit_xor m m' 3
  | 2, 0 => exact Nat.testBit_xor m m' 4
  | 2, 1 => exact Nat.testBit_xor m m' 5
  | 2, 2 => exact Nat.testBit_xor m m' 7

theorem slToMat_zero : slToMat 0 = fun _ _ => false := by
  funext i j
  match i, j with
  | 0, 0 | 0, 1 | 0, 2 | 1, 0 | 1, 1 | 1, 2 | 2, 0 | 2, 1 | 2, 2 => rfl

theorem orN_bits {n k : Nat} {b : Nat → Nat} (hb : ∀ i < n, b i < 2) :
    (orN n fun i => b i <<< i).testBit k = (decide (k < n) && (b k).testBit 0) := by
  rw [Bool.eq_iff_iff, orN_testBit]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [Nat.testBit_shiftLeft] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have hki : k - i = 0 := by
      by_contra hne
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hb i hi)
        (Nat.pow_le_pow_right (n := 2) (by omega) (by omega) : 2 ^ 1 ≤ 2 ^ (k - i)))] at h
      exact absurd h.2 (by decide)
    have : i = k := by omega
    subst this
    exact ⟨hi, by simpa using h.2⟩
  · rintro ⟨hk, h⟩
    exact ⟨k, hk, by rw [Nat.testBit_shiftLeft]; simp [h]⟩

theorem rhoK_eq (R : Nat) : rhoK R = orN 9 fun ij => bitN (fget R (ij % 3) 3) (ij / 3) <<< ij :=
  rfl

theorem bitN_lt (X i : Nat) : bitN X i < 2 := by rw [bitN_eq]; split <;> omega

theorem testBit_bitN (X i : Nat) : (bitN X i).testBit 0 = X.testBit i := by
  rw [bitN_eq]; split <;> simp_all

theorem rhoK_packV (r : Lin8) : rhoK (packV r) = encM (rhoMat r) := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [rhoK_eq, orN_bits (fun i _ => bitN_lt _ _), testBit_encM, testBit_bitN]
  by_cases hk : k < 9
  · simp only [hk, decide_true, Bool.true_and]
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    have hk3 : (fin3 (k / 3)).val = k / 3 := Nat.mod_eq_of_lt (by omega)
    rcases this with h | h | h
    · rw [h, fget_packV0, fin3_0]
      change _ = r.1.val.testBit (fin3 (k / 3)).val
      rw [hk3]
    · rw [h, fget_packV1, fin3_1]
      change _ = r.2.1.val.testBit (fin3 (k / 3)).val
      rw [hk3]
    · rw [h, fget_packV2, fin3_2]
      change _ = r.2.2.val.testBit (fin3 (k / 3)).val
      rw [hk3]
  · simp [hk]

theorem bitN_encM (A : M3) (i t : Fin 3) :
    bitN (encM A) (3 * i.val + t.val) = if A i t then 1 else 0 := by
  rw [bitN_eq, testBit_encM']

theorem bmulK_encM (A B : M3) : bmulK (encM A) (encM B) = encM (bmul A B) := by
  have hdef : bmulK (encM A) (encM B) = orN 9 fun ij => xorN 3 (fun k =>
      bitN (encM A) (3 * (ij / 3) + k) &&& bitN (encM B) (3 * k + ij % 3)) <<< ij := rfl
  have hlt : ∀ ij < 9, xorN 3 (fun k =>
      bitN (encM A) (3 * (ij / 3) + k) &&& bitN (encM B) (3 * k + ij % 3)) < 2 :=
    fun ij _ => xorN_lt (w := 1) fun k _ => Nat.and_lt_two_pow _ (bitN_lt _ _)
  apply Nat.eq_of_testBit_eq; intro k
  rw [hdef, orN_bits hlt, testBit_encM]
  by_cases hk : k < 9
  · simp only [hk, decide_true, Bool.true_and]
    have e : ∀ t, t < 3 → bitN (encM A) (3 * (k / 3) + t) =
        if A (fin3 (k / 3)) (fin3 t) then 1 else 0 := by
      intro t ht
      have : 3 * (k / 3) + t = 3 * (fin3 (k / 3)).val + (fin3 t).val := by
        simp [fin3, Nat.mod_eq_of_lt (by omega : k / 3 < 3), Nat.mod_eq_of_lt ht]
      rw [this, bitN_encM]
    have e' : ∀ t, t < 3 → bitN (encM B) (3 * t + k % 3) =
        if B (fin3 t) (fin3 (k % 3)) then 1 else 0 := by
      intro t ht
      have : 3 * t + k % 3 = 3 * (fin3 t).val + (fin3 (k % 3)).val := by
        simp [fin3, Nat.mod_eq_of_lt ht]
      rw [this, bitN_encM]
    simp only [xorN_succ, xorN_zero, Nat.xor_zero]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e' 0 (by omega), e' 1 (by omega),
      e' 2 (by omega), fin3_0, fin3_1, fin3_2]
    simp only [bmul]
    cases A (fin3 (k / 3)) 0 <;> cases A (fin3 (k / 3)) 1 <;> cases A (fin3 (k / 3)) 2 <;>
      cases B 0 (fin3 (k % 3)) <;> cases B 1 (fin3 (k % 3)) <;> cases B 2 (fin3 (k % 3)) <;> rfl
  · simp [hk]

theorem slToMatK_eq : ∀ m < 256, slToMatK m = encM (slToMat m) := by decide +kernel

theorem matToSlK_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    ((if b0 then 1 else 0) ||| (if b1 then 1 else 0) <<< 1 |||
      ((if b2 then 1 else 0) <<< 2 ||| (if b3 then 1 else 0) <<< 3) |||
      ((if b4 then 1 else 0) <<< 4 ||| (if b5 then 1 else 0) <<< 5 |||
        ((if b6 then 1 else 0) <<< 6 ||| (if b7 then 1 else 0) <<< 7))) =
      bitVal b0 0 + bitVal b1 1 + bitVal b2 2 + bitVal b3 3 + bitVal b4 4 + bitVal b5 5 +
        bitVal b6 6 + bitVal b7 7 := by
  decide

theorem matToSlK_encM (A : M3) : matToSlK (encM A) = matToSl A := by
  have e : ∀ (i t : Fin 3), bitN (encM A) (3 * i.val + t.val) = if A i t then 1 else 0 :=
    bitN_encM A
  have e01 := e 0 1; have e02 := e 0 2; have e10 := e 1 0; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e00 := e 0 0; have e22 := e 2 2
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.mul_zero, Nat.zero_add, Nat.mul_one,
    Nat.add_zero] at e01 e02 e10 e12 e20 e21 e00 e22
  simp only [matToSlK, nat_lor_eq, nat_shiftLeft_eq]
  rw [e01, e02, e10, e12, e20, e21, e00, e22, matToSl, matToSlK_bits]

theorem matToSl_lt (A : M3) : matToSl A < 256 := by
  rw [← matToSlK_encM]
  simp only [matToSlK, nat_lor_eq, nat_shiftLeft_eq]
  have h : ∀ X i s, s < 8 → bitN X i <<< s < 2 ^ 8 := fun X i s hs => by
    rw [Nat.shiftLeft_eq]
    calc bitN X i * 2 ^ s < 2 * 2 ^ s :=
          Nat.mul_lt_mul_of_pos_right (bitN_lt _ _) (Nat.two_pow_pos _)
      _ = 2 ^ (s + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      _ ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h0 : ∀ X i, bitN X i < 2 ^ 8 := fun X i => Nat.lt_of_lt_of_le (bitN_lt X i) (by decide)
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (h0 _ _) (h _ _ _ (by omega)))
    (Nat.or_lt_two_pow (h _ _ _ (by omega)) (h _ _ _ (by omega))))
    (Nat.or_lt_two_pow (Nat.or_lt_two_pow (h _ _ _ (by omega)) (h _ _ _ (by omega)))
      (Nat.or_lt_two_pow (h _ _ _ (by omega)) (h _ _ _ (by omega))))

theorem encM_m3One : encM m3One = LINID := by decide +kernel

theorem xAppK_expand (X p q v : Nat) : xAppK X p q v =
    (if (fget v 1 3).testBit 2 then fget X 7 8 else 0) ^^^
    ((if (fget v 0 3).testBit 2 then fget X 6 8 else 0) ^^^
    ((if (fget v 2 3 == q || fget v 2 3 == p ^^^ q) then fget X 5 8 else 0) ^^^
    ((if (fget v 1 3).testBit 1 then fget X 4 8 else 0) ^^^
    ((if (fget v 0 3).testBit 1 then fget X 3 8 else 0) ^^^
    ((if (fget v 2 3 == p || fget v 2 3 == p ^^^ q) then fget X 2 8 else 0) ^^^
    ((if (fget v 1 3).testBit 0 then fget X 1 8 else 0) ^^^
    (if (fget v 0 3).testBit 0 then fget X 0 8 else 0))))))) := by
  simp only [xAppK, xorN_succ, xorN_zero, nIf_eq, bIf_eq, bit_eq, orB_eq, nat_beq_eq,
    nat_mod_eq, nat_div_eq, nat_xor_eq, Nat.xor_zero]
  simp (config := { decide := true }) only [Nat.reduceDiv, ↓reduceIte]

theorem selB_eq (b : Bool) (c : Nat) : selB b c = if b = true then c else 0 := rfl

theorem xAppK_packV {X : Nat} {X' : List Nat} (hX : ∀ k < 8, fget X k 8 = X'.getD k 0)
    (p q : Fin 8) (w : V3) : xAppK X p.val q.val (packV w) = xApply X' p q w := by
  rw [xAppK_expand, fget_packV0, fget_packV1, fget_packV2, xApply, sCoeff]
  simp only [selB_eq, fin_beq_val, fin8_xor_val, hX 0 (by omega), hX 1 (by omega),
    hX 2 (by omega), hX 3 (by omega), hX 4 (by omega), hX 5 (by omega), hX 6 (by omega),
    hX 7 (by omega)]
  xsimp

theorem lam_coeff {p q : Nat} (hc : canonK p q = true) (hp : p < 8) (hq : q < 8) {t : Nat}
    (ht : t < 4) :
    (lamK p q t == p || lamK p q t == p ^^^ q) = t.testBit 0 ∧
      (lamK p q t == q || lamK p q t == p ^^^ q) = t.testBit 1 := by
  rw [canonK_eq] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have t0 : Nat.testBit 0 0 = false := by decide
  have t1 : Nat.testBit 0 1 = false := by decide
  have t2 : Nat.testBit 1 0 = true := by decide
  have t3 : Nat.testBit 1 1 = false := by decide
  have t4 : Nat.testBit 2 0 = false := by decide
  have t5 : Nat.testBit 2 1 = true := by decide
  have t6 : Nat.testBit 3 0 = true := by decide
  have t7 : Nat.testBit 3 1 = true := by decide
  have l0 : lamK p q 0 = 0 := by rw [lamK_eq]; simp [t0, t1]
  have l1 : lamK p q 1 = p := by rw [lamK_eq]; simp [t2, t3]
  have l2 : lamK p q 2 = q := by rw [lamK_eq]; simp [t4, t5]
  have l3 : lamK p q 3 = p ^^^ q := by rw [lamK_eq]; simp [t6, t7]
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  have n1 : (0 == p) = false := by simp; omega
  have n2 : (0 == q) = false := by simp; omega
  have n3 : (0 == p ^^^ q) = false := by simp; omega
  have n4 : (p == q) = false := by simp; omega
  have n5 : (p == p ^^^ q) = false := by simp; omega
  have n6 : (q == p) = false := by simp; omega
  have n7 : (q == p ^^^ q) = false := by simp; omega
  have n8 : (p ^^^ q == p) = false := by simp; omega
  have n9 : (p ^^^ q == q) = false := by simp; omega
  rcases this with rfl | rfl | rfl | rfl
  · rw [l0, t0, t1, n1, n2, n3]; exact ⟨rfl, rfl⟩
  · rw [l1, t2, t3, n4, n5]; simp
  · rw [l2, t4, t5, n6, n7]; simp
  · rw [l3, t6, t7, n8, n9]; simp

theorem xAppK_wK {X p q i : Nat} (hc : canonK p q = true) (hp : p < 8) (hq : q < 8)
    (hi : i < 256) :
    xAppK X p q (wK p q i) = xorN 8 fun k => if i.testBit (abit k) then fget X k 8 else 0 := by
  obtain ⟨c1, c2⟩ := lam_coeff hc hp hq (Nat.mod_lt i (by omega : 0 < 4))
  rw [xAppK_expand, fget_wK0 hp hq hi, fget_wK1 hp hq hi, fget_wK2 hp hq hi, c1, c2]
  have e1 : ∀ t, (i / 32).testBit t = i.testBit (t + 5) := fun t => by
    have e : (32 : Nat) = 2 ^ 5 := rfl
    rw [e, Nat.testBit_div_two_pow]
  have e2 : ∀ t, t < 3 → (i / 4 % 8).testBit t = i.testBit (t + 2) := fun t ht => by
    have e8 : (8 : Nat) = 2 ^ 3 := rfl
    have e4 : (4 : Nat) = 2 ^ 2 := rfl
    rw [e8, Nat.testBit_mod_two_pow, e4, Nat.testBit_div_two_pow]
    simp [ht]
  have e3 : ∀ t, t < 2 → (i % 4).testBit t = i.testBit t := fun t ht => by
    have e4 : (4 : Nat) = 2 ^ 2 := rfl
    rw [e4, Nat.testBit_mod_two_pow]; simp [ht]
  rw [e1, e1, e1, e2 _ (by omega), e2 _ (by omega), e2 _ (by omega), e3 _ (by omega),
    e3 _ (by omega)]
  simp (config := { decide := true }) only [xorN_succ, xorN_zero, Nat.xor_zero, abit, fget_eq]
  rfl

theorem maskAppK_eq {A : Nat} {cols : List Nat} (hA : ∀ k < 8, fget A k 8 = cols.getD k 0)
    (m : Nat) : maskAppK A m = maskApply cols m := by
  simp only [maskAppK, maskApply, sel, xorN_succ, xorN_zero, nIf_eq, bit_eq, Nat.xor_zero]
  rw [hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega), hA 4 (by omega),
    hA 5 (by omega), hA 6 (by omega), hA 7 (by omega)]
  xsimp

theorem maskAppK_xor (A m m' : Nat) : maskAppK A (m ^^^ m') = maskAppK A m ^^^ maskAppK A m' := by
  rw [maskAppK, maskAppK, maskAppK, ← xorN_xor]
  apply xorN_congr; intro k _
  simp only [nIf_eq, bit_eq, Nat.testBit_xor]
  cases m.testBit k <;> cases m'.testBit k <;> simp

theorem maskAppK_zero (A : Nat) : maskAppK A 0 = 0 := by
  rw [maskAppK, xorN_congr (g := fun _ => 0) (fun k _ => by simp [bit_eq]), xorN_zero_fun]

theorem maskAppK_lt (A m : Nat) : maskAppK A m < 256 :=
  xorN_lt (w := 8) fun k _ => by rw [nIf_eq]; split; exact fget_lt _ _ _; exact Nat.two_pow_pos _

theorem adK_field (r i : Lin8) {k : Nat} (hk : k < 8) :
    fget (adK (packV r) (packV i)) k 8 =
      matToSl (bmul (bmul (rhoMat r) (slToMat (2 ^ k))) (rhoMat i)) := by
  have : adK (packV r) (packV i) = orN 8 (fun k => matToSlK (bmulK (bmulK (rhoK (packV r))
      (slToMatK (pw2 k))) (rhoK (packV i))) <<< (8 * k)) := by
    unfold adK; rw [strictN_eq, strictN_eq]; rfl
  have hp : pw2 k < 256 := by rw [pw2_eq]; exact Nat.pow_lt_pow_right (by omega) hk
  rw [this, orN_field (fun j hj => by
      rw [rhoK_packV, rhoK_packV, slToMatK_eq _ (by
        rw [pw2_eq]; exact Nat.pow_lt_pow_right (by omega) hj), bmulK_encM, bmulK_encM,
        matToSlK_encM]
      exact matToSl_lt _) hk]
  rw [rhoK_packV, rhoK_packV, slToMatK_eq _ hp, bmulK_encM, bmulK_encM, matToSlK_encM, pw2_eq]

theorem adMat_getD (r : Lin8) {k : Nat} (hk : k < 8) :
    (adMat r).getD k 0 =
      matToSl (bmul (bmul (rhoMat r) (slToMat (2 ^ k))) (rhoMat (linInv r))) := by
  rw [adMat, List.getD_eq_getElem _ _ (by simp [hk])]
  simp

theorem kS0_spec {SD INV : Nat} (h : kS0 SD INV = true) :
    (∀ d < 7, fget (fget SD d 160) 0 12 = fget SPEC d 12 ∧
      canonK (fget (fget SD d 160) 2 3) (fget (fget SD d 160) 3 3) = true) ∧
    (∀ R < 512, glK R = true → glK (fget INV R 9) = true ∧
      linCompK R (fget INV R 9) = LINID ∧ linCompK (fget INV R 9) R = LINID ∧
      bmulK (rhoK R) (rhoK (fget INV R 9)) = LINID ∧ bmulK (rhoK (fget INV R 9)) (rhoK R) = LINID) ∧
    (∀ m < 256, matToSlK (slToMatK m) = m) ∧
    (∀ R < 512, glK R = true → ∀ k < 8, slToMatK (maskAppK (adK R (fget INV R 9)) (pw2 k)) =
      bmulK (bmulK (rhoK R) (slToMatK (pw2 k))) (rhoK (fget INV R 9))) ∧
    (∀ d < 7,
      (∀ a < 8, xiK (fget SD d 160 >>> 76) (xAppK (fget (fget SD d 160 >>> 12) 0 64)
        (fget (fget SD d 160) 2 3) (fget (fget SD d 160) 3 3)
        (wK (fget (fget SD d 160) 2 3) (fget (fget SD d 160) 3 3) (pw2 a))) =
          wK (fget (fget SD d 160) 2 3) (fget (fget SD d 160) 3 3) (pw2 a)) ∧
      ∀ k < 8, xAppK (fget (fget SD d 160 >>> 12) 0 64) (fget (fget SD d 160) 2 3)
          (fget (fget SD d 160) 3 3) (xiK (fget SD d 160 >>> 76) (pw2 k)) = pw2 k ∧
        lamMemK (fget (fget SD d 160) 2 3) (fget (fget SD d 160) 3 3)
          (fget (xiK (fget SD d 160 >>> 76) (pw2 k)) 2 3) = true) := by
  unfold kS0 at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [allN_iff] at h1
    intro d hd
    have := h1 d hd
    simp only [Bool.and_eq_true, nat_beq_eq, beq_iff_eq] at this
    exact this
  · rw [allN_iff] at h2
    intro R hR hg
    have := h2 R hR
    simp only [orB_eq, notB_eq, hg, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      nat_beq_eq, beq_iff_eq] at this
    exact this
  · rw [allN_iff] at h3
    intro m hm
    have := h3 m hm
    simp only [nat_beq_eq, beq_iff_eq] at this
    exact this
  · rw [allN_iff] at h4
    intro R hR hg
    have := h4 R hR
    simp only [orB_eq, notB_eq, hg, Bool.not_true, Bool.false_or, strictN_eq, rec01_eq_one]
      at this
    simp only [allN_iff, nat_beq_eq, beq_iff_eq] at this
    exact this
  · rw [allN_iff] at h5
    intro d hd
    have := h5 d hd
    simp only [Bool.and_eq_true, allN_iff, nat_beq_eq, beq_iff_eq, nat_shiftRight_eq] at this
    exact this

theorem inv_spec {INV : Nat} (h2 : ∀ R < 512, glK R = true → glK (fget INV R 9) = true ∧
      linCompK R (fget INV R 9) = LINID ∧ linCompK (fget INV R 9) R = LINID ∧
      bmulK (rhoK R) (rhoK (fget INV R 9)) = LINID ∧ bmulK (rhoK (fget INV R 9)) (rhoK R) = LINID)
    {r : Lin8} (hr : r ∈ glList) :
    ∃ i : Lin8, packV i = fget INV (packV r) 9 ∧ i ∈ glList ∧ linComp r i = linId ∧
      linComp i r = linId ∧ encM (bmul (rhoMat r) (rhoMat i)) = encM m3One ∧
      encM (bmul (rhoMat i) (rhoMat r)) = encM m3One ∧ linInv r = i := by
  have hg : glK (packV r) = true := by rw [glK_packV]; exact (mem_glList r).mp hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := h2 _ (packV_lt r) hg
  have hI : packV (unpackV (fget INV (packV r) 9)) = fget INV (packV r) 9 :=
    packV_unpackV (fget_lt _ _ 9)
  generalize unpackV (fget INV (packV r) 9) = i at hI
  rw [← hI] at g1 g2 g3 g4 g5
  have hi : i ∈ glList := by rw [mem_glList, ← glK_packV]; exact g1
  have e1 : linComp r i = linId := packV_inj (by rw [packV_linComp, g2, LINID_eq])
  have e2 : linComp i r = linId := packV_inj (by rw [packV_linComp, g3, LINID_eq])
  rw [rhoK_packV, rhoK_packV, bmulK_encM, ← encM_m3One] at g4 g5
  exact ⟨i, hI, hi, e1, e2, g4, g5, linInv_eq hi e1 e2⟩

theorem xiK_xor (XI m m' : Nat) : xiK XI (m ^^^ m') = xiK XI m ^^^ xiK XI m' := by
  rw [xiK, xiK, xiK, ← xorN_xor]
  apply xorN_congr; intro k _
  simp only [nIf_eq, bit_eq, Nat.testBit_xor]
  cases m.testBit k <;> cases m'.testBit k <;> simp

theorem xiK_zero (XI : Nat) : xiK XI 0 = 0 := by
  rw [xiK, xorN_congr (g := fun _ => 0) (fun k _ => by simp [bit_eq]), xorN_zero_fun]

theorem xiK_lt (XI m : Nat) : xiK XI m < 512 :=
  xorN_lt (w := 9) fun k _ => by rw [nIf_eq]; split; exact fget_lt _ _ _; exact Nat.two_pow_pos _

theorem xiK_pow (XI : Nat) {j : Nat} (hj : j < 8) : xiK XI (2 ^ j) = fget XI j 9 := by
  rw [xiK, xorN_single (b := j) (fun i hi => by
    rw [nIf_eq, bit_eq, Nat.testBit_two_pow]; simp [Ne.symm hi])]
  simp [hj, bit_eq]

theorem xW_xor {X p q i j : Nat} (hc : canonK p q = true) (hp : p < 8) (hq : q < 8) (hi : i < 256)
    (hj : j < 256) :
    xAppK X p q (wK p q (i ^^^ j)) = xAppK X p q (wK p q i) ^^^ xAppK X p q (wK p q j) := by
  rw [xAppK_wK hc hp hq (xor_lt256 hi hj), xAppK_wK hc hp hq hi, xAppK_wK hc hp hq hj, ← xorN_xor]
  apply xorN_congr; intro k _
  rw [Nat.testBit_xor]
  cases i.testBit (abit k) <;> cases j.testBit (abit k) <;> simp

theorem xW_zero {X p q : Nat} (hc : canonK p q = true) (hp : p < 8) (hq : q < 8) :
    xAppK X p q (wK p q 0) = 0 := by
  rw [xAppK_wK hc hp hq (by omega), xorN_congr (g := fun _ => 0) (fun k _ => by simp),
    xorN_zero_fun]

theorem xW_lt {X p q i : Nat} (hc : canonK p q = true) (hp : p < 8) (hq : q < 8) (hi : i < 256) :
    xAppK X p q (wK p q i) < 256 := by
  rw [xAppK_wK hc hp hq hi]
  exact xorN_lt (w := 8) fun k _ => by split; exact fget_lt _ _ _; exact Nat.two_pow_pos _

theorem wK_xor {p q i j : Nat} (hp : p < 8) (hq : q < 8) (hi : i < 256) (hj : j < 256) :
    wK p q (i ^^^ j) = wK p q i ^^^ wK p q j := by
  have hij := xor_lt256 hi hj
  apply eq_of_fget3 (wK_lt hp hq hij)
    (Nat.xor_lt_two_pow (n := 9) (wK_lt hp hq hi) (wK_lt hp hq hj))
  · rw [fget_xor, fget_wK0 hp hq hi, fget_wK0 hp hq hj, fget_wK0 hp hq hij]
    exact Nat.xor_div_two_pow (n := 5)
  · rw [fget_xor, fget_wK1 hp hq hi, fget_wK1 hp hq hj, fget_wK1 hp hq hij,
      Nat.xor_div_two_pow (n := 2)]
    exact Nat.xor_mod_two_pow (n := 3)
  · rw [fget_xor, fget_wK2 hp hq hi, fget_wK2 hp hq hj, fget_wK2 hp hq hij,
      Nat.xor_mod_two_pow (n := 2), lamK_xor]

theorem wK_zero {p q : Nat} : wK p q 0 = 0 := by
  rw [wK_eq (by omega)]; simp [lamK_eq]

theorem lamMemK_iff (p q s : Nat) :
    lamMemK p q s = true ↔ s = 0 ∨ s = p ∨ s = q ∨ s = p ^^^ q := by
  simp [lamMemK, orB_eq, nat_beq_eq]

theorem lamMemK_xor {p q s s' : Nat} (h : lamMemK p q s = true) (h' : lamMemK p q s' = true) :
    lamMemK p q (s ^^^ s') = true := by
  rw [lamMemK_iff] at h h' ⊢
  rcases h with rfl | rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl | rfl <;> xsimp <;>
    simp

theorem exists_wK {p q v : Nat} (hp : p < 8) (hq : q < 8) (hv : v < 512)
    (hs : lamMemK p q (fget v 2 3) = true) : ∃ J < 256, wK p q J = v := by
  have key : ∃ t < 4, lamK p q t = fget v 2 3 := by
    rw [lamMemK_iff] at hs
    rcases hs with h | h | h | h
    · exact ⟨0, by omega, by rw [lamK_eq, h]; simp [(by decide : Nat.testBit 0 0 = false),
        (by decide : Nat.testBit 0 1 = false)]⟩
    · exact ⟨1, by omega, by rw [lamK_eq, h]; simp [(by decide : Nat.testBit 1 0 = true),
        (by decide : Nat.testBit 1 1 = false)]⟩
    · exact ⟨2, by omega, by rw [lamK_eq, h]; simp [(by decide : Nat.testBit 2 0 = false),
        (by decide : Nat.testBit 2 1 = true)]⟩
    · exact ⟨3, by omega, by rw [lamK_eq, h]; simp [(by decide : Nat.testBit 3 0 = true),
        (by decide : Nat.testBit 3 1 = true)]⟩
  obtain ⟨t, ht, hts⟩ := key
  have h0 := fget3_lt v 0; have h1 := fget3_lt v 1
  have hJ : 32 * fget v 0 3 + 4 * fget v 1 3 + t < 256 := by omega
  refine ⟨_, hJ, eq_of_fget3 (wK_lt hp hq hJ) hv ?_ ?_ ?_⟩
  · rw [fget_wK0 hp hq hJ]; omega
  · rw [fget_wK1 hp hq hJ]; omega
  · rw [fget_wK2 hp hq hJ, ← hts]; congr 1; omega

theorem filter_length_eq (n : Nat) (P : Nat → Bool) :
    ((List.range n).filter P).length = sumN n (fun m => if P m then 1 else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, sumN_succ]
    cases h : P n <;> simp [h, Nat.add_comm]

theorem xorN_closed {P : Nat → Prop} (h0 : P 0) (hx : ∀ a b, P a → P b → P (a ^^^ b))
    {n : Nat} {f : Nat → Nat} (hf : ∀ i < n, P (f i)) : P (xorN n f) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [xorN_succ]
    exact hx _ _ (hf n (by omega)) (ih fun i hi => hf i (by omega))

theorem sdRec_spec' {d : (Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3} {R : Nat}
    (h : sdRecOK d R = true) :
    pack4 d.1 = fget R 0 12 ∧ d.2.1.length = 8 ∧
      (∀ k (hk : k < d.2.1.length), d.2.1[k] = fget (R >>> 12) k 8) ∧
      (∀ n ∈ d.2.1, n < 256) ∧ d.2.2.length = 8 ∧
      ∀ k (hk : k < d.2.2.length), packV d.2.2[k] = fget (R >>> 76) k 9 := by
  obtain ⟨t, X, Xi⟩ := d
  exact sdRec_spec h

theorem adConj {INV : Nat} (h2 : ∀ R < 512, glK R = true → glK (fget INV R 9) = true ∧
      linCompK R (fget INV R 9) = LINID ∧ linCompK (fget INV R 9) R = LINID ∧
      bmulK (rhoK R) (rhoK (fget INV R 9)) = LINID ∧ bmulK (rhoK (fget INV R 9)) (rhoK R) = LINID)
    (h4 : ∀ R < 512, glK R = true → ∀ k < 8, slToMatK (maskAppK (adK R (fget INV R 9)) (pw2 k)) =
      bmulK (bmulK (rhoK R) (slToMatK (pw2 k))) (rhoK (fget INV R 9)))
    {r : Lin8} (hr : r ∈ glList) {m : Nat} (hm : m < 256) :
    encM (slToMat (maskApply (adMat r) m)) =
      encM (bmul (bmul (rhoMat r) (slToMat m)) (rhoMat (linInv r))) := by
  obtain ⟨i, hI, hi, -, -, -, -, hinv⟩ := inv_spec h2 hr
  have hg : glK (packV r) = true := by rw [glK_packV]; exact (mem_glList r).mp hr
  have hA : ∀ k < 8, fget (adK (packV r) (packV i)) k 8 = (adMat r).getD k 0 := by
    intro k hk; rw [adK_field r i hk, adMat_getD r hk, hinv]
  rw [← maskAppK_eq hA, hinv]
  have hF := decomp (N := 8) (f := fun m => encM (slToMat (maskAppK (adK (packV r) (packV i)) m)))
    (by simp only [maskAppK_zero, slToMat_zero, encM_zero])
    (fun a b _ _ => by simp only [maskAppK_xor, slToMat_xor, encM_madd]) (by omega : m < 2 ^ 8)
  have hG := decomp (N := 8) (f := fun m => encM (bmul (bmul (rhoMat r) (slToMat m)) (rhoMat i)))
    (by simp only [slToMat_zero, bmul_zero_right, bmul_zero_left, encM_zero])
    (fun a b _ _ => by simp only [slToMat_xor, bmul_madd_right, bmul_madd_left, encM_madd])
    (by omega : m < 2 ^ 8)
  rw [hF, hG]
  apply xorN_congr; intro k hk
  congr 1
  have h4k := h4 _ (packV_lt r) hg k hk
  have hpk : pw2 k < 256 := by rw [pw2_eq]; exact Nat.pow_lt_pow_right (by omega) hk
  rw [← hI, slToMatK_eq _ (maskAppK_lt _ _), slToMatK_eq _ hpk, rhoK_packV, rhoK_packV,
    bmulK_encM, bmulK_encM, pw2_eq] at h4k
  exact h4k

theorem stein_spec {p q : Fin 8} {X' : List Nat} {Xi : List V3} {X XI : Nat}
    (hc : canonK p.val q.val = true) (hX : ∀ k < 8, fget X k 8 = X'.getD k 0)
    (hXl : Xi.length = 8) (hXi : ∀ k (hk : k < Xi.length), packV Xi[k] = fget XI k 9)
    (hB1 : ∀ a < 8, xiK XI (xAppK X p.val q.val (wK p.val q.val (pw2 a))) = wK p.val q.val (pw2 a))
    (hB2 : ∀ k < 8, xAppK X p.val q.val (xiK XI (pw2 k)) = pw2 k ∧
      lamMemK p.val q.val (fget (xiK XI (pw2 k)) 2 3) = true) :
    (((wList p q).all fun w => xiApply Xi (xApply X' p q w) == w) &&
      (all256.all fun m => xApply X' p q (xiApply Xi m) == m &&
        (lamList p q).contains (xiApply Xi m).2.2)) = true := by
  have hp := p.isLt; have hq := q.isLt
  rw [Bool.and_eq_true]
  have hlam : ∀ m, lamMemK p.val q.val (fget (xiK XI m) 2 3) = true := by
    intro m
    have hm : fget (xiK XI m) 2 3 =
        xorN 8 (fun j => if m.testBit j then fget (fget XI j 9) 2 3 else 0) := by
      unfold xiK
      rw [xorN_map (fun X => fget X 2 3) (fget_zero 2 3) (fun a b => fget_xor a b 2 3)]
      apply xorN_congr; intro j hj
      rw [nIf_eq, bit_eq]
      by_cases hb : m.testBit j <;> simp [hb, fget_zero]
    rw [hm]
    refine xorN_closed (P := fun s => lamMemK p.val q.val s = true) (by simp [lamMemK_iff])
      (fun a b ha hb => lamMemK_xor ha hb) fun j hj => ?_
    split
    · have := (hB2 j hj).2; rwa [pw2_eq, xiK_pow XI hj] at this
    · simp [lamMemK_iff]
  constructor
  · rw [List.all_eq_true]
    intro w hw
    obtain ⟨i, hi, rfl⟩ := exists_wPt hw
    rw [beq_iff_eq]
    apply packV_inj
    rw [← xiK_eq hXl hXi, ← xAppK_packV hX, packV_wPt p q hi]
    have hF := decomp (N := 8) (f := fun i => xiK XI (xAppK X p.val q.val (wK p.val q.val i)))
      (by simp only [xW_zero hc hp hq, xiK_zero])
      (fun a b ha hb => by simp only [xW_xor hc hp hq ha hb, xiK_xor]) (by omega : i < 2 ^ 8)
    have hW := decomp (N := 8) (f := fun i => wK p.val q.val i) wK_zero
      (fun a b ha hb => wK_xor hp hq ha hb) (by omega : i < 2 ^ 8)
    rw [hF, hW]
    apply xorN_congr; intro a ha
    have := hB1 a ha
    rw [pw2_eq] at this
    rw [this]
  · rw [List.all_eq_true]
    intro m hm
    rw [all256, List.mem_range] at hm
    rw [Bool.and_eq_true, beq_iff_eq]
    have hpack : packV (xiApply Xi m) = xiK XI m := (xiK_eq hXl hXi m).symm
    constructor
    · rw [← xAppK_packV hX, hpack]
      have hJ : ∀ m, ∃ J < 256, wK p.val q.val J = xiK XI m :=
        fun m => exists_wK hp hq (xiK_lt XI m) (hlam m)
      have hadd : ∀ a b, xAppK X p.val q.val (xiK XI (a ^^^ b)) =
          xAppK X p.val q.val (xiK XI a) ^^^ xAppK X p.val q.val (xiK XI b) := by
        intro a b
        obtain ⟨Ja, hJa, ea⟩ := hJ a
        obtain ⟨Jb, hJb, eb⟩ := hJ b
        rw [xiK_xor, ← ea, ← eb, ← wK_xor hp hq hJa hJb, xW_xor hc hp hq hJa hJb]
      have hG := decomp (N := 8) (f := fun m => xAppK X p.val q.val (xiK XI m))
        (by
          rw [xiK_zero]
          have := xW_zero (X := X) hc hp hq
          rwa [wK_zero] at this)
        (fun a b _ _ => hadd a b) (by omega : m < 2 ^ 8)
      rw [hG]
      conv_rhs => rw [← Nat.mod_eq_of_lt (by omega : m < 2 ^ 8), ← xorN_bits m 8]
      apply xorN_congr; intro k hk
      have := (hB2 k hk).1
      rw [pw2_eq] at this
      rw [this]
    · rw [List.contains_iff_mem]
      have h2 := hlam m
      rw [← hpack, fget_packV2, lamMemK_iff] at h2
      simp only [lamList, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, fin8_xor_val]
      exact h2

theorem rec_data {sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3)} {SD : Nat}
    (hS : bindSD sd SD = true) {k : Nat} (hk : k < sd.length) :
    pack4 sd[k].1 = fget (fget SD k 160) 0 12 ∧
      fget (fget SD k 160) 0 3 = sd[k].1.1.val ∧ fget (fget SD k 160) 1 3 = sd[k].1.2.1.val ∧
      fget (fget SD k 160) 2 3 = sd[k].1.2.2.1.val ∧ fget (fget SD k 160) 3 3 = sd[k].1.2.2.2.val ∧
      (∀ j < 8, fget (fget (fget SD k 160 >>> 12) 0 64) j 8 = sd[k].2.1.getD j 0) ∧
      sd[k].2.2.length = 8 ∧
      ∀ j (hj : j < sd[k].2.2.length), packV sd[k].2.2[j] = fget (fget SD k 160 >>> 76) j 9 := by
  obtain ⟨-, hsk⟩ := bindSD_spec hS
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := sdRec_spec' (hsk k hk)
  obtain ⟨f0, f1, f2, f3⟩ := fget_rec h1
  refine ⟨h1, f0, f1, f2, f3, fun j hj => ?_, h5, h6⟩
  have e64 : (64 : Nat) = 8 * 8 := rfl
  rw [e64, fget_fget_mul hj, Nat.mul_zero, Nat.zero_add,
    List.getD_eq_getElem _ _ (by omega), h3 j (by omega)]

theorem s0Check_of {sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3)}
    {sl : List (Fin 8 × Fin 8 × Fin 8 × Fin 8)} {SD INV : Nat} (hS : bindSD sd SD = true)
    (hSp : bindSpec sl = true) (h0 : kS0 SD INV = true) : Gen.s0Check sd sl = true := by
  obtain ⟨P1, P2, P3, P4, P5⟩ := kS0_spec h0
  obtain ⟨hsl, -⟩ := bindSD_spec hS
  obtain ⟨hpl, hpk⟩ := bindList_iff hSp
  unfold Gen.s0Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    apply List.ext_getElem (by simp only [List.length_map]; lomega)
    intro k h1 h2
    rw [List.getElem_map]
    have hk : k < sd.length := by simpa using h1
    apply pack4_inj
    rw [(rec_data hS hk).1, (P1 k (by lomega)).1, hpk k h2]
  · rw [List.all_eq_true]
    intro r hr
    obtain ⟨i, -, -, e1, e2, e3, e4, hinv⟩ := inv_spec P2 hr
    rw [hinv]
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨e1, e2⟩, m3Eq_of e3⟩, m3Eq_of e4⟩
  · rw [List.all_eq_true]
    intro m hm
    rw [all256, List.mem_range] at hm
    rw [beq_iff_eq, ← matToSlK_encM, ← slToMatK_eq m hm]
    exact P3 m hm
  · rw [List.all_eq_true]
    intro r hr
    rw [List.all_eq_true]
    intro m hm
    rw [all256, List.mem_range] at hm
    exact m3Eq_of (adConj P2 P4 hr hm)
  · rw [List.all_eq_true]
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hd
    obtain ⟨-, -, -, f2, f3, hX, hXl, hXi⟩ := rec_data hS hk
    obtain ⟨-, hcan⟩ := P1 k (by lomega)
    obtain ⟨hB1, hB2⟩ := P5 k (by lomega)
    rw [f2, f3] at hcan hB1 hB2
    exact stein_spec hcan hX hXl hXi hB1 hB2

theorem quad_eq {Q₁ Q₂ : Nat → Nat} {B₁ B₂ : Nat → Nat → Nat}
    (hQ₁ : ∀ i j, i < 256 → j < 256 → Q₁ (i ^^^ j) = Q₁ i ^^^ Q₁ j ^^^ B₁ i j)
    (hQ₂ : ∀ i j, i < 256 → j < 256 → Q₂ (i ^^^ j) = Q₂ i ^^^ Q₂ j ^^^ B₂ i j)
    (hB₁ : ∀ i j k, i < 256 → j < 256 → B₁ (i ^^^ j) k = B₁ i k ^^^ B₁ j k)
    (hB₁' : ∀ i j k, i < 256 → j < 256 → B₁ k (i ^^^ j) = B₁ k i ^^^ B₁ k j)
    (hB₂ : ∀ i j k, i < 256 → j < 256 → B₂ (i ^^^ j) k = B₂ i k ^^^ B₂ j k)
    (hB₂' : ∀ i j k, i < 256 → j < 256 → B₂ k (i ^^^ j) = B₂ k i ^^^ B₂ k j)
    (h0₁ : ∀ k, B₁ 0 k = 0) (h0₁' : ∀ k, B₁ k 0 = 0) (h0₂ : ∀ k, B₂ 0 k = 0)
    (h0₂' : ∀ k, B₂ k 0 = 0)
    (h0 : Q₁ 0 = Q₂ 0) (hpow : ∀ a < 8, Q₁ (2 ^ a) = Q₂ (2 ^ a))
    (hpair : ∀ a < 8, ∀ b < a, Q₁ (2 ^ a ^^^ 2 ^ b) = Q₂ (2 ^ a ^^^ 2 ^ b)) :
    ∀ x < 256, Q₁ x = Q₂ x := by
  have hp : ∀ a < 8, 2 ^ a < 256 := fun a ha => Nat.pow_lt_pow_right (by omega) ha
  have hH : ∀ i j, i < 256 → j < 256 → Q₁ (i ^^^ j) ^^^ Q₂ (i ^^^ j) =
      (Q₁ i ^^^ Q₂ i) ^^^ (Q₁ j ^^^ Q₂ j) ^^^ (B₁ i j ^^^ B₂ i j) := by
    intro i j hi hj; rw [hQ₁ i j hi hj, hQ₂ i j hi hj]; xsimp
  have hβ0 : ∀ a < 8, ∀ b < 8, B₁ (2 ^ a) (2 ^ b) ^^^ B₂ (2 ^ a) (2 ^ b) = 0 := by
    intro a ha b hb
    have e := hH _ _ (hp a ha) (hp b hb)
    rw [hpow a ha, hpow b hb, Nat.xor_self, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at e
    rcases Nat.lt_trichotomy b a with h | h | h
    · rw [hpair a ha b h, Nat.xor_self] at e; exact e.symm
    · subst h
      rw [Nat.xor_self, h0, Nat.xor_self] at e; exact e.symm
    · rw [Nat.xor_comm (2 ^ a), hpair b hb a h, Nat.xor_self] at e; exact e.symm
  have hβ : ∀ x < 256, ∀ y < 256, B₁ x y ^^^ B₂ x y = 0 := by
    intro x hx y hy
    have hx' := decomp (N := 8) (f := fun x => B₁ x y ^^^ B₂ x y)
      (by simp only [h0₁, h0₂, Nat.xor_self])
      (fun u v hu hv => by rw [hB₁ u v y hu hv, hB₂ u v y hu hv]; xsimp)
      (by omega : x < 2 ^ 8)
    rw [hx', xorN_congr (g := fun _ => 0) (fun a ha => ?_), xorN_zero_fun]
    split
    · have hy' := decomp (N := 8) (f := fun y => B₁ (2 ^ a) y ^^^ B₂ (2 ^ a) y)
        (by simp only [h0₁', h0₂', Nat.xor_self])
        (fun u v hu hv => by rw [hB₁' u v _ hu hv, hB₂' u v _ hu hv]; xsimp)
        (by omega : y < 2 ^ 8)
      rw [hy', xorN_congr (g := fun _ => 0) (fun b hb => by
        split
        · exact hβ0 a ha b hb
        · rfl), xorN_zero_fun]
    · rfl
  intro x hx
  have hx' := decomp (N := 8) (f := fun x => Q₁ x ^^^ Q₂ x) (by rw [h0, Nat.xor_self])
    (fun u v hu hv => by rw [hH u v hu hv, hβ u hu v hv, Nat.xor_zero])
    (by omega : x < 2 ^ 8)
  rw [xorN_congr (g := fun _ => 0) (fun a ha => by
    split
    · rw [hpow a ha, Nat.xor_self]
    · rfl), xorN_zero_fun] at hx'
  exact eq_of_xor_eq_zero hx'

theorem or_pow_eq_xor {a b : Nat} (h : b < a) : 2 ^ a ||| 2 ^ b = 2 ^ a ^^^ 2 ^ b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
  by_cases h1 : a = i
  · subst h1; simp [Nat.ne_of_lt h]
  · simp [h1]

theorem kS1_spec {INV Rd : Nat} (h : kS1 INV Rd = true) : ∀ R < 512, glK R = true →
    ∀ a < 8, ∀ b < a + 1,
      sqK (fget Rd 0 3) (fget Rd 1 3) (xiK (Rd >>> 76) (maskAppK (adK R (fget INV R 9))
        (xAppK (fget (Rd >>> 12) 0 64) (fget Rd 2 3) (fget Rd 3 3)
          (wK (fget Rd 2 3) (fget Rd 3 3) (2 ^ a ||| 2 ^ b))))) =
      linAppK R (sqK (fget Rd 0 3) (fget Rd 1 3)
        (wK (fget Rd 2 3) (fget Rd 3 3) (2 ^ a ||| 2 ^ b))) := by
  unfold kS1 at h
  rw [allN_iff] at h
  intro R hR hg a ha b hb
  have := h R hR
  simp only [orB_eq, notB_eq, hg, Bool.not_true, Bool.false_or, strictN_eq, rec01_eq_one] at this
  simp only [allN_iff, nat_beq_eq, beq_iff_eq, nat_lor_eq, pw2_eq, nat_shiftRight_eq] at this
  exact this a ha b hb

theorem s1Check_of {mt : Array (Fin 8)}
    {sd : List ((Fin 8 × Fin 8 × Fin 8 × Fin 8) × List Nat × List V3)} {SD INV : Nat}
    (hM : bindMul mt = true) (hMul : mulOK = true) (hS : bindSD sd SD = true)
    (h0 : kS0 SD INV = true) (h1 : ∀ d < 7, kS1 INV (fget SD d 160) = true) :
    Gen.s1Check mt sd = true := by
  have L := mulLaws_of hMul
  obtain ⟨P1, P2, -, -, -⟩ := kS0_spec h0
  obtain ⟨hsl, -⟩ := bindSD_spec hS
  unfold Gen.s1Check
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hd
  obtain ⟨-, f0, f1, f2, f3, hX, hXl, hXi⟩ := rec_data hS hk
  obtain ⟨-, hcan⟩ := P1 k (by lomega)
  have hK := kS1_spec (h1 k (by lomega))
  generalize sd[k] = d at f0 f1 f2 f3 hX hXl hXi ⊢
  obtain ⟨⟨c, e, p, q⟩, X', Xi⟩ := d
  simp only at f0 f1 f2 f3 hX hXl hXi ⊢
  rw [f2, f3] at hcan
  rw [f0, f1, f2, f3] at hK
  generalize fget (fget SD k 160 >>> 12) 0 64 = X at hX hK
  generalize fget SD k 160 >>> 76 = XI at hXi hK
  have hp := p.isLt; have hq := q.isLt
  have P : Par c.val e.val p.val q.val := ⟨c.isLt, e.isLt, hp, hq, L⟩
  rw [List.all_eq_true]
  intro r hr
  obtain ⟨i, hI, -, -, -, -, -, hinv⟩ := inv_spec P2 hr
  have hg : glK (packV r) = true := by rw [glK_packV]; exact (mem_glList r).mp hr
  have hA : ∀ k < 8, fget (adK (packV r) (packV i)) k 8 = (adMat r).getD k 0 := by
    intro k hk; rw [adK_field r i hk, adMat_getD r hk, hinv]
  have hK' := hK _ (packV_lt r) hg
  rw [← hI] at hK'
  let A := adK (packV r) (packV i)
  let M : Nat → Nat := fun j => xiK XI (maskAppK A (xAppK X p.val q.val (wK p.val q.val j)))
  have hMx : ∀ u v, u < 256 → v < 256 → M (u ^^^ v) = M u ^^^ M v := by
    intro u v hu hv
    simp only [M, xW_xor hcan hp hq hu hv, maskAppK_xor, xiK_xor]
  have hM0 : M 0 = 0 := by simp only [M, xW_zero hcan hp hq, maskAppK_zero, xiK_zero]
  have key := quad_eq (Q₁ := fun j => sqK c.val e.val (M j))
    (Q₂ := fun j => linAppK (packV r) (Qi c.val e.val p.val q.val j))
    (B₁ := fun u v => commK c.val (M u) (M v))
    (B₂ := fun u v => linAppK (packV r) (Bi c.val p.val q.val u v))
    (fun u v hu hv => by rw [hMx u v hu hv, L.sqK_xor c.isLt e.isLt])
    (fun u v hu hv => by rw [P.Qi_xor hu hv, linAppK_xor, linAppK_xor])
    (fun u v w hu hv => by rw [hMx u v hu hv, L.commK_xor c.isLt])
    (fun u v w hu hv => by rw [hMx u v hu hv, L.commK_xor_right c.isLt])
    (fun u v w hu hv => by rw [P.Bi_xor_left hu hv, linAppK_xor])
    (fun u v w hu hv => by rw [P.Bi_xor_right hu hv, linAppK_xor])
    (fun w => by rw [hM0, L.commK_zero c.isLt])
    (fun w => by rw [hM0, L.commK_symm, L.commK_zero c.isLt])
    (fun w => by rw [P.Bi_zero_left, linAppK_zero])
    (fun w => by rw [P.Bi_zero_right, linAppK_zero])
    (by rw [hM0, L.sqK_zero c.isLt e.isLt, P.Qi_zero, linAppK_zero])
    (fun a ha => by
      have := hK' a ha a (by omega)
      rw [Nat.or_self] at this
      exact this)
    (fun a ha b hb => by
      have := hK' a ha b (by omega)
      rw [or_pow_eq_xor hb] at this
      exact this)
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨j, hj, rfl⟩ := exists_wPt hw
  rw [beq_iff_eq, Fin.ext_iff, sqN_packV hM, linApply_val, sqN_packV hM, ← xiK_eq hXl hXi,
    ← maskAppK_eq hA, ← xAppK_packV hX, packV_wPt p q hj]
  exact key j hj

theorem packV_beq (x y : V3) : (packV x == packV y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨packV_inj, fun h => h ▸ rfl⟩

theorem invoK_packV (r : Lin8) :
    invoK (packV r) = (indep3 r.1 r.2.1 r.2.2 && r != linId && linComp r r == linId) := by
  rw [invoK, andB_eq, andB_eq, notB_eq, glK_packV, nat_beq_eq, nat_beq_eq, LINID_eq, packV_beq,
    ← packV_linComp, packV_beq, bne, Bool.and_assoc]

theorem fourK_packV (r₁ r₂ : Lin8) :
    fourK (packV r₁) (packV r₂) = (!(r₁ == r₂) && (linComp r₁ r₂ == linComp r₂ r₁)) := by
  rw [fourK, andB_eq, notB_eq, nat_beq_eq, nat_beq_eq, packV_beq, ← packV_linComp,
    ← packV_linComp, packV_beq]

theorem invlOK_spec {INVL : Nat} (h : invlOK INVL = true) {R : Nat} (hR : R < 512)
    (hi : invoK R = true) : ∃ i < 21, fget INVL i 9 = R := by
  unfold invlOK at h
  rw [allN_iff] at h
  have := h R hR
  rw [rec01_beq, beq_iff_eq, hi] at this
  obtain ⟨i, hi', h'⟩ := anyN_iff.mp this.symm
  rw [nat_beq_eq, beq_iff_eq] at h'
  exact ⟨i, hi', h'⟩

theorem invListOK_mem {il : List Lin8} (hil : Gen.invListOK il = true) {r : Lin8} (hr : r ∈ il) :
    r ∈ glList ∧ invoK (packV r) = true := by
  unfold Gen.invListOK at hil
  simp only [Bool.and_eq_true, List.all_eq_true] at hil
  have := hil.2 r hr
  refine ⟨(mem_glList r).mpr this.1.1, ?_⟩
  rw [invoK_packV]
  simp only [Bool.and_eq_true]
  exact this

theorem rec01_eq_iff (b : Bool) : (Bool.rec (motive := fun _ => Nat) 0 1 b = 1) ↔ b = true := by
  cases b <;> simp

theorem s2aCheck_of {SD INV INVL : Nat} {il : List Lin8} (h0 : kS0 SD INV = true)
    (h2a : kS2a INV INVL = true) (hil : Gen.invListOK il = true) : Gen.s2aCheckG il = true := by
  obtain ⟨-, P2, -, -, -⟩ := kS0_spec h0
  unfold kS2a at h2a
  rw [andB_eq, Bool.and_eq_true] at h2a
  obtain ⟨hinvl, hall⟩ := h2a
  unfold Gen.s2aCheckG
  rw [List.all_eq_true]; intro r₁ hr₁
  rw [List.all_eq_true]; intro r₂ hr₂
  obtain ⟨hg₁, hv₁⟩ := invListOK_mem hil hr₁
  obtain ⟨hg₂, hv₂⟩ := invListOK_mem hil hr₂
  obtain ⟨i₁, hi₁, e₁⟩ := invlOK_spec hinvl (packV_lt r₁) hv₁
  obtain ⟨i₂, hi₂, e₂⟩ := invlOK_spec hinvl (packV_lt r₂) hv₂
  rw [allN_iff] at hall
  have h12 := hall i₁ hi₁
  rw [allN_iff] at h12
  have h := h12 i₂ hi₂
  rw [e₁, e₂] at h
  beta_reduce at h
  rw [orB_eq, notB_eq, fourK_packV] at h
  rw [Bool.or_eq_true, Bool.or_eq_true]
  by_cases hc : (r₁ == r₂) = true ∨ (linComp r₁ r₂ != linComp r₂ r₁) = true
  · exact Or.inl hc
  right
  have hc1 : (r₁ == r₂) = false := by simpa using (not_or.mp hc).1
  have hc2 : (linComp r₁ r₂ == linComp r₂ r₁) = true := by
    have := (not_or.mp hc).2; simpa [bne] using this
  rw [hc1, hc2] at h
  simp only [Bool.not_false, Bool.true_and, Bool.not_true, Bool.false_or] at h
  rw [nat_beq_eq, beq_iff_eq, strictN_eq, strictN_eq, rec01_eq_iff, nat_ble_eq,
    decide_eq_true_eq] at h
  obtain ⟨j₁, hI₁, -, -, -, -, -, hinv₁⟩ := inv_spec P2 hg₁
  obtain ⟨j₂, hI₂, -, -, -, -, -, hinv₂⟩ := inv_spec P2 hg₂
  have hA₁ : ∀ k < 8, fget (adK (packV r₁) (packV j₁)) k 8 = (adMat r₁).getD k 0 := by
    intro k hk; rw [adK_field r₁ j₁ hk, adMat_getD r₁ hk, hinv₁]
  have hA₂ : ∀ k < 8, fget (adK (packV r₂) (packV j₂)) k 8 = (adMat r₂).getD k 0 := by
    intro k hk; rw [adK_field r₂ j₂ hk, adMat_getD r₂ hk, hinv₂]
  rw [← hI₁, ← hI₂] at h
  simp only [maskAppK_eq hA₁, maskAppK_eq hA₂] at h
  rw [decide_eq_true_eq, all256, filter_length_eq]
  refine Nat.le_trans (Nat.le_of_eq (sumN_congr fun m _ => ?_)) h
  simp only [andB_eq, nat_beq_eq, nIf_eq]

theorem s2bCheck_of {INVL : Nat} {il gl : List Lin8} (h2b : kS2b INVL = true)
    (hil : Gen.invListOK il = true) (hgl : Gen.glOK gl = true) : Gen.s2bCheckG il gl = true := by
  unfold kS2b at h2b
  rw [andB_eq, Bool.and_eq_true] at h2b
  obtain ⟨hinvl, hall⟩ := h2b
  unfold Gen.s2bCheckG
  rw [List.all_eq_true]; intro r₁ hr₁
  rw [List.all_eq_true]; intro r₂ hr₂
  obtain ⟨-, hv₁⟩ := invListOK_mem hil hr₁
  obtain ⟨-, hv₂⟩ := invListOK_mem hil hr₂
  obtain ⟨i₁, hi₁, e₁⟩ := invlOK_spec hinvl (packV_lt r₁) hv₁
  obtain ⟨i₂, hi₂, e₂⟩ := invlOK_spec hinvl (packV_lt r₂) hv₂
  rw [allN_iff] at hall
  have h12 := hall i₁ hi₁
  rw [allN_iff] at h12
  have h := h12 i₂ hi₂
  rw [e₁, e₂] at h
  beta_reduce at h
  rw [orB_eq, notB_eq, fourK_packV] at h
  rw [Bool.or_eq_true, Bool.or_eq_true]
  by_cases hc : (r₁ == r₂) = true ∨ (linComp r₁ r₂ != linComp r₂ r₁) = true
  · exact Or.inl hc
  right
  have hc1 : (r₁ == r₂) = false := by simpa using (not_or.mp hc).1
  have hc2 : (linComp r₁ r₂ == linComp r₂ r₁) = true := by
    have := (not_or.mp hc).2; simpa [bne] using this
  rw [hc1, hc2] at h
  simp only [Bool.not_false, Bool.true_and, Bool.not_true, Bool.false_or] at h
  rw [allN_iff] at h
  rw [List.all_eq_true]
  intro r hr
  have hgr : glK (packV r) = true := by
    unfold Gen.glOK at hgl
    simp only [Bool.and_eq_true, List.all_eq_true] at hgl
    rw [glK_packV]; exact hgl.2 r hr
  have hR := h (packV r) (packV_lt r)
  simp only [orB_eq, notB_eq, hgr, Bool.not_true, Bool.false_or, nat_beq_eq, LINID_eq,
    ← packV_linComp, packV_beq] at hR
  simp only [bne, Bool.or_eq_true, List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
    or_false]
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hR
  rcases hR with h1 | h1 | h1 | h1 | h1 | h1
  · left; left; simpa using h1
  · left; right; simpa using h1
  · right; left; exact h1
  · right; right; left; exact h1
  · right; right; right; left; exact h1
  · right; right; right; right; exact h1

end CFSG.KC.GMS.Snd

end
