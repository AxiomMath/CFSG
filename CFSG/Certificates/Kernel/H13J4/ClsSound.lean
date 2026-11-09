
module

public import Certificates.Data.Kernel.H13J4.Cls
public import CFSG.Certificates.Kernel.SporSch.J4SSylowSound
public import CFSG.Quasithin.H13.J4ClassCheckInputs
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.H13J4

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11 CFSG.KS.Raw.Orb
open CFSG.Quasithin.H13.J4 CFSG.Quasithin.H13.J4.Native
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem conj_eq (P Q B : Nat) :
    conjCols (unpack11 P) (unpack11 Q) (unpack11 B) = unpack11 (conjK P Q B) := by
  change CFSG.Sporadic.J4Schreier.comp11 (CFSG.Sporadic.J4Schreier.comp11 _ _) _ = _
  rw [comp_eq, comp_eq]
  rfl

theorem colsBounded_unpack (P : Nat) : colsBounded (unpack11 P) = true := by
  obtain ⟨h1, h2⟩ := unpack11_bounded P
  simp only [colsBounded, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  exact ⟨h1, h2⟩

theorem compTabK_eq {P L : Nat} (h : appTabOK P L = true) (B : Nat) :
    compTabK L B = compK P B := by
  unfold compTabK compK
  congr 1
  funext j
  have hj : colK B j < 2048 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  exact Nat.eq_of_beq_eq_true (allN_spec h _ hj)

theorem unpack11_eq_of_cols {P Q : Nat} (h : colsMatrix (unpack11 P) = colsMatrix (unpack11 Q)) :
    unpack11 P = unpack11 Q := by
  obtain ⟨sP, hP⟩ := unpack11_bounded P
  obtain ⟨sQ, hQ⟩ := unpack11_bounded Q
  refine Array.ext (by rw [sP, sQ]) (fun j h1 h2 => ?_)
  have hj : j < 11 := by omega
  have eP : (unpack11 P)[j]?.getD 0 = (unpack11 P)[j]! := by
    rw [getElem!_pos _ j h1, getElem?_pos _ j h1, Option.getD_some]
  have eQ : (unpack11 Q)[j]?.getD 0 = (unpack11 Q)[j]! := by
    rw [getElem!_pos _ j h2, getElem?_pos _ j h2, Option.getD_some]
  have e := toVecD_injective (d := 11) (hP j hj) (hQ j hj) (funext fun i => by
    have := congrFun (congrFun h i) ⟨j, hj⟩
    rwa [colsMatrix_apply, colsMatrix_apply, eP, eQ] at this)
  rwa [getElem!_pos _ j h1, getElem!_pos _ j h2] at e

theorem cols_conjCols (A B X : Array Nat) :
    colsMatrix (conjCols A B X) = colsMatrix A * colsMatrix X * colsMatrix B := by
  change colsMatrix (comp11 (comp11 A X) B) = _
  rw [colsMatrix_comp11, colsMatrix_comp11]

theorem conjCols_inv {a b x : Nat} (h : comp11 (unpack11 a) (unpack11 b) = idRows 11) :
    conjCols (unpack11 a) (unpack11 b) (unpack11 (conjK b a x)) = unpack11 x := by
  rw [conj_eq]
  apply unpack11_eq_of_cols
  rw [← conj_eq, cols_conjCols, ← conj_eq, cols_conjCols]
  have h1 : colsMatrix (unpack11 a) * colsMatrix (unpack11 b) = 1 := by
    rw [← colsMatrix_comp11, h, colsMatrix_idRows]
  calc colsMatrix (unpack11 a) * (colsMatrix (unpack11 b) * colsMatrix (unpack11 x) *
        colsMatrix (unpack11 a)) * colsMatrix (unpack11 b)
      = (colsMatrix (unpack11 a) * colsMatrix (unpack11 b)) * colsMatrix (unpack11 x) *
          (colsMatrix (unpack11 a) * colsMatrix (unpack11 b)) := by
        simp only [Matrix.mul_assoc]
    _ = colsMatrix (unpack11 x) := by rw [h1, Matrix.one_mul, Matrix.mul_one]

@[expose] noncomputable def packUpK (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => strictN acc (fun s => Nat.lor s (Nat.shiftLeft (f j) (Nat.mul (nat_lit 11) j)))) n

theorem packUpK_succ (f : Nat → Nat) (n : Nat) :
    packUpK f (n + 1) = packUpK f n ||| f n <<< (11 * n) := by
  unfold packUpK
  exact PackFld.strictN_eqP _ _

theorem packK_eq (f : Nat → Nat) : packK f = packUpK f (nat_lit 11) := rfl

theorem packUpK_zero (n : Nat) : packUpK (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packUpK_succ, ih, Nat.zero_shiftLeft, Nat.or_zero]

theorem bit_mul_le {b : Nat} (hb : b ≤ 1) (v : Nat) : b * v ≤ v := by
  simpa using Nat.mul_le_mul_right v hb

theorem packUpK_lt {f : Nat → Nat} (hf : ∀ j, f j < 2 ^ 11) (n : Nat) :
    packUpK f n < 2 ^ (11 * n) := by
  induction n with
  | zero => exact Nat.two_pow_pos _
  | succ n ih =>
    rw [packUpK_succ, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ih, Nat.shiftLeft_eq,
      Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (11 * n))]
    have h2 : f n * 2 ^ (11 * n) + 2 ^ (11 * n) ≤ 2 ^ 11 * 2 ^ (11 * n) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (hf n)
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left ih _) h2

theorem packUpK_xor {f g : Nat → Nat} (hf : ∀ j, f j < 2 ^ 11) (hg : ∀ j, g j < 2 ^ 11)
    (n : Nat) : packUpK f n ^^^ packUpK g n = packUpK (fun j => f j ^^^ g j) n := by
  induction n with
  | zero => exact Nat.zero_xor 0
  | succ n ih =>
    rw [packUpK_succ, packUpK_succ, packUpK_succ, ← ih]
    have hA := packUpK_lt hf n
    have hB := packUpK_lt hg n
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hi : 11 * n ≤ i
    · have h1 : (packUpK f n).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by omega) hi))
      have h2 : (packUpK g n).testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hB (Nat.pow_le_pow_right (by omega) hi))
      simp [h1, h2, hi]
    · simp [hi]

theorem mul_packUpK {b : Nat → Nat} (hb : ∀ j, b j ≤ 1) {v : Nat} (hv : v < 2 ^ 11) (n : Nat) :
    v * packUpK b n = packUpK (fun j => b j * v) n := by
  have hb' : ∀ j, b j < 2 ^ 11 := fun j => Nat.lt_of_le_of_lt (hb j) (by decide)
  have hbv : ∀ j, b j * v < 2 ^ 11 := fun j =>
    Nat.lt_of_le_of_lt (bit_mul_le (hb j) v) hv
  induction n with
  | zero => exact Nat.mul_zero v
  | succ n ih =>
    rw [packUpK_succ, packUpK_succ, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt
      (packUpK_lt hb' n), Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (packUpK_lt hbv n), ← ih,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_add]
    ring

theorem fld_packUpK (f : Nat → Nat) (hf : ∀ j, f j < 2 ^ 11) (n : Nat) :
    PackFld.Fld 11 (packUpK f n) (fun i => if i < n then f i else 0) := by
  induction n with
  | zero => exact PackFld.fld_congr (PackFld.fld_zero 11) (fun i => by simp)
  | succ n ih =>
    rw [packUpK_succ]
    refine PackFld.fld_congr (PackFld.fld_or ih (PackFld.fld_shl n (PackFld.fld_one (hf n))))
      (fun i => ?_)
    by_cases h1 : i < n
    · have h2 : ¬ n ≤ i := by omega
      simp [h1, h2, show i < n + 1 by omega]
    · by_cases h3 : i = n
      · subst h3
        simp
      · have h4 : ¬ i < n + 1 := by omega
        have h5 : i - n ≠ 0 := by omega
        simp [h1, h4, h5]

theorem colK_lt (P j : Nat) : colK P j < 2 ^ 11 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem appTabK_lt (L a : Nat) : appTabK L a < 2 ^ 11 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem colK_packK {f : Nat → Nat} (hf : ∀ j, f j < 2 ^ 11) {k : Nat} (hk : k < 11) :
    colK (packK f) k = f k := by
  have hk' : (fun i => if i < 11 then f i else 0) k < 2 ^ 11 := by
    simp only [hk, ↓reduceIte]
    exact hf k
  have := PackFld.pg_of_fld (fld_packUpK f hf 11) hk'
  simp only [hk, ↓reduceIte] at this
  exact this

theorem appRec_succ (P a n : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
        (nat_lit 1), Nat.xor s (colK P j), s))) (n + 1) : Nat) =
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
        (nat_lit 1), Nat.xor s (colK P j), s))) n) ^^^
      (Nat.land (Nat.shiftRight a n) (nat_lit 1) * colK P n) := by
  change strictN _ _ = _
  rw [PackFld.strictN_eqP]
  have hb : Nat.land (Nat.shiftRight a n) (nat_lit 1) < 2 := by
    change (a >>> n) &&& 1 < 2
    rw [Nat.and_one_is_mod]
    exact Nat.mod_lt _ (by decide)
  generalize Nat.land (Nat.shiftRight a n) (nat_lit 1) = b at hb ⊢
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · rw [Nat.zero_mul, Nat.xor_zero]
    rfl
  · rw [Nat.one_mul]
    rfl

theorem appRec_lt (P a n : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight a j) (nat_lit 1))
        (nat_lit 1), Nat.xor s (colK P j), s))) n : Nat) < 2 ^ 11 := by
  induction n with
  | zero => exact Nat.two_pow_pos 11
  | succ n ih =>
    rw [appRec_succ]
    exact Nat.xor_lt_two_pow ih (Nat.lt_of_le_of_lt (bit_mul_le Nat.and_le_right _) (colK_lt _ _))

theorem conjTabK_eq {P R : Nat} (hR : rowOK P R = true) (L B : Nat) :
    conjTabK L R B = compK (compTabK L B) P := by
  have hX : ∀ k < 11, appTabK L (colK B k) = colK (compTabK L B) k := fun k hk =>
    (colK_packK (f := fun j => appTabK L (colK B j)) (fun j => appTabK_lt _ _) hk).symm
  suffices h : ∀ n, n ≤ 11 → (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => strictN acc fun s =>
        Nat.xor s (Nat.mul (appTabK L (colK B k)) (rowK R k))) n : Nat) =
      packUpK (fun j => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight (colK P j) i)
          (nat_lit 1)) (nat_lit 1), Nat.xor s (colK (compTabK L B) i), s))) n) (nat_lit 11) by
    unfold conjTabK compK packK appK
    exact h (nat_lit 11) (by decide)
  intro n hn
  induction n with
  | zero => exact (packUpK_zero _).symm
  | succ n ih =>
    change strictN _ _ = _
    rw [PackFld.strictN_eqP, ih (Nat.le_of_succ_le hn), hX n (Nat.lt_of_succ_le hn)]
    have hr := Nat.eq_of_beq_eq_true (allN_spec hR n (Nat.lt_of_succ_le hn))
    change _ ^^^ (colK (compTabK L B) n * rowK R n) = _
    rw [hr, packK_eq, mul_packUpK (b := fun j => Nat.land (Nat.shiftRight (colK P j) n) (nat_lit 1))
      (fun j => Nat.and_le_right) (colK_lt _ _),
      packUpK_xor (f := fun j => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun i acc => strictN acc (fun s => nIf(Nat.beq (Nat.land (Nat.shiftRight (colK P j) i)
          (nat_lit 1)) (nat_lit 1), Nat.xor s (colK (compTabK L B) i), s))) n)
        (g := fun j => Nat.land (Nat.shiftRight (colK P j) n) (nat_lit 1) * colK (compTabK L B) n)
        (fun j => appRec_lt _ _ _)
        (fun j => Nat.lt_of_le_of_lt (bit_mul_le Nat.and_le_right _) (colK_lt _ _))]
    congr 1
    funext j
    rw [appRec_succ]

theorem stepK_spec {L R T GEN NX : Nat → Nat} {m n i : Nat}
    (h : stepK L R T GEN NX m n i = true) :
    (0 < i → GEN i < m ∧ NX (m * i + GEN i) < i) ∧
      ∀ g < m, NX (m * i + g) < n ∧ T (NX (m * i + g)) = conjTabK (L g) (R g) (T i) := by
  unfold stepK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun hi => ?_, fun g hg => ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hne : Nat.beq (i + 1) 0 = false := rfl
    rw [bIf_eq, hne] at h1
    simp only [Bool.false_eq_true, ↓reduceIte, strictB_eq] at h1
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h1
    exact ⟨Nat.le_of_ble_eq_true a, Nat.le_of_ble_eq_true b⟩
  · have := allN_spec h2 g hg
    simp only [strictB_eq] at this
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 this
    exact ⟨Nat.le_of_ble_eq_true a, Nat.eq_of_beq_eq_true b⟩

theorem clsFacts_of {G GI L R T GEN NX SO SOI : Nat → Nat} {m n : Nat}
    {gens : Array (Array ℕ × Array ℕ)} {M : Array ℕ} (hgs : gens.size = m)
    (hG : ∀ g < m, (gens[g]!).1 = unpack11 (G g)) (hGI : ∀ g < m, (gens[g]!).2 = unpack11 (GI g))
    (hinv : ∀ g < m, Nat.beq (compK (G g) (GI g)) pidK = true)
    (hL : ∀ g < m, appTabOK (GI g) (L g) = true) (hR : ∀ g < m, rowOK (G g) (R g) = true)
    (hM : M = unpack11 (T 0)) (hd : distinctK T SO SOI n = true)
    (hs : ∀ i < n, stepK L R T GEN NX m n i = true) : ClsFacts gens M n := by
  have hc : ∀ i < n, ∀ g < m, NX (m * i + g) < n ∧
      T (NX (m * i + g)) = conjK (GI g) (G g) (T i) := fun i hi g hg => by
    obtain ⟨h1, h2⟩ := (stepK_spec (hs i hi)).2 g hg
    rw [conjTabK_eq (hR g hg), compTabK_eq (hL g hg)] at h2
    exact ⟨h1, h2⟩
  refine ⟨fun i => unpack11 (T i), hM.symm, fun i _ => colsBounded_unpack _,
    fun i hi j hj => distinctK_sound hd i hi j hj, fun i hi hi0 => ?_, fun i hi g hg => ?_⟩
  · obtain ⟨h1, h2⟩ := (stepK_spec (hs i hi)).1 hi0
    have hid : comp11 (unpack11 (G (GEN i))) (unpack11 (GI (GEN i))) = idRows 11 := by
      rw [comp_sound (hinv _ h1), SporSch.C11.id_eq]
    refine ⟨NX (m * i + GEN i), h2, GEN i, hgs ▸ h1, ?_⟩
    beta_reduce
    rw [hG _ h1, hGI _ h1, (hc i hi _ h1).2, conjCols_inv hid]
  · rw [hgs] at hg
    obtain ⟨h1, h2⟩ := hc i hi g hg
    refine ⟨NX (m * i + g), h1, ?_⟩
    beta_reduce
    rw [hG _ hg, hGI _ hg, conj_eq, h2]

theorem step_of_slices {L R T GEN NX : Nat → Nat} {m n k S : Nat} (hn : n ≤ k * S)
    (h : ∀ s < S, allBlk (k * s) (stepAt L R T GEN NX m n) k = true) :
    ∀ i < n, stepK L R T GEN NX m n i = true := by
  intro i hi
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · omega
    · exact hk
  have hs : i / k < S := by
    rw [Nat.div_lt_iff_lt_mul hk]
    rw [Nat.mul_comm] at hn
    omega
  have := allBlk_spec (h _ hs) (i % k) (Nat.mod_lt i hk)
  have e : Nat.add (k * (i / k)) (i % k) = i := Nat.div_add_mod i k
  rw [e] at this
  unfold stepAt at this
  simp only [bIf_eq, Nat.blt_eq, hi, ↓reduceIte] at this
  exact this

end CFSG.KS.H13J4

end
