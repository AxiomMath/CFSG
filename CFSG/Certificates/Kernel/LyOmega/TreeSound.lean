module

public import Certificates.Data.Kernel.LyOmega.Canon
import all CFSG.Certificates.Kernel.LyOmega.SoundB1
import all CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.LyOmega.TreeCoreSpread
import CFSG.Certificates.Kernel.LyOmega.TreeCoreMul
import CFSG.Certificates.Kernel.LyOmega.TreeCoreLeaf
public import CFSG.Certificates.Kernel.LyOmega.Defs
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KS.LyOm

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop

@[expose] def keyM (k : ℕ) : Matrix (Fin 7) (Fin 111) (ZMod 5) :=
  fun i j => ((k / 2 ^ (3 * (111 * i.val + j.val)) % 8 : ℕ) : ZMod 5)

namespace TreePf

open CFSG.KS.LyOm.SB1

private theorem bAnd2 {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem canonM1_bit {e : ℕ} (he : e < 49728) : canonM1.testBit (3 * e) = true := by
  have h1 : canonM1 = CFSG.KS.Ord.pk 3 49728 (fun _ => 1) := by
    unfold canonM1
    rw [CFSG.KS.Ord.rep1_eq (Or.inl (by norm_num))]
    unfold CFSG.KS.Ord.pk
    simp
  have h2 : CFSG.KS.Ord.lane 3 canonM1 e = 1 := by
    rw [h1]
    exact CFSG.KS.Ord.lane_pk (fun _ _ => by norm_num) he
  unfold CFSG.KS.Ord.lane at h2
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 3), h2]
  rfl

private theorem small_of_bits (y : ℕ) (h : ¬ (y.testBit 2 = true ∧ (y.testBit 1 = true ∨ y.testBit 0 = true))) :
    y % 8 < 5 := by
  have e2 : y.testBit 2 = (y % 8).testBit 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp
  have e1 : y.testBit 1 = (y % 8).testBit 1 := by
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp
  have e0 : y.testBit 0 = (y % 8).testBit 0 := by
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp
  rw [e2, e1, e0] at h
  have hy : y % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize y % 8 = v at h hy ⊢
  interval_cases v <;> revert h <;> decide

private theorem canon3_sound {x : ℕ} (h : canon3 x = true) : ∀ e < 49728, x / 2 ^ (3 * e) % 8 < 5 := by
  intro e he
  unfold canon3 at h
  have h0 := Nat.eq_of_beq_eq_true h
  have hb := congrArg (fun z => z.testBit (3 * e)) h0
  simp only [Nat.zero_testBit] at hb
  change ((x >>> 2) &&& ((x >>> 1) ||| x) &&& canonM1).testBit (3 * e) = false at hb
  rw [Nat.testBit_land, Nat.testBit_land, canonM1_bit he, Nat.testBit_lor, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight] at hb
  apply small_of_bits
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  intro ⟨h2, h1⟩
  rw [show 0 + 3 * e = 3 * e by ring] at h1
  rw [h2] at hb
  rcases h1 with h1 | h1
  · rw [h1] at hb; simp at hb
  · rw [h1] at hb; simp at hb

private theorem canonRange' {KX : ℕ → ℕ} {b₀ c : ℕ} (h : canonRange KX b₀ c = true) :
    ∀ b, b₀ ≤ b → b < b₀ + c → ∀ e < 49728, KX b / 2 ^ (3 * e) % 8 < 5 := by
  intro b hb1 hb2
  unfold canonRange at h
  have := (recAnd_iff (fun j => canon3 (KX (Nat.add b₀ j))) c).1 h (b - b₀) (by omega)
  have e : Nat.add b₀ (b - b₀) = b := by change b₀ + (b - b₀) = b; omega
  rw [e] at this
  exact canon3_sound this

private theorem treeRange' {C : Consts} {KX PT : ℕ → ℕ} {G0 G1 n b₀ c : ℕ}
    (h : treeRange C KX PT G0 G1 n b₀ c = true) :
    ∀ b, b₀ ≤ b → b < b₀ + c → treeLeaf C KX PT G0 G1 n b = true := by
  intro b hb1 hb2
  unfold treeRange at h
  have := (recAnd_iff (fun j => treeLeaf C KX PT G0 G1 n (Nat.add b₀ j)) c).1 h (b - b₀) (by omega)
  have e : Nat.add b₀ (b - b₀) = b := by change b₀ + (b - b₀) = b; omega
  rwa [e] at this

private theorem sortChunk' {KX SG : ℕ → ℕ} {n k₀ c : ℕ} (h : sortChunk KX SG n k₀ c = true) :
    ∀ k, k₀ ≤ k → k < k₀ + c → getRec SG 20 k < n ∧ getRec SG 20 (k + 1) < n ∧
      getRec KX 2331 (getRec SG 20 k) < getRec KX 2331 (getRec SG 20 (k + 1)) := by
  intro k hk1 hk2
  have hm : c ≤ 64 * (Nat.add (Nat.shiftRight c (nat_lit 6)) 1) := by
    change c ≤ 64 * (Nat.shiftRight c 6 + 1)
    rw [shr6]; omega
  have key := allBelow_spec h hm (k - k₀) (by omega)
  have e : Nat.add k₀ (k - k₀) = k := by change k₀ + (k - k₀) = k; omega
  dsimp only at key
  rw [e] at key
  simp only [letB_eq, bAnd_eq, Bool.and_eq_true, blt_iff, Nat.succ_eq_add_one] at key
  exact ⟨key.1, key.2.1, key.2.2⟩


section Leaf

open CFSG.KS.Ord CFSG.KS.PackFld CFSG.KS.LyOm.TreeCore

private theorem consts3 {C : Consts} (hC : constsOK C = true) :
    spMasksOK C.MS = true ∧
      (∀ q < 7, ∀ l < 7, C.MASK7 / 2 ^ (12 * (111 * q + l)) % 2 ^ 12 = 2 ^ 12 - 1) ∧
      (∀ q < 7, ∀ l < 7, C.ONE7 / 2 ^ (12 * (111 * q + l)) % 2 ^ 12 = if q = l then 1 else 0) := by
  unfold CFSG.KC.LyOm.constsOK at hC
  obtain ⟨-, hC⟩ := bAnd2 hC
  obtain ⟨-, hC⟩ := bAnd2 hC
  obtain ⟨-, hC⟩ := bAnd2 hC
  obtain ⟨-, hC⟩ := bAnd2 hC
  obtain ⟨-, hC⟩ := bAnd2 hC
  obtain ⟨-, hC⟩ := bAnd2 hC
  obtain ⟨hONE, hC⟩ := bAnd2 hC
  obtain ⟨hMASK, hMS⟩ := bAnd2 hC
  refine ⟨hMS, ?_, ?_⟩
  · rw [Nat.eq_of_beq_eq_true hMASK]
    decide +kernel
  · rw [Nat.eq_of_beq_eq_true hONE]
    decide +kernel

private theorem lane_and (a b k : ℕ) :
    (a &&& b) / 2 ^ k % 2 ^ 12 = (a / 2 ^ k % 2 ^ 12) &&& (b / 2 ^ k % 2 ^ 12) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
  by_cases hj : j < 12 <;> simp [hj]

private theorem lane12 {M t : ℕ} {f : ℕ → ℕ} (hf : ∀ e < M, f e < 2 ^ 12) (ht : t < M) :
    pk 12 M f / 2 ^ (12 * t) % 2 ^ 12 = f t := by
  have := lane_pk hf ht
  unfold lane at this
  exact this

private theorem rows_pk {w M a h : ℕ} {f : ℕ → ℕ} (hw : 0 < w) (hf : ∀ e < M, f e < 2 ^ w)
    (hq : a + h ≤ M) : (pk w M f >>> (w * a)) &&& (2 ^ (w * h) - 1) = pk w h (fun t => f (a + t)) := by
  refine pk_of_fld hw (fld_congr (fld_and (fld_shr a (fld_pk hf)) (fld_RM w h)) fun t => ?_)
    (fun t ht => hf _ (by omega))
  by_cases ht : t < h
  · have h3 : t + a < M := by omega
    simp only [ht, h3, ↓reduceIte]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf _ h3), Nat.add_comm]
  · simp [ht]

private theorem rows7_pk {M q : ℕ} {f : ℕ → ℕ} (hf : ∀ e < M, f e < 2 ^ 12)
    (hq : 777 * q + 777 ≤ M) : rows7 (pk 12 M f) q = pk 12 777 (fun t => f (777 * q + t)) := by
  have key := rows_pk (w := 12) (a := 777 * q) (h := 777) (by norm_num) hf hq
  have e1 : 12 * (777 * q) = Nat.mul 1332 (Nat.mul 7 q) := by
    change _ = 1332 * (7 * q)
    ring
  have e2 : (2 : ℕ) ^ (12 * 777) - 1 = Nat.sub (Nat.shiftLeft 1 (Nat.mul 1332 7)) 1 := by
    change _ = 1 <<< (1332 * 7) - 1
    rw [Nat.one_shiftLeft]
  rw [e1, e2] at key
  exact key

private theorem fld_split (y c e : ℕ) (he : e < 777) :
    y / 2 ^ (3 * (777 * c + e)) % 8 = y / 2 ^ (2331 * c) % 2 ^ 2331 / 2 ^ (3 * e) % 8 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (8 : ℕ) = 2 ^ 3 from rfl]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 3
  · have h1 : j + 3 * e < 2331 := by omega
    simp only [hj, h1, decide_true, Bool.true_and]
    congr 1
    ring
  · simp [hj]

private theorem key_fld (KX : ℕ → ℕ) (b r e : ℕ) (hr : r < 64) (he : e < 777) :
    KX b / 2 ^ (3 * (777 * r + e)) % 8 = getRec KX 2331 (64 * b + r) / 2 ^ (3 * e) % 8 := by
  rw [fld_split _ _ _ he, getRec_eq]
  have e1 : (64 * b + r) / 64 = b := by omega
  have e2 : (64 * b + r) % 64 = r := by omega
  rw [e1, e2, Nat.mul_comm r]

private theorem spread_small {MS : List ℕ} (hMS : spMasksOK MS = true) {x : ℕ}
    (hx : x < 2 ^ (3 * 49728)) :
    spreadB MS x = pk 12 49728 (fun e => x / 2 ^ (3 * e) % 8) := by
  rw [spreadB_eq hMS (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by norm_num))),
    show (65536 : ℕ) = 49728 + 15808 from rfl, Finset.sum_range_add]
  have h0 : ∑ e ∈ Finset.range 15808, x / 2 ^ (3 * (49728 + e)) % 8 * 2 ^ (12 * (49728 + e)) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp
  rw [h0, Nat.add_zero]
  rfl

private theorem rec_of_getRec (PT : ℕ → ℕ) (b r : ℕ) (hr : r < 64) :
    getRec PT 21 (64 * b + r) = recL PT b r := by
  rw [getRec_eq]
  unfold recL
  rw [fldW_eq]
  have e1 : (64 * b + r) / 64 = b := by omega
  have e2 : (64 * b + r) % 64 = r := by omega
  rw [e1, e2, Nat.mul_comm r]
  rfl

private theorem recL_lt (PT : ℕ → ℕ) (b r : ℕ) : recL PT b r < 2 ^ 21 := by
  unfold recL
  rw [fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem par_eq (PT : ℕ → ℕ) (b r : ℕ) (hr : r < 64) :
    fldW (getRec PT 21 (64 * b + r)) 0 20 = parL PT b r := by
  rw [rec_of_getRec PT b r hr, fldW_eq]
  unfold parL
  change _ = recL PT b r &&& (2 ^ 20 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod]
  simp

private theorem lab_eq (PT : ℕ → ℕ) (b r : ℕ) (hr : r < 64) :
    fldW (getRec PT 21 (64 * b + r)) 20 1 = labL PT b r := by
  rw [rec_of_getRec PT b r hr, fldW_eq]
  unfold labL
  change _ = recL PT b r >>> 20
  rw [Nat.shiftRight_eq_div_pow]
  have := recL_lt PT b r
  have h2 : recL PT b r / 2 ^ 20 < 2 ^ 1 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact this
  exact Nat.mod_eq_of_lt h2

private theorem label_case {C : Consts} (hC : constsOK C = true) {KX PT : ℕ → ℕ} {G n b r s : ℕ}
    (hG : LCanon 12 111 111 G)
    (hK : ∀ j < n, ∀ e < 777, getRec KX 2331 j / 2 ^ (3 * e) % 8 < 5) (hKb : KX b < 2 ^ 196608)
    (hpar : ∀ r < 64, isChild n (64 * b + r) = true → parL PT b r < n) (hr : r < 64)
    (hch : isChild n (64 * b + r) = true) (hl : labL PT b r = s) (hin : 64 * b + r < n)
    (hmul : mul7 C (rows7 (mulH C (spreadB C.MS (gather KX PT n b s)) G) (cntL PT n b s r))
        (rows7 (spreadB C.MS (KX b)) r) =
      rows7 (mulH C (spreadB C.MS (gather KX PT n b s)) G) (cntL PT n b s r)) :
    ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
      keyM (getRec KX 2331 (parL PT b r)) * bigM G = M * keyM (getRec KX 2331 (64 * b + r)) := by
  obtain ⟨hMS, -, -⟩ := consts3 hC
  obtain ⟨hgb, hblk, hex⟩ := gather_spec (KX := KX) s hpar
  set A := gather KX PT n b s with hA
  set c := cntL PT n b s r with hc
  have hc64 : c ≤ 63 := by have := cntL_le PT n b s r; omega
  have hcnt : cntL PT n b s 64 ≤ 64 := cntL_le PT n b s 64
  have hA2 : A < 2 ^ (3 * 49728) :=
    lt_of_lt_of_le hgb (Nat.pow_le_pow_right (by norm_num) (by omega))
  set x : ℕ → ℕ := fun e => A / 2 ^ (3 * e) % 8 with hxdef
  have hx : ∀ t < 49728, x t < 5 := by
    intro t ht
    have ht' : t = 777 * (t / 777) + t % 777 := by omega
    show A / 2 ^ (3 * t) % 8 < 5
    rw [ht', fld_split _ _ _ (Nat.mod_lt _ (by norm_num))]
    by_cases hlt : t / 777 < cntL PT n b s 64
    · obtain ⟨j, hj, hjA⟩ := hex _ hlt
      rw [hjA]
      exact hK j hj _ (Nat.mod_lt _ (by norm_num))
    · have : A / 2 ^ (2331 * (t / 777)) = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hgb (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [this]
      norm_num
  have hX : spreadB C.MS A = pk 12 49728 x := spread_small hMS hA2
  have hGex : ∃ g, G = pk 12 12321 g ∧ ∀ t < 12321, g t < 5 :=
    ⟨lane 12 G, pk_lane (by norm_num) (hG.1.trans_eq (congrArg (2 ^ ·) (by norm_num))),
      fun t ht => by
        have := hG.2 (t / 111) (by omega) (t % 111) (by omega)
        have e : 12 * 111 * (t / 111) + 12 * (t % 111) = 12 * t := by omega
        unfold lane
        rwa [e] at this⟩
  obtain ⟨g, hGg, hg⟩ := hGex
  rw [hGg] at hmul ⊢
  set y : ℕ → ℕ := fun t => (∑ k ∈ Finset.range 111, x (111 * (t / 111) + k) * g (111 * k + t % 111)) % 5
    with hydef
  have hY : mulH C (spreadB C.MS A) (pk 12 12321 g) = pk 12 49728 y := by
    rw [hX]
    exact mulH_eq hC hx hg
  have hy : ∀ t < 49728, y t < 5 := fun t _ => Nat.mod_lt _ (by norm_num)
  have hy' : ∀ t < 49728, y t < 2 ^ 12 := fun t ht => lt_of_lt_of_le (hy t ht) (by norm_num)
  set fK : ℕ → ℕ := fun e => KX b / 2 ^ (3 * e) % 8 with hfK
  have hXC : spreadB C.MS (KX b) = pk 12 65536 fK := spreadB_eq hMS hKb
  have hfK' : ∀ e < 65536, fK e < 2 ^ 12 := fun e _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  set m : ℕ → ℕ := fun t => fK (777 * r + t) with hmdef
  have hm_eq : ∀ t < 777, m t = getRec KX 2331 (64 * b + r) / 2 ^ (3 * t) % 8 :=
    fun t ht => key_fld KX b r t hr ht
  have hm : ∀ t < 777, m t < 5 := fun t ht => by rw [hm_eq t ht]; exact hK _ hin t ht
  have hN : rows7 (spreadB C.MS (KX b)) r = pk 12 777 m := by
    rw [hXC]
    exact rows7_pk hfK' (by omega)
  set yy : ℕ → ℕ := fun t => y (777 * c + t) with hyydef
  have hR : rows7 (mulH C (spreadB C.MS A) (pk 12 12321 g)) c = pk 12 777 yy := by
    rw [hY]
    exact rows7_pk hy' (by omega)
  have hyy : ∀ t < 777, yy t < 5 := fun t ht => hy _ (by omega)
  have h7 : mul7 C (pk 12 777 yy) (pk 12 777 m) = pk 12 777 (fun t =>
      (∑ k ∈ Finset.range 7, yy (111 * (t / 111) + k) * m (111 * k + t % 111)) % 5) :=
    mul7_eq hC hyy hm
  rw [hR, hN, h7] at hmul
  have hlane : ∀ t < 777,
      (∑ k ∈ Finset.range 7, yy (111 * (t / 111) + k) * m (111 * k + t % 111)) % 5 = yy t := by
    intro t ht
    have := congrArg (fun z => z / 2 ^ (12 * t) % 2 ^ 12) hmul
    try simp only at this
    rwa [lane12 (fun e _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) ht,
      lane12 (fun e he => lt_of_lt_of_le (hyy e he) (by norm_num)) ht] at this
  have hxk : ∀ q < 7, ∀ k < 111, x (111 * (7 * c + q) + k) =
      getRec KX 2331 (parL PT b r) / 2 ^ (3 * (111 * q + k)) % 8 := by
    intro q hq k hk
    show A / 2 ^ (3 * (111 * (7 * c + q) + k)) % 8 = _
    rw [show 111 * (7 * c + q) + k = 777 * c + (111 * q + k) by ring,
      fld_split _ _ _ (by omega), hc, hblk r hr hch hl]
  refine ⟨Matrix.of fun q k => ((yy (111 * q.val + k.val) : ℕ) : ZMod 5), ?_⟩
  funext q l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.of_apply]
  have hl2 := hlane (111 * q.val + l.val) (by omega)
  have e1 : (111 * q.val + l.val) / 111 = q.val := by omega
  have e2 : (111 * q.val + l.val) % 111 = l.val := by omega
  rw [e1, e2] at hl2
  have hR1 : (∑ k : Fin 7, ((yy (111 * q.val + k.val) : ℕ) : ZMod 5) *
      keyM (getRec KX 2331 (64 * b + r)) k l) = ((yy (111 * q.val + l.val) : ℕ) : ZMod 5) := by
    rw [← hl2, ZMod.natCast_mod, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold keyM
    rw [← hm_eq _ (by omega)]
    push_cast
    ring
  rw [hR1]
  have hyq : yy (111 * q.val + l.val) =
      (∑ k ∈ Finset.range 111, x (111 * (7 * c + q.val) + k) * g (111 * k + l.val)) % 5 := by
    show y (777 * c + (111 * q.val + l.val)) = _
    simp only [hydef]
    have e3 : (777 * c + (111 * q.val + l.val)) / 111 = 7 * c + q.val := by omega
    have e4 : (777 * c + (111 * q.val + l.val)) % 111 = l.val := by omega
    rw [e3, e4]
  rw [hyq, ZMod.natCast_mod, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hxk q.val q.isLt k.val k.isLt]
  unfold keyM bigM ent
  have e5 : 1332 * k.val + 12 * l.val = 12 * (111 * k.val + l.val) := by ring
  rw [e5, lane12 (fun e he => lt_of_lt_of_le (hg e he) (by norm_num)) (by omega)]
  push_cast
  ring

private theorem treeLeaf' {C : Consts} (hC : constsOK C = true) {KX PT : ℕ → ℕ} {G0 G1 n b r : ℕ}
    (hG0 : LCanon 12 111 111 G0) (hG1 : LCanon 12 111 111 G1)
    (hK : ∀ j < n, ∀ e < 777, getRec KX 2331 j / 2 ^ (3 * e) % 8 < 5) (hKb : KX b < 2 ^ 196608)
    (h : treeLeaf C KX PT G0 G1 n b = true) (hr : r < 64) (hi0 : 0 < 64 * b + r)
    (hin : 64 * b + r < n) :
    fldW (getRec PT 21 (64 * b + r)) 0 20 < 64 * b + r ∧
      firstCols (keyM (getRec KX 2331 (64 * b + r))) = 1 ∧
      ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
        keyM (getRec KX 2331 (fldW (getRec PT 21 (64 * b + r)) 0 20)) *
          bigM (if fldW (getRec PT 21 (64 * b + r)) 20 1 = 0 then G0 else G1) =
          M * keyM (getRec KX 2331 (64 * b + r)) := by
  unfold treeLeaf at h
  simp only [letB_eq] at h
  have hch : ∀ r' < 64, 0 < 64 * b + r' → 64 * b + r' < n → isChild n (64 * b + r') = true := by
    intro r' _ h1 h2
    unfold isChild
    rw [blt_iff.2 h1, blt_iff.2 h2]
  have hw := leafCmp_walk h
  have hpar : ∀ r' < 64, isChild n (64 * b + r') = true → parL PT b r' < n := by
    intro r' hr' hc
    have := (hw r' hr' hc).1
    have : 64 * b + r' < n := by
      unfold isChild at hc
      obtain ⟨-, h2⟩ := bAnd2 hc
      exact blt_iff.1 h2
    omega
  obtain ⟨hp, hmask, h0, h1⟩ := hw r hr (hch r hr hi0 hin)
  rw [par_eq PT b r hr, lab_eq PT b r hr]
  refine ⟨hp, ?_, ?_⟩
  ·
    obtain ⟨hMS, hM7, hO7⟩ := consts3 hC
    have hXC : spreadB C.MS (KX b) = pk 12 65536 (fun e => KX b / 2 ^ (3 * e) % 8) :=
      spreadB_eq hMS hKb
    have hN : rows7 (spreadB C.MS (KX b)) r =
        pk 12 777 (fun t => KX b / 2 ^ (3 * (777 * r + t)) % 8) := by
      rw [hXC]
      exact rows7_pk (fun e _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
        (by omega)
    funext q l
    have hql := congrArg (fun z => z / 2 ^ (12 * (111 * q.val + l.val)) % 2 ^ 12) hmask
    try simp only at hql
    change (rows7 (spreadB C.MS (KX b)) r &&& C.MASK7) / _ % _ = _ at hql
    rw [lane_and, hM7 q.val q.isLt l.val l.isLt, hO7 q.val q.isLt l.val l.isLt, hN,
      lane12 (fun e _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) (by omega),
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
        (by norm_num))] at hql
    show keyM (getRec KX 2331 (64 * b + r)) q ⟨l.val, by omega⟩ =
      (1 : Matrix (Fin 7) (Fin 7) (ZMod 5)) q l
    unfold keyM
    rw [← key_fld KX b r _ hr (by omega), hql, Matrix.one_apply]
    by_cases hqe : q.val = l.val
    · have : q = ⟨l.val, by omega⟩ := Fin.ext hqe
      simp [hqe, this]
    · have : q ≠ ⟨l.val, by omega⟩ := fun h => hqe (by rw [h])
      simp [hqe, this]
  · by_cases hl : labL PT b r = 0
    · rw [if_pos hl]
      exact label_case hC hG0 hK hKb hpar hr (hch r hr hi0 hin) hl hin (h0 hl)
    · have hl1 : labL PT b r = 1 := by have := labL_lt PT b r; omega
      rw [if_neg hl]
      exact label_case hC hG1 hK hKb hpar hr (hch r hr hi0 hin) hl1 hin (h1 hl1)

end Leaf

end TreePf

theorem canonRange_sound {KX : ℕ → ℕ} {b₀ c : ℕ} (h : canonRange KX b₀ c = true) :
    ∀ b, b₀ ≤ b → b < b₀ + c → ∀ e < 49728, KX b / 2 ^ (3 * e) % 8 < 5 :=
  TreePf.canonRange' h

theorem treeLeaf_sound {C : Consts} (hC : constsOK C = true) {KX PT : ℕ → ℕ} {G0 G1 n b r : ℕ}
    (hG0 : LCanon 12 111 111 G0) (hG1 : LCanon 12 111 111 G1)
    (hK : ∀ j < n, ∀ e < 777, getRec KX 2331 j / 2 ^ (3 * e) % 8 < 5) (hKb : KX b < 2 ^ 196608)
    (h : treeLeaf C KX PT G0 G1 n b = true) (hr : r < 64) (hi0 : 0 < 64 * b + r)
    (hin : 64 * b + r < n) :
    fldW (getRec PT 21 (64 * b + r)) 0 20 < 64 * b + r ∧
      firstCols (keyM (getRec KX 2331 (64 * b + r))) = 1 ∧
      ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 5),
        keyM (getRec KX 2331 (fldW (getRec PT 21 (64 * b + r)) 0 20)) *
          bigM (if fldW (getRec PT 21 (64 * b + r)) 20 1 = 0 then G0 else G1) =
          M * keyM (getRec KX 2331 (64 * b + r)) :=
  TreePf.treeLeaf' hC hG0 hG1 hK hKb h hr hi0 hin

theorem treeRange_sound {C : Consts} {KX PT : ℕ → ℕ} {G0 G1 n b₀ c : ℕ}
    (h : treeRange C KX PT G0 G1 n b₀ c = true) :
    ∀ b, b₀ ≤ b → b < b₀ + c → treeLeaf C KX PT G0 G1 n b = true :=
  TreePf.treeRange' h

theorem sortChunk_sound {KX SG : ℕ → ℕ} {n k₀ c : ℕ} (h : sortChunk KX SG n k₀ c = true) :
    ∀ k, k₀ ≤ k → k < k₀ + c → getRec SG 20 k < n ∧ getRec SG 20 (k + 1) < n ∧
      getRec KX 2331 (getRec SG 20 k) < getRec KX 2331 (getRec SG 20 (k + 1)) :=
  TreePf.sortChunk' h

end CFSG.KS.LyOm

end
