module

public import Certificates.Data.Kernel.SporSch.HNXPtS
public import CFSG.Certificates.Kernel.SporSch.HNXPtSound
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Spor.PackFld
import all CFSG.Certificates.Kernel.Spor.OrdSound

public section

set_option maxRecDepth 100000

namespace CFSG.KS.SporSch.HNXP

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.SporSch CFSG.KS.Ord CFSG.KS.PackFld Finset Matrix

theorem sOnes_eq {w : Nat} (hw : 0 < w) : ∀ n, sOnes w n = ∑ i ∈ range n, 2 ^ (w * i)
  | 0 => rfl
  | n + 1 => by
    change sOnes w n ||| (1 <<< (w * n)) = _
    rw [sOnes_eq hw n, Finset.sum_range_succ, Nat.shiftLeft_eq, Nat.one_mul]
    have hb : ∑ i ∈ range n, 2 ^ (w * i) < 2 ^ (w * n) := by
      have := lanes_lt (w := w) (n := n) (g := fun _ => 1) fun _ _ => Nat.one_lt_two_pow (by omega)
      simpa using this
    have e := Nat.two_pow_add_eq_or_of_lt hb 1
    rw [Nat.mul_one] at e
    change _ ||| _ = _
    rw [Nat.lor_comm, ← e, Nat.add_comm]

theorem sk_and {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A &&& B) (fun i => g i &&& h i) := by
  intro i k hk
  rw [Nat.testBit_and, hA i k hk, hB i k hk, Nat.testBit_and]

theorem sk_pairs (f : Nat → Nat) (S : Nat) : ∀ N, ∑ m ∈ range (2 * N), f m * 2 ^ (S * m) =
    ∑ j ∈ range N, (f (2 * j) + f (2 * j + 1) * 2 ^ S) * 2 ^ (2 * S * j)
  | 0 => rfl
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sk_pairs f S N, Finset.sum_range_succ]
    rw [show S * (2 * N + 1) = 2 * S * N + S by ring, show S * (2 * N) = 2 * S * N by ring,
      Nat.pow_add]
    ring

theorem sk_step {S w d N : Nat} (hS : 0 < S) (hd : d + w = S) {E O : Nat → Nat}
    (hE : ∀ j < N, E j < 2 ^ w) (hO : ∀ j < N, O j < 2 ^ w) {x : Nat}
    (hx : x = ∑ j ∈ range N, (E j + O j * 2 ^ S) * 2 ^ (2 * S * j)) :
    (x &&& ((2 ^ w - 1) * ∑ j ∈ range N, 2 ^ (2 * S * j))) |||
        ((x - (x &&& ((2 ^ w - 1) * ∑ j ∈ range N, 2 ^ (2 * S * j)))) >>> d) =
      ∑ j ∈ range N, (E j + O j * 2 ^ w) * 2 ^ (2 * S * j) := by
  have h2S : 0 < 2 * S := by omega
  have hwS : 2 ^ w ≤ 2 ^ S := Nat.pow_le_pow_right (by omega) (by omega)
  have hpair : ∀ j < N, E j + O j * 2 ^ S < 2 ^ (2 * S) := fun j hj => by
    have h1 : E j + O j * 2 ^ S < (O j + 1) * 2 ^ S := by
      have := hE j hj
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : (O j + 1) * 2 ^ S ≤ 2 ^ S * 2 ^ S :=
      Nat.mul_le_mul_right _ (by have := hO j hj; omega)
    rw [show 2 * S = S + S by ring, Nat.pow_add]
    omega
  have FX : Fld (2 * S) x (fun t => if t < N then E t + O t * 2 ^ S else 0) := hx ▸ fld_pk hpair
  have hK : (2 ^ w - 1) * ∑ j ∈ range N, 2 ^ (2 * S * j) =
      CFSG.KS.Ord.pk (2 * S) N (fun _ => 2 ^ w - 1) := by
    unfold CFSG.KS.Ord.pk
    rw [Finset.mul_sum]
  have FK := fld_pk (w := 2 * S) (n := N) (g := fun _ => 2 ^ w - 1) fun _ _ =>
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [hK]
  have hk : x &&& CFSG.KS.Ord.pk (2 * S) N (fun _ => 2 ^ w - 1) = ∑ j ∈ range N, E j * 2 ^ (2 * S * j) := by
    refine pk_of_fld h2S (fld_congr (sk_and FX FK) fun t => ?_)
      fun j hj => Nat.lt_of_lt_of_le (hE j hj) (Nat.pow_le_pow_right (by omega) (by omega))
    by_cases ht : t < N
    · simp only [ht, ↓reduceIte, Nat.and_two_pow_sub_one_eq_mod]
      rw [show 2 ^ S = 2 ^ d * 2 ^ w by rw [← Nat.pow_add, hd], ← Nat.mul_assoc,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hE t ht)]
    · simp [ht]
  rw [hk]
  have hsplit : x = ∑ j ∈ range N, E j * 2 ^ (2 * S * j) +
      2 ^ d * ∑ j ∈ range N, O j * 2 ^ w * 2 ^ (2 * S * j) := by
    rw [hx, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 ^ S = 2 ^ d * 2 ^ w by rw [← Nat.pow_add, hd]]
    ring
  have hsh : (x - ∑ j ∈ range N, E j * 2 ^ (2 * S * j)) >>> d =
      ∑ j ∈ range N, O j * 2 ^ w * 2 ^ (2 * S * j) := by
    rw [hsplit, Nat.add_sub_cancel_left, Nat.shiftRight_eq_div_pow,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  rw [hsh]
  have hOw : ∀ j < N, O j * 2 ^ w < 2 ^ (2 * S) := fun j hj =>
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right (hO j hj) (Nat.two_pow_pos _))
      (by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega))
  have hEw : ∀ j < N, E j < 2 ^ (2 * S) := fun j hj =>
    Nat.lt_of_lt_of_le (hE j hj) (Nat.pow_le_pow_right (by omega) (by omega))
  refine pk_of_fld h2S (fld_congr (fld_or (fld_pk hEw) (fld_pk hOw)) fun t => ?_) fun j hj => ?_
  · by_cases ht : t < N
    · simp only [ht, ↓reduceIte]
      rw [Nat.lor_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (hE t ht), Nat.add_comm,
        Nat.mul_comm]
    · simp [ht]
  · have h1 : E j + O j * 2 ^ w < 2 ^ (w + w) := by
      rw [Nat.pow_add]
      have := hE j hj
      have := Nat.mul_le_mul_right (2 ^ w) (show O j + 1 ≤ 2 ^ w from hO j hj)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))

noncomputable def skBlk (LW : Nat) (v : Nat → Nat) (i m : Nat) : Nat :=
  ∑ q ∈ range (2 ^ i), v (2 ^ i * m + q) * 2 ^ (LW * q)

theorem skBlk_succ (LW : Nat) (v : Nat → Nat) (i j : Nat) :
    skBlk LW v (i + 1) j = skBlk LW v i (2 * j) + skBlk LW v i (2 * j + 1) * 2 ^ (LW * 2 ^ i) := by
  unfold skBlk
  rw [Nat.pow_succ, Nat.mul_two, Finset.sum_range_add, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (2 ^ i + 2 ^ i) * j + q = 2 ^ i * (2 * j) + q by ring]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (2 ^ i + 2 ^ i) * j + (2 ^ i + q) = 2 ^ i * (2 * j + 1) + q by ring,
      show LW * (2 ^ i + q) = LW * q + LW * 2 ^ i by ring, Nat.pow_add, Nat.mul_assoc]

theorem skBlk_lt {LW : Nat} {v : Nat → Nat} (hv : ∀ r, v r < 2 ^ LW) (i m : Nat) :
    skBlk LW v i m < 2 ^ (LW * 2 ^ i) :=
  lanes_lt fun _ _ => hv _

theorem sLeafA_eq {L RB Q LW g : Nat} (h0 : 0 < LW) (h1 : LW ≤ RB) (h2 : 3 * Q ≤ LW) :
    sLeafA L RB Q LW g = ∑ r ∈ range 64, L / 2 ^ (RB * r + 3 * Q * g) % 2 ^ (3 * Q) * 2 ^ (LW * r) := by
  set v : Nat → Nat := fun r => L / 2 ^ (RB * r + 3 * Q * g) % 2 ^ (3 * Q) with hvdef
  have hv : ∀ r, v r < 2 ^ LW := fun r =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) h2)
  have hRB : 0 < RB := by omega
  have inv : ∀ i ≤ 6, Nat.rec (motive := fun _ => Nat)
      (Nat.land (Nat.shiftRight L (Nat.mul (Nat.mul (nat_lit 3) Q) g))
        (Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 3) Q)) (nat_lit 1))
          (sOnes RB (nat_lit 64))))
      (fun i x => CFSG.KC.Loop.strictN x (fun x => CFSG.KC.Loop.strictN
        (Nat.land x (sKeep RB LW i)) (fun k =>
          Nat.lor k (Nat.shiftRight (Nat.sub x k)
            (Nat.mul (Nat.sub RB LW) (Nat.shiftLeft (nat_lit 1) i)))))) i =
      ∑ m ∈ range (2 ^ (6 - i)), skBlk LW v i m * 2 ^ (RB * 2 ^ i * m) := by
    refine lanes_rec_eq (N := 6) ?_ ?_
    ·
      have FL := CFSG.KS.Ord.fld_lane RB (L >>> (3 * Q * g))
      have FM := fld_pk (w := RB) (n := 64) (g := fun _ => 2 ^ (3 * Q) - 1) fun _ _ =>
        Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
          (Nat.pow_le_pow_right (by omega) (by omega))
      have hM : Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 3) Q)) (nat_lit 1))
          (sOnes RB (nat_lit 64)) = CFSG.KS.Ord.pk RB 64 (fun _ => 2 ^ (3 * Q) - 1) := by
        change (1 <<< (3 * Q) - 1) * sOnes RB 64 = _
        rw [sOnes_eq hRB, Nat.shiftLeft_eq, Nat.one_mul, Finset.mul_sum]
        rfl
      rw [hM]
      change (L >>> (3 * Q * g)) &&& _ = _
      have e := pk_of_fld (n := 64) (g := v) hRB (fld_congr (sk_and FL FM) fun t => ?_)
        fun t _ => Nat.lt_of_lt_of_le (hv t) (Nat.pow_le_pow_right (by omega) h1)
      · rw [e]
        unfold CFSG.KS.Ord.pk skBlk
        simp
      · by_cases ht : t < 64
        · simp only [ht, ↓reduceIte, Nat.and_two_pow_sub_one_eq_mod]
          unfold CFSG.KS.Ord.lane
          rw [hvdef, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.shiftRight_eq_div_pow,
            Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm (3 * Q * g)]
        · simp [ht]
    · intro i hi acc hacc
      rw [loopStrictN_eq, loopStrictN_eq, hacc]
      obtain ⟨N, hN⟩ : ∃ N, 2 ^ (6 - i) = 2 * N := ⟨2 ^ (5 - i), by
        rw [show 6 - i = 5 - i + 1 by omega, Nat.pow_succ, Nat.mul_comm]⟩
      have hN' : 2 ^ (6 - (i + 1)) = N := by
        rw [show 6 - i = 6 - (i + 1) + 1 by omega, Nat.pow_succ] at hN
        omega
      have hkeep : sKeep RB LW i =
          (2 ^ (LW * 2 ^ i) - 1) * ∑ j ∈ range N, 2 ^ (2 * (RB * 2 ^ i) * j) := by
        unfold sKeep
        change (1 <<< (LW * (1 <<< i)) - 1) * sOnes (RB * (2 <<< i)) (32 >>> i) = _
        rw [sOnes_eq (Nat.mul_pos hRB (by rw [Nat.shiftLeft_eq]; positivity)), Nat.shiftLeft_eq,
          Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, Nat.shiftRight_eq_div_pow,
          show (32 : Nat) = 2 ^ 5 by norm_num, Nat.pow_div (by omega) (by omega)]
        have e5 : 2 ^ (5 - i) = N := by
          rw [← hN', show 6 - (i + 1) = 5 - i by omega]
        rw [e5]
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        ring_nf
      rw [hkeep, hN, sk_pairs (fun m => skBlk LW v i m) (RB * 2 ^ i) N]
      change (_ &&& _) ||| ((_ - (_ &&& _)) >>> ((RB - LW) * (1 <<< i))) = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [sk_step (S := RB * 2 ^ i) (w := LW * 2 ^ i) (d := (RB - LW) * 2 ^ i) (N := N)
        (by positivity) (by rw [← Nat.add_mul]; congr 1; omega)
        (fun j _ => skBlk_lt hv i _) (fun j _ => skBlk_lt hv i _) rfl, hN']
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [skBlk_succ, Nat.pow_succ]
      ring_nf
  unfold sLeafA
  refine (inv 6 le_rfl).trans ?_
  simp only [Nat.sub_self, Nat.pow_zero, Finset.sum_range_one, Nat.mul_zero, Nat.pow_zero,
    Nat.mul_one]
  unfold skBlk
  simp [hvdef]

theorem mulC_pkS {CM3 M A G : Nat} (hc : constsOK CM3 M = true) {a : Nat → Nat}
    (hA : A = ∑ r ∈ Finset.range 64, a r * 2 ^ (1729 * r)) (ha : ∀ r < 64, a r < 2 ^ 399)
    {g : Nat → Nat → Nat}
    (hG : G = ∑ k ∈ Finset.range 133, ∑ l ∈ Finset.range 133, g k l * 2 ^ (1729 * k + 13 * l))
    (hg : ∀ k < 133, ∀ l < 133, g k l < 5) :
    mulC CM3 A G = ∑ t ∈ range (133 * 133), (if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) % 5 * 2 ^ (13 * t) := by
  obtain ⟨-, -, -, -, hT, -, hL, hH, -, hRM, -⟩ := CFSG.KS.Ord.consts_facts CFSG.KD.OrdHN.consts
  have hg' : ∀ k < 133, ∀ l < 133, g k l < 2 ^ 13 := fun k hk l hl =>
    Nat.lt_of_lt_of_le (hg k hk l hl) (by norm_num)
  have hU : ∑ k ∈ range 133, ((A >>> (3 * k)) &&& CM3) * ((G >>> (1729 * k)) &&& (2 ^ (13 * 133) - 1))
      = ∑ u ∈ range (133 * 133), (if u / 133 < 64 then
        ∑ k ∈ range 133, (a (u / 133) / 2 ^ (3 * k) % 8) * g k (u % 133) else 0) * 2 ^ (13 * u) := by
    rw [← lanes_U (fun k r => a r / 2 ^ (3 * k) % 8) g]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [lanes_col hc hA ha (Finset.mem_range.1 hk), lanes_rowG hG hg' (Finset.mem_range.1 hk)]
  have hFb : ∀ t < 133 * 133, (if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) ≤ 3724 := by
    intro t _
    split
    · exact lanes_F_le hg _ _ (Nat.mod_lt _ (by omega))
    · omega
  have hR := CFSG.KS.Ord.redP_pk (w := 13) (n := 133 * 133) (p := 5) (T := 9)
    (f := fun t => if t / 133 < 64 then
      ∑ k ∈ range 133, (a (t / 133) / 2 ^ (3 * k) % 8) * g k (t % 133) else 0) (by omega) hT
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
  unfold CFSG.KS.Ord.pk at hR hL hH
  beta_reduce at hR hL hH
  have hrec := lanes_mulC_rec A G CM3 CFSG.KD.OrdHN.RM (nat_lit 133)
  unfold mulC
  rw [hrec, hRM, hU, hL, hH, hR]

theorem fixAt_iff {T : Nat → Nat} {CM3 M V : Nat} (hc : constsOK CM3 M = true)
    (hV : CFSG.KS.Ord.Canon 5 133 13 V) (i : Nat) :
    fixAt T 464 CM3 M (trM V) i = true ↔ ordMat 5 133 13 1729 V *ᵥ xvec T i = 0 := by
  have hM : M = Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 399)) (nat_lit 1) := by
    unfold constsOK at hc
    exact Nat.eq_of_beq_eq_true ((CFSG.KS.bAnd_iff _ _).1 hc).2
  have hA : Nat.land (getRec T 464 i) M =
      ∑ r ∈ Finset.range 64, (if r = 0 then xv T i else 0) * 2 ^ (1729 * r) := by
    rw [Finset.sum_eq_single 0 (fun r _ hr => by rw [if_neg hr, Nat.zero_mul])
      (fun h => absurd (Finset.mem_range.2 (by omega)) h), if_pos rfl, Nat.mul_zero, Nat.pow_zero,
      Nat.mul_one, hM]
    change getRec T 464 i &&& ((1 <<< 399) - 1) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    unfold xv
    rw [fldW_eq, Nat.pow_zero, Nat.div_one]
  have hP := mulC_pkS hc hA (fun r _ => by split; exact lanes_xv_lt T i; exact Nat.two_pow_pos _)
    (G := trM V) (g := fun k l => ent13 V l k) (by rw [trM_eq]) (fun k hk l hl => canon_ent hV l hl k hk)
  unfold fixAt
  rw [Nat.beq_eq]
  change mulC CM3 (Nat.land (getRec T 464 i) M) (trM V) = 0 ↔ _
  rw [← lanes_zero_iff hV (xvec T i) (xe T i) (fun j _ => rfl), hP, Finset.sum_eq_zero_iff]
  constructor
  · intro h l hl
    have e := h l (Finset.mem_range.2 (by omega))
    rw [Nat.mul_eq_zero] at e
    rcases e with e | e
    · rw [Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl, if_pos (by omega)] at e
      simp only [↓reduceIte] at e
      exact e
    · exact absurd e (by positivity)
  · intro h t ht
    have ht' := Finset.mem_range.1 ht
    rw [Nat.mul_eq_zero]
    left
    split
    · by_cases h0 : t / 133 = 0
      · have htl : t < 133 := by omega
        rw [h0, Nat.mod_eq_of_lt htl]
        simp only [↓reduceIte]
        exact h t htl
      · simp [h0]
    · rfl

theorem sk_col {LW A : Nat} (h0 : 0 < LW) {u : Nat → Nat}
    (hA : A = ∑ r ∈ range 64, u r * 2 ^ (LW * r)) (hu : ∀ r < 64, u r < 2 ^ LW)
    {j : Nat} (hj : 3 * j + 3 ≤ LW) :
    (A >>> (3 * j)) &&& (7 * sOnes LW 64) = ∑ r ∈ range 64, (u r / 2 ^ (3 * j) % 8) * 2 ^ (LW * r) := by
  have h7 : ∀ r < 64, (7 : Nat) < 2 ^ LW := fun _ _ =>
    Nat.lt_of_lt_of_le (by norm_num : (7 : Nat) < 2 ^ 3) (Nat.pow_le_pow_right (by omega) (by omega))
  have FA : Fld LW (∑ r ∈ range 64, u r * 2 ^ (LW * r)) (fun t => if t < 64 then u t else 0) :=
    fld_pk hu
  have FC : Fld LW (∑ r ∈ range 64, 7 * 2 ^ (LW * r)) (fun t => if t < 64 then 7 else 0) :=
    fld_pk h7
  have hb : ∀ r < 64, u r / 2 ^ (3 * j) % 8 < 2 ^ LW := fun r _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
      (by rw [show (8 : Nat) = 2 ^ 3 by norm_num]; exact Nat.pow_le_pow_right (by omega) (by omega))
  have hC : 7 * sOnes LW 64 = ∑ r ∈ range 64, 7 * 2 ^ (LW * r) := by
    rw [sOnes_eq h0, Finset.mul_sum]
  rw [hC, hA]
  refine pk_of_fld h0 ?_ hb
  intro i b hbw
  rw [Nat.testBit_and, Nat.testBit_shiftRight, FC i b hbw]
  by_cases hi : i < 64
  · simp only [hi, ↓reduceIte]
    rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.testBit_two_pow_sub_one,
      show (8 : Nat) = 2 ^ 3 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases hb3 : b < 3
    · rw [show 3 * j + (LW * i + b) = LW * i + (b + 3 * j) by ring, FA i _ (by omega)]
      simp [hi, hb3]
    · simp [hb3]
  · simp [hi]

theorem sk_rec_add (x : Nat) (F : Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) x (fun k acc => Nat.add acc (F k)) n = x + ∑ k ∈ range n, F k
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ← sk_rec_add x F n]
    rfl

theorem sPre_eq {L RB Q LW NG W J GO : Nat} (h0 : 0 < LW) {v : Nat → Nat → Nat}
    (hA : ∀ g < NG, sLeafA L RB Q LW g = ∑ r ∈ range 64, v g r * 2 ^ (LW * r))
    (hv : ∀ g < NG, ∀ r < 64, v g r < 2 ^ LW)
    (hJ : ∀ g < NG, ∀ k < fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8,
      3 * fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 + 3 ≤ LW) :
    sPre L RB Q LW NG (7 * sOnes LW 64) W J GO = ∑ r ∈ range 64,
      (∑ g ∈ range NG, ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
        (v g r / 2 ^ (3 * fldW J (8 * (fldW GO (8 * g) 8 + k)) 8) % 8) *
          fldW W (LW * (fldW GO (8 * g) 8 + k)) LW) * 2 ^ (LW * r) := by
  unfold sPre
  refine lanes_rec_eq (N := NG) (S := fun n => ∑ r ∈ range 64,
      (∑ g ∈ range n, ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
        (v g r / 2 ^ (3 * fldW J (8 * (fldW GO (8 * g) 8 + k)) 8) % 8) *
          fldW W (LW * (fldW GO (8 * g) 8 + k)) LW) * 2 ^ (LW * r)) ?_ ?_ NG le_rfl
  · simp
  · intro g hg acc hacc
    rw [loopStrictN_eq, loopStrictN_eq]
    have e := sk_rec_add acc (fun k => CFSG.KC.Loop.strictN (Nat.add (fldW GO (Nat.mul 8 g) 8) k)
      (fun t => Nat.mul (Nat.land (Nat.shiftRight (sLeafA L RB Q LW g)
          (Nat.mul 3 (fldW J (Nat.mul 8 t) 8))) (Nat.mul 7 (sOnes LW 64)))
        (fldW W (Nat.mul LW t) LW))) (Nat.sub (fldW GO (Nat.mul 8 (Nat.succ g)) 8)
          (fldW GO (Nat.mul 8 g) 8))
    refine (Eq.trans ?_ e).trans ?_
    · congr 1
      funext k acc'
      simp only [loopStrictN_eq]
      rfl
    rw [hacc]
    have hk : ∀ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
        CFSG.KC.Loop.strictN (Nat.add (fldW GO (Nat.mul 8 g) 8) k)
          (fun t => Nat.mul (Nat.land (Nat.shiftRight (sLeafA L RB Q LW g)
            (Nat.mul 3 (fldW J (Nat.mul 8 t) 8))) (Nat.mul 7 (sOnes LW 64)))
          (fldW W (Nat.mul LW t) LW)) =
        ∑ r ∈ range 64, ((v g r / 2 ^ (3 * fldW J (8 * (fldW GO (8 * g) 8 + k)) 8) % 8) *
          fldW W (LW * (fldW GO (8 * g) 8 + k)) LW) * 2 ^ (LW * r) := by
      intro k hk
      rw [loopStrictN_eq]
      change ((sLeafA L RB Q LW g >>> (3 * fldW J (8 * (fldW GO (8 * g) 8 + k)) 8)) &&&
        (7 * sOnes LW 64)) * fldW W (LW * (fldW GO (8 * g) 8 + k)) LW = _
      rw [sk_col h0 (hA g hg) (hv g hg) (hJ g hg k (Finset.mem_range.1 hk)), Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    change _ + ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8), _ = _
    rw [Finset.sum_congr rfl hk, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_range_succ, Nat.add_mul]
    congr 1
    rw [Finset.sum_mul]

noncomputable def sLane (T : Nat → Nat) (W J GO b r : Nat) : Nat :=
  fldW (CFSG.KC.Ord.redP (nat_lit 13) (sOnes (nat_lit 13) (Nat.mul (nat_lit 64) 16))
      (Nat.shiftLeft (sOnes (nat_lit 13) (Nat.mul (nat_lit 64) 16)) (nat_lit 12)) (nat_lit 5)
      (nat_lit 9)
    (sPre (T b) (nat_lit 464) (Nat.div (Nat.mul (nat_lit 13) 16) (nat_lit 3)) (Nat.mul (nat_lit 13) 16)
      (Nat.div (Nat.add (nat_lit 132) (Nat.div (Nat.mul (nat_lit 13) 16) (nat_lit 3)))
        (Nat.div (Nat.mul (nat_lit 13) 16) (nat_lit 3)))
      (Nat.mul (nat_lit 7) (sOnes (Nat.mul (nat_lit 13) 16) (nat_lit 64))) W J GO))
    (Nat.mul (Nat.mul (nat_lit 13) 16) r) (Nat.mul (nat_lit 13) 16)

theorem sk_rec_sum (f : Nat → Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => CFSG.KC.Loop.strictN acc (fun a => Nat.add a (f i))) n = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← sk_rec_sum f n]
    exact strictN_eq' _ _

theorem sk_term (y : Nat) (f : Bool) (P : Prop) [Decidable P] (h1 : f = true ↔ P)
    (h2 : P → y = 0) :
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) f) (Nat.beq y (nat_lit 0)) =
      if P then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, h2 hP, h1.2 hP]
    rfl
  · rw [if_neg hP]
    cases hf : f
    · cases Nat.beq y 0 <;> rfl
    · exact absurd (h1.1 hf) hP

theorem fixLeafS_eq {T : Nat → Nat} {CM3 M V : Nat} (hc : constsOK CM3 M = true)
    (hV : Canon 5 133 13 V) {Q LW NG CMS SL SH W J GO b c : Nat} (hc64 : c ≤ 64)
    (hpre : ∀ r < c, ordMat 5 133 13 1729 V *ᵥ xvec T (64 * b + r) = 0 →
      fldW (CFSG.KC.Ord.redP 13 SL SH 5 9 (sPre (T b) 464 Q LW NG CMS W J GO)) (LW * r) LW = 0) :
    fixLeafS T 464 CM3 M (trM V) Q LW NG CMS SL SH W J GO b c = fixLeaf T 464 CM3 M [trM V] b c := by
  rw [fixLeaf_one hc hV hc64, Finset.card_filter]
  unfold fixLeafS
  rw [strictN_eq']
  refine (lanes_rec_add _ c).trans (Finset.sum_congr rfl fun r hr => ?_)
  have hi : Nat.add (Nat.shiftLeft b 6) r = 64 * b + r := by
    change b <<< 6 + r = _
    rw [Nat.shiftLeft_eq]
    ring
  have hfa : fixAt T 464 CM3 M (trM V) (Nat.add (Nat.shiftLeft b 6) r) = true ↔
      ordMat 5 133 13 1729 V *ᵥ xvec T (64 * b + r) = 0 := by
    have hx : xvec T (Nat.add (Nat.shiftLeft b 6) r) = xvec T (64 * b + r) := congrArg (xvec T) hi
    refine (fixAt_iff (T := T) hc hV (Nat.add (Nat.shiftLeft b 6) r)).trans ?_
    rw [hx]
  exact sk_term _ _ _ hfa (hpre r (Finset.mem_range.1 hr))

theorem fixSumS_eq {T : Nat → Nat} {CM3 M V : Nat} (hc : constsOK CM3 M = true)
    (hV : Canon 5 133 13 V) {W J GO lo : Nat}
    (hpre : ∀ b, ∀ r < hnxC b, ordMat 5 133 13 1729 V *ᵥ xvec T (64 * b + r) = 0 →
      sLane T W J GO b r = 0) :
    ∀ n, fixSumS T CM3 M (trM V) 16 W J GO lo n = fixSum T CM3 M (trM V) lo n := by
  intro n
  rw [fixSum_eq]
  unfold fixSumS
  rw [strictN_eq', strictN_eq', strictN_eq', strictN_eq', strictN_eq']
  exact (sk_rec_sum _ n).trans
    (Finset.sum_congr rfl fun i _ => fixLeafS_eq hc hV (hnxC_le _) (hpre _))

theorem pre_zero {T : Nat → Nat} {CM3 M V SC SD : Nat} (hc : constsOK CM3 M = true)
    (hV : Canon 5 133 13 V) {c : Nat → Nat}
    (hSC : SC = ∑ s ∈ range 64, c s * 2 ^ (1729 * s)) (hc399 : ∀ s < 64, c s < 2 ^ 399)
    (hSD : mulC CM3 SC V = SD) {jt : Nat → Nat → Nat} {w : Nat → Nat → Nat → Nat}
    {cnt : Nat → Nat} {NG : Nat}
    (hD1 : ∀ s < 16, ∀ j < 133, (∑ g ∈ range NG, ∑ k ∈ range (cnt g),
      if jt g k = j then w g k s else 0) % 5 = SD / 2 ^ (1729 * s + 13 * j) % 2 ^ 13)
    (hD2 : ∀ g < NG, ∀ k < cnt g, jt g k < 133) {i : Nat}
    (hx : ordMat 5 133 13 1729 V *ᵥ xvec T i = 0) {s : Nat} (hs : s < 16) :
    (∑ g ∈ range NG, ∑ k ∈ range (cnt g), xe T i (jt g k) * w g k s) % 5 = 0 := by
  have hz := (lanes_zero_iff hV (xvec T i) (xe T i) (fun j _ => rfl)).2 hx
  have hxe0 : ∀ k < 133, ((∑ j ∈ range 133, xe T i j * ent13 V k j : ℕ) : ZMod 5) = 0 :=
    fun k hk => by rw [← ZMod.natCast_mod, hz k hk, Nat.cast_zero]
  have hG := lanes_canon_eq hV.1
  have hSDe : ∀ j < 133, ((∑ g ∈ range NG, ∑ k ∈ range (cnt g),
      if jt g k = j then w g k s else 0 : ℕ) : ZMod 5) =
      ((∑ k ∈ range 133, (c s / 2 ^ (3 * k) % 8) * ent13 V k j : ℕ) : ZMod 5) := fun j hj => by
    rw [← ZMod.natCast_mod, hD1 s hs j hj, ← hSD,
      mulC_lane hc hSC hc399 hG (fun k hk l hl => canon_ent hV k hk l hl) s (by omega) j hj,
      ZMod.natCast_mod]
  have e1 : ∑ g ∈ range NG, ∑ k ∈ range (cnt g), xe T i (jt g k) * w g k s =
      ∑ j ∈ range 133, xe T i j * ∑ g ∈ range NG, ∑ k ∈ range (cnt g),
        if jt g k = j then w g k s else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (range 133) (jt g k), if_pos (Finset.mem_range.2
      (hD2 g (Finset.mem_range.1 hg) k (Finset.mem_range.1 hk)))]
  have e2 : ((∑ g ∈ range NG, ∑ k ∈ range (cnt g), xe T i (jt g k) * w g k s : ℕ) : ZMod 5) = 0 := by
    rw [e1, Nat.cast_sum, Finset.sum_congr rfl fun j hj => by
      rw [Nat.cast_mul, hSDe j (Finset.mem_range.1 hj)]]
    simp_rw [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k hk => ?_
    have := hxe0 k (Finset.mem_range.1 hk)
    rw [Nat.cast_sum] at this
    simp_rw [Nat.cast_mul] at this
    rw [← mul_zero ((c s / 2 ^ (3 * k) % 8 : ℕ) : ZMod 5), ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have := congrArg ZMod.val e2
  rwa [ZMod.val_natCast, ZMod.val_zero] at this

theorem sk_bits (x a b c : Nat) (h : b + c ≤ a) (d : Nat) :
    x / 2 ^ d % 2 ^ a / 2 ^ b % 2 ^ c = x / 2 ^ (d + b) % 2 ^ c := by
  rw [lanes_dm _ _ _ _ h, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem sk_bits8 (x a b : Nat) (h : b + 3 ≤ a) (d : Nat) :
    x / 2 ^ d % 2 ^ a / 2 ^ b % 8 = x / 2 ^ (d + b) % 8 :=
  sk_bits x a b 3 h d

private theorem sOnes_pk {w : Nat} (hw : 0 < w) (n : Nat) :
    sOnes w n = CFSG.KS.Ord.pk w n (fun _ => 1) := by
  rw [sOnes_eq hw]
  unfold CFSG.KS.Ord.pk
  simp

private theorem sOnes_pkH {w : Nat} (hw : 0 < w) (n : Nat) :
    sOnes w n <<< (w - 1) = CFSG.KS.Ord.pk w n (fun _ => 2 ^ (w - 1)) := by
  rw [sOnes_eq hw, Nat.shiftLeft_eq, Finset.sum_mul]
  unfold CFSG.KS.Ord.pk
  exact Finset.sum_congr rfl fun t _ => Nat.mul_comm _ _

theorem sLane_zeroV {T : Nat → Nat} {W J GO b r LW Q NG N SL SH CMS : Nat} (hr : r < 64)
    (hLW : LW = 208) (hQ : Q = 69) (hNG : NG = 2) (hN : N = 16 * 64) (hSL : SL = sOnes 13 N)
    (hSH : SH = sOnes 13 N <<< 12) (hCMS : CMS = 7 * sOnes LW 64)
    (hJ : ∀ g < 2, ∀ k < fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8,
      fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 < 69 ∧
        69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 < 133 ∧
        ∀ s < 16, W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13 < 5)
    (hcnt : ∑ g ∈ range 2, (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8) ≤ 146)
    (hF : ∀ s < 16, (∑ g ∈ range 2, ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
      xe T (64 * b + r) (69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8) *
        (W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13)) % 5 = 0) :
    fldW (CFSG.KC.Ord.redP 13 SL SH 5 9 (sPre (T b) 464 Q LW NG CMS W J GO)) (LW * r) LW = 0 := by
  subst hLW hQ hNG hN hSL hSH hCMS
  set v : Nat → Nat → Nat := fun g r' => T b / 2 ^ (464 * r' + 3 * 69 * g) % 2 ^ (3 * 69) with hvdef
  have hA : ∀ g < 2, sLeafA (T b) 464 69 208 g = ∑ r' ∈ range 64, v g r' * 2 ^ (208 * r') :=
    fun g _ => sLeafA_eq (by norm_num) (by norm_num) (by norm_num)
  have hv : ∀ g < 2, ∀ r' < 64, v g r' < 2 ^ 208 := fun g _ r' _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by omega))
  rw [sPre_eq (by norm_num) hA hv (fun g hg k hk => by have := (hJ g hg k hk).1; omega)]
  set tt : Nat → Nat → Nat := fun g k => fldW GO (8 * g) 8 + k with htt
  set cnt : Nat → Nat := fun g => fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8 with hcntd
  set w : Nat → Nat → Nat := fun t s => W / 2 ^ (208 * t + 13 * s) % 2 ^ 13 with hwd
  have hW : ∀ t, fldW W (208 * t) 208 = ∑ s ∈ range 16, w t s * 2 ^ (13 * s) := fun t => by
    have hlt : fldW W (208 * t) 208 < 2 ^ (13 * 16) := by
      rw [fldW_eq]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    refine (CFSG.KS.Ord.pk_lane (w := 13) (n := 16) (by norm_num) hlt).trans ?_
    unfold CFSG.KS.Ord.pk CFSG.KS.Ord.lane
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [fldW_eq, sk_bits _ _ _ _ (by have := Finset.mem_range.1 hs; omega)]
  set F : Nat → Nat → Nat := fun r' s => ∑ g ∈ range 2, ∑ k ∈ range (cnt g),
    (v g r' / 2 ^ (3 * fldW J (8 * tt g k) 8) % 8) * w (tt g k) s with hFd
  have hS : ∑ r' ∈ range 64, (∑ g ∈ range 2, ∑ k ∈ range (cnt g),
      (v g r' / 2 ^ (3 * fldW J (8 * tt g k) 8) % 8) * fldW W (208 * tt g k) 208) * 2 ^ (208 * r') =
      CFSG.KS.Ord.pk 13 (16 * 64) (fun u => F (u / 16) (u % 16)) := by
    rw [CFSG.KS.Ord.pk_rows]
    refine Finset.sum_congr rfl fun r' _ => ?_
    simp_rw [hW, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun g _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    rw [show (16 * r' + s) / 16 = r' by omega, show (16 * r' + s) % 16 = s by omega,
      show 13 * (16 * r' + s) = 208 * r' + 13 * s by ring, Nat.pow_add, hFd]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hS]
  have hFb : ∀ u < 16 * 64, F (u / 16) (u % 16) ≤ 4088 := fun u _ => by
    calc F (u / 16) (u % 16) ≤ ∑ g ∈ range 2, ∑ k ∈ range (cnt g), 28 :=
          Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun k hk => by
            have h1 := Nat.mod_lt (v g (u / 16) / 2 ^ (3 * fldW J (8 * tt g k) 8)) (show 8 > 0 by norm_num)
            have h2 : w (tt g k) (u % 16) < 5 :=
              (hJ g (Finset.mem_range.1 hg) k (Finset.mem_range.1 hk)).2.2 (u % 16)
                (Nat.mod_lt _ (by norm_num))
            exact Nat.mul_le_mul (show _ ≤ 7 by omega) (show _ ≤ 4 by omega) |>.trans (by norm_num)
      _ = 28 * ∑ g ∈ range 2, cnt g := by simp [Finset.mul_sum, Nat.mul_comm]
      _ ≤ 4088 := by
          have : ∑ g ∈ range 2, cnt g ≤ 146 := hcnt
          omega
  have hT : 5 * 2 ^ 9 ≤ 2 ^ (13 - 1) := by norm_num
  rw [sOnes_pkH (w := 13) (by norm_num), sOnes_pk (w := 13) (by norm_num),
    CFSG.KS.Ord.redP_pk (w := 13) (n := 16 * 64) (p := 5) (T := 9) (by omega) hT
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))
    (fun t ht => Nat.lt_of_le_of_lt (hFb t ht) (by norm_num))]
  have hz : ∀ s < 16, F r s % 5 = 0 := fun s hs => by
    refine (congrArg (· % 5) ?_).trans (hF s hs)
    rw [hFd]
    refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hJ1, hJ2, -⟩ := hJ g (Finset.mem_range.1 hg) k (Finset.mem_range.1 hk)
    have hJ1' : fldW J (8 * tt g k) 8 < 69 := hJ1
    refine congrArg (· * w (tt g k) s) ?_
    unfold xe
    rw [xv_leaf T b r hr, sk_bits8 (T b) 399 (3 * (69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8))
      (by omega) (464 * r), hvdef]
    beta_reduce
    rw [sk_bits8 (T b) (3 * 69) (3 * fldW J (8 * tt g k) 8) (by omega) (464 * r + 3 * 69 * g), htt]
    beta_reduce
    exact congrArg (fun e => T b / 2 ^ e % 8) (by ring)
  have FY := fld_pk (w := 13) (n := 16 * 64) (g := fun u => F (u / 16) (u % 16) % 5)
    fun t _ => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [fldW_eq]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.zero_testBit, Nat.testBit_mod_two_pow]
  by_cases hq : q < 208
  · rw [decide_eq_true hq, Bool.true_and, Nat.testBit_div_two_pow,
      show q + 208 * r = 13 * (16 * r + q / 13) + q % 13 by omega, FY _ _ (Nat.mod_lt _ (by norm_num))]
    beta_reduce
    rw [if_pos (by omega), show (16 * r + q / 13) / 16 = r by omega,
      show (16 * r + q / 13) % 16 = q / 13 by omega, hz _ (by omega), Nat.zero_testBit]
  · rw [decide_eq_false hq, Bool.false_and]

theorem sk_nmul (a x : Nat) : Nat.mul a x = a * x := rfl

theorem sk_shl (x k : Nat) : Nat.shiftLeft x k = x <<< k := rfl

theorem sLane_zero {T : Nat → Nat} {W J GO b r : Nat} (hr : r < 64)
    (hJ : ∀ g < 2, ∀ k < fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8,
      fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 < 69 ∧
        69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 < 133 ∧
        ∀ s < 16, W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13 < 5)
    (hcnt : ∑ g ∈ range 2, (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8) ≤ 146)
    (hF : ∀ s < 16, (∑ g ∈ range 2, ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
      xe T (64 * b + r) (69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8) *
        (W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13)) % 5 = 0) :
    sLane T W J GO b r = 0 :=
  sLane_zeroV (LW := Nat.mul 13 16) (Q := Nat.div (Nat.mul 13 16) 3)
    (NG := Nat.div (Nat.add 132 (Nat.div (Nat.mul 13 16) 3)) (Nat.div (Nat.mul 13 16) 3))
    (N := Nat.mul 64 16) (SL := sOnes 13 (Nat.mul 64 16))
    (SH := Nat.shiftLeft (sOnes 13 (Nat.mul 64 16)) 12)
    (CMS := Nat.mul 7 (sOnes (Nat.mul 13 16) 64)) hr rfl rfl rfl rfl rfl
    (sk_shl _ _) (sk_nmul _ _) hJ hcnt hF

theorem sk_shl1 (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n :=
  (Nat.shiftLeft_eq 1 n).trans (Nat.one_mul _)

theorem sk_letB (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem sk_rec2 (F : Nat → Nat → Nat) (c : Nat → Nat) : ∀ n,
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun g acc => Nat.rec (motive := fun _ => Nat) acc (fun k a => Nat.add a (F g k)) (c g)) n =
      ∑ g ∈ range n, ∑ k ∈ range (c g), F g k
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← sk_rec2 F c n]
    exact sk_rec_add _ _ _

theorem sk_nIf (a j w : Nat) :
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) w (Nat.beq a j) = if a = j then w else 0 := by
  cases hb : Nat.beq a j
  · have hne : a ≠ j := fun e => by
      rw [e, Nat.beq_refl] at hb
      cases hb
    rw [if_neg hne]
  · rw [if_pos (Nat.eq_of_beq_eq_true hb)]

theorem sColSum_eq (W J GO s j : Nat) : sColSum W J GO s j =
    ∑ g ∈ range 2, ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
      if 69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 = j then
        W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13 else 0 := by
  unfold sColSum
  refine (sk_rec2 (fun g k => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (fldW W (Nat.add (Nat.mul 208 (Nat.add (fldW GO (Nat.mul 8 g) 8) k)) (Nat.mul 13 s)) 13)
      (Nat.beq (Nat.add (Nat.mul 69 g) (fldW J (Nat.mul 8 (Nat.add (fldW GO (Nat.mul 8 g) 8) k)) 8))
        j)) (sCnt GO) 2).trans
    (Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun k _ => ?_)
  refine (sk_nIf _ _ _).trans ?_
  rw [fldW_eq W]
  rfl

theorem sk_and4 {a b c d : Bool} (h : Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false d c) b) a =
      true) : a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem sPreOK_parts {CM3 V W J GO SC SD : Nat} (h : sPreOK CM3 V W J GO SC SD = true) :
    sOKc SC = true ∧ sOKt W J GO = true ∧ sOKd W J GO SD = true ∧
      Nat.beq (mulC CM3 SC V) SD = true :=
  sk_and4 h

theorem sLane_of_ok {T : Nat → Nat} {CM3 M V W J GO SC SD : Nat} (hc : constsOK CM3 M = true)
    (hV : Canon 5 133 13 V) (h : sPreOK CM3 V W J GO SC SD = true) (b : Nat) :
    ∀ r < hnxC b, ordMat 5 133 13 1729 V *ᵥ xvec T (64 * b + r) = 0 → sLane T W J GO b r = 0 := by
  intro r hr hx
  obtain ⟨hc', ht', h6, h1⟩ := sPreOK_parts h
  unfold sOKc at hc'
  unfold sOKt at ht'
  unfold sOKd at h6
  obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 hc'
  obtain ⟨h4, h5⟩ := (CFSG.KS.bAnd_iff _ _).1 ht'
  have hSD : mulC CM3 SC V = SD := Nat.eq_of_beq_eq_true h1
  have hSC : SC < 2 ^ (1729 * 64) := by
    have := Eq.mp Nat.blt_eq h2
    rw [sk_shl1, sk_nmul] at this
    exact this
  have hc399 : ∀ s < 64, CFSG.KS.Ord.lane 1729 SC s < 2 ^ 399 := fun s hs => by
    have := Eq.mp Nat.blt_eq (CFSG.KS.allN_spec h3 s hs)
    rw [sk_shl1, fldW_eq, sk_nmul] at this
    exact this
  have hSC' : SC = ∑ s ∈ range 64, CFSG.KS.Ord.lane 1729 SC s * 2 ^ (1729 * s) :=
    CFSG.KS.Ord.pk_lane (by norm_num) hSC
  have hcnt : ∑ g ∈ range 2, (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8) ≤ 146 := by
    have := Nat.le_of_ble_eq_true h4
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    exact this
  have hJ : ∀ g < 2, ∀ k < fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8,
      fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 < 69 ∧
        69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 < 133 ∧
        ∀ s < 16, W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13 < 5 := by
    intro g hg k hk
    have ht := CFSG.KS.allN_spec (CFSG.KS.allN_spec h5 g hg) k hk
    unfold sTermOK at ht
    rw [sk_letB, sk_letB] at ht
    obtain ⟨t1, ht⟩ := (CFSG.KS.bAnd_iff _ _).1 ht
    obtain ⟨t2, t3⟩ := (CFSG.KS.bAnd_iff _ _).1 ht
    refine ⟨Eq.mp Nat.blt_eq t1, Eq.mp Nat.blt_eq t2, fun s hs => ?_⟩
    have := Eq.mp Nat.blt_eq (CFSG.KS.allN_spec t3 s hs)
    rwa [fldW_eq] at this
  have hD1 : ∀ s < 16, ∀ j < 133, (∑ g ∈ range 2,
      ∑ k ∈ range (fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8),
        if 69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8 = j then
          W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13 else 0) % 5 =
      SD / 2 ^ (1729 * s + 13 * j) % 2 ^ 13 := fun s hs j hj => by
    have := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec (CFSG.KS.allN_spec h6 s hs) j hj)
    rw [sColSum_eq, fldW_eq] at this
    exact this
  exact sLane_zero (Nat.lt_of_lt_of_le hr (hnxC_le b)) hJ hcnt fun s hs =>
    pre_zero (T := T) (NG := 2) (cnt := fun g => fldW GO (8 * (g + 1)) 8 - fldW GO (8 * g) 8)
      (jt := fun g k => 69 * g + fldW J (8 * (fldW GO (8 * g) 8 + k)) 8)
      (w := fun g k s => W / 2 ^ (208 * (fldW GO (8 * g) 8 + k) + 13 * s) % 2 ^ 13)
      hc hV hSC' hc399 hSD hD1 (fun g hg k hk => (hJ g hg k hk).2.1) hx hs

end CFSG.KS.SporSch.HNXP

end
