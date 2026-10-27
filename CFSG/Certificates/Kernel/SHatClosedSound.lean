module

public import Certificates.Data.Kernel.SHatClosedK
public import Certificates.Data.AS81SHatClosed
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.AxisPlane.Pop
import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.StdOdd.RootOrbitSound
import all CFSG.Certificates.Kernel.Spor.PEnumSound
import Mathlib.Tactic.Ring
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
import CFSG.Certificates.Kernel.BfsPinSound

set_option exponentiation.threshold 400

namespace CFSG.KC.SHatClosed

open CFSG.KC.AxisPlane (lanes cnt testBit_lanes lanes_add cnt_succ cnt_lt cnt_le lanes_lt sum_cnt
  cnt_zero)

theorem lanes_succ (w : Nat) (f : Nat → Nat) (n : Nat) :
    lanes w f (n + 1) = lanes w f n + 2 ^ (w * n) * f n := rfl

theorem lanes_head (w : Nat) (f : Nat → Nat) : ∀ m,
    lanes w f (m + 1) = f 0 + 2 ^ w * lanes w (fun i => f (i + 1)) m
  | 0 => by simp [lanes]
  | m + 1 => by
    rw [lanes_succ w f (m + 1), lanes_head w f m, lanes_succ w (fun i => f (i + 1)) m]
    have e : 2 ^ (w * (m + 1)) = 2 ^ w * 2 ^ (w * m) := by
      rw [← Nat.pow_add]
      congr 1
      ring
    rw [e]
    ring

theorem lanes_pad (w : Nat) (f : Nat → Nat) (m : Nat) (h : f m = 0) :
    lanes w f (m + 1) = lanes w f m := by
  rw [lanes_succ, h, Nat.mul_zero, Nat.add_zero]

theorem lanes_pair (w : Nat) (f : Nat → Nat) : ∀ n,
    lanes w f (2 * n) = lanes (2 * w) (fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, lanes_succ w f (2 * n + 1),
      lanes_succ w f (2 * n), lanes_pair w f n, lanes_succ (2 * w) _ n]
    have e1 : 2 ^ (w * (2 * n + 1)) = 2 ^ (2 * w * n) * 2 ^ w := by
      rw [← Nat.pow_add]
      congr 1
      ring
    have e2 : 2 ^ (w * (2 * n)) = 2 ^ (2 * w * n) := by
      congr 1
      ring
    rw [e1, e2]
    ring

theorem lanes_shr {w : Nat} {f : Nat → Nat} (m : Nat) (h0 : f 0 < 2 ^ w) :
    Nat.shiftRight (lanes w f (m + 1)) w = lanes w (fun i => f (i + 1)) m := by
  change lanes w f (m + 1) >>> w = _
  rw [Nat.shiftRight_eq_div_pow, lanes_head, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
    Nat.div_eq_of_lt h0, Nat.zero_add]

theorem lanes_even {w n : Nat} (hw : 0 < w) {v : Nat → Nat} (hv : ∀ i, v i < 2 ^ w) {K : Nat}
    (hK : ∀ q, K.testBit q = (decide (q < 2 * w * n) && decide (q % (2 * w) < w))) :
    Nat.land (lanes w v (2 * n)) K = lanes (2 * w) (fun i => v (2 * i)) n := by
  have hv2 : ∀ i < n, v (2 * i) < 2 ^ (2 * w) := fun i _ =>
    Nat.lt_of_lt_of_le (hv _) (Nat.pow_le_pow_right (by decide) (by omega))
  apply Nat.eq_of_testBit_eq
  intro q
  change (lanes w v (2 * n) &&& K).testBit q = _
  rw [Nat.testBit_and, testBit_lanes hw _ (fun i _ => hv i), hK,
    testBit_lanes (by omega) _ hv2]
  have hk := Nat.div_add_mod q (2 * w)
  generalize q / (2 * w) = k at hk
  have hr : q % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
  generalize q % (2 * w) = r at hk hr
  subst hk
  have e0 : w * (2 * n) = 2 * w * n := by ring
  rw [e0]
  by_cases hrw : r < w
  · have e1 : (2 * w * k + r) / w = 2 * k := by
      rw [show 2 * w * k + r = r + w * (2 * k) by ring, Nat.add_mul_div_left _ _ hw,
        Nat.div_eq_of_lt hrw, Nat.zero_add]
    have e2 : (2 * w * k + r) % w = r := by
      rw [show 2 * w * k + r = r + w * (2 * k) by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hrw]
    rw [e1, e2, decide_eq_true hrw]
    cases decide (2 * w * k + r < 2 * w * n) <;> simp
  · have hz : (v (2 * k)).testBit r = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hv _) (Nat.pow_le_pow_right (by decide)
        (by omega)))
    simp [hrw, hz]

theorem lanes_fold {w n : Nat} (hw : 0 < w) {v : Nat → Nat} (hv : ∀ i, v i + v (i + 1) < 2 ^ w)
    (hpad : v (2 * n) = 0) {K : Nat}
    (hK : ∀ q, K.testBit q = (decide (q < 2 * w * n) && decide (q % (2 * w) < w))) :
    Nat.land (Nat.add (lanes w v (2 * n)) (Nat.shiftRight (lanes w v (2 * n)) w)) K =
      lanes (2 * w) (fun i => v (2 * i) + v (2 * i + 1)) n := by
  have h0 : v 0 < 2 ^ w := by have := hv 0; omega
  have hs : Nat.shiftRight (lanes w v (2 * n)) w = lanes w (fun i => v (i + 1)) (2 * n) := by
    rw [← lanes_pad w v (2 * n) hpad, lanes_shr _ h0]
  rw [hs]
  change Nat.land (lanes w v (2 * n) + lanes w (fun i => v (i + 1)) (2 * n)) K = _
  rw [lanes_add, lanes_even hw hv hK]

theorem lanes_zero (w : Nat) : ∀ m, lanes w (fun _ => 0) m = 0
  | 0 => rfl
  | m + 1 => by rw [lanes_succ, lanes_zero w m, Nat.mul_zero]

def gHead (f : Nat → Nat) (i : Nat) : Nat := f (i + 1) + if i = 0 then f 0 else 0

theorem lanes_mulH {w : Nat} (hw : 0 < w) : ∀ n (f : Nat → Nat),
    (∀ s < n, ∑ i ∈ Finset.range (s + 1), f i < 2 ^ w) →
    (lanes w f n * lanes w (fun _ => 1) n) % 2 ^ (w * n) =
      lanes w (fun s => ∑ i ∈ Finset.range (s + 1), f i) n
  | 0, _, _ => by simp [lanes]
  | 1, f, hP => by
    have hf0 : f 0 < 2 ^ w := by simpa using hP 0 (by omega)
    simp [lanes, Nat.mod_eq_of_lt hf0]
  | m + 1 + 1, f, hP => by
    have hf0 : f 0 < 2 ^ w := by simpa using hP 0 (by omega)
    have hgl : lanes w (gHead f) (m + 1) = f 0 + lanes w (fun i => f (i + 1)) (m + 1) := by
      have e := lanes_add w (fun i => f (i + 1)) (fun i => if i = 0 then f 0 else 0) (m + 1)
      change _ = lanes w (gHead f) (m + 1) at e
      rw [← e, lanes_head w (fun i => if i = 0 then f 0 else 0) m]
      simp [lanes_zero, Nat.add_comm]
    have hPg : ∀ s, ∑ i ∈ Finset.range (s + 1), gHead f i =
        ∑ i ∈ Finset.range (s + 1 + 1), f i := by
      intro s
      unfold gHead
      rw [Finset.sum_add_distrib, Finset.sum_range_succ' f (s + 1)]
      simp
    have ih := lanes_mulH hw (m + 1) (gHead f) fun s hs => by rw [hPg]; exact hP (s + 1) (by omega)
    simp only [hPg] at ih
    have hH : lanes w (fun _ => 1) (m + 1 + 1) = 1 + 2 ^ w * lanes w (fun _ => 1) (m + 1) :=
      lanes_head w _ _
    have hE : 1 + 2 ^ w * lanes w (fun _ => 1) (m + 1) =
        lanes w (fun _ => 1) (m + 1) + 2 ^ (w * (m + 1)) := by
      rw [← hH, lanes_succ, Nat.mul_one]
    have eprod : lanes w f (m + 1 + 1) * lanes w (fun _ => 1) (m + 1 + 1) =
        f 0 + 2 ^ w * (lanes w (gHead f) (m + 1) * lanes w (fun _ => 1) (m + 1) +
          2 ^ (w * (m + 1)) * lanes w (fun i => f (i + 1)) (m + 1)) := by
      rw [hgl, lanes_head w f (m + 1), hH]
      calc (f 0 + 2 ^ w * lanes w (fun i => f (i + 1)) (m + 1)) *
            (1 + 2 ^ w * lanes w (fun _ => 1) (m + 1))
          = f 0 + 2 ^ w * (f 0 * lanes w (fun _ => 1) (m + 1)) +
            2 ^ w * (lanes w (fun i => f (i + 1)) (m + 1) *
              (1 + 2 ^ w * lanes w (fun _ => 1) (m + 1))) := by ring
        _ = _ := by rw [hE]; ring
    rw [eprod, show w * (m + 1 + 1) = w + w * (m + 1) by ring, Nat.pow_add, Nat.mod_mul,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf0,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hf0, Nat.zero_add,
      Nat.add_mul_mod_self_left, ih,
      lanes_head w (fun s => ∑ i ∈ Finset.range (s + 1), f i) (m + 1)]
    simp

theorem cnt_pad {x s i : Nat} (hx : x < 2 ^ 320) (hi : 320 ≤ 2 ^ s * i) : cnt x s i = 0 := by
  unfold cnt
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
    (by omega)))]
  rfl

theorem bits_lanes {x : Nat} (hx : x < 2 ^ 320) : x = lanes 1 (cnt x 0) 320 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_lanes Nat.one_pos _ (fun i _ => cnt_lt x 0 i), Nat.div_one, Nat.mod_one, cnt_zero,
    Nat.one_mul]
  by_cases hq : q < 320
  · rw [decide_eq_true hq, Bool.true_and]
    cases x.testBit q <;> rfl
  · rw [decide_eq_false hq, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
      (by omega)))

theorem mask_spec {L n c K : Nat} (hL : 0 < L) (hc : c < 2 ^ L) (k : Nat) (hck : c = 2 ^ k - 1)
    (hK : K = c * ((2 ^ (L * n) - 1) / (2 ^ L - 1))) (q : Nat) :
    K.testBit q = (decide (q < L * n) && decide (q % L < k)) := by
  rw [hK, CFSG.KC.Benes.testBit_mul_div hL rfl hc, hck, Nat.testBit_two_pow_sub_one]

theorem sum_toNat_filter (f : Nat → Bool) : ∀ n,
    ∑ j ∈ Finset.range n, (f j).toNat = ((List.range n).filter f).length
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_toNat_filter f n, List.range_succ, List.filter_append,
      List.length_append]
    cases h : f n <;> simp [h]

theorem pop_gen {m1 m2 m4 m8 H : Nat}
    (h1 : ∀ q, m1.testBit q = (decide (q < 2 * 1 * 160) && decide (q % (2 * 1) < 1)))
    (h2 : ∀ q, m2.testBit q = (decide (q < 2 * 2 * 80) && decide (q % (2 * 2) < 2)))
    (h4 : ∀ q, m4.testBit q = (decide (q < 2 * 4 * 40) && decide (q % (2 * 4) < 4)))
    (h8 : ∀ q, m8.testBit q = (decide (q < 2 * 8 * 20) && decide (q % (2 * 8) < 8)))
    (hH : H = lanes 16 (fun _ => 1) 20) {x : Nat} (hx : x < 2 ^ 320) :
    Nat.land (Nat.shiftRight (Nat.mul (
      Nat.land (Nat.add
        (Nat.land (Nat.add
          (Nat.add (Nat.land (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) m2)
            (Nat.land (Nat.shiftRight (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) 2) m2))
          (Nat.shiftRight (Nat.add (Nat.land (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) m2)
            (Nat.land (Nat.shiftRight (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) 2) m2)) 4))
          m4)
        (Nat.shiftRight (Nat.land (Nat.add
          (Nat.add (Nat.land (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) m2)
            (Nat.land (Nat.shiftRight (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) 2) m2))
          (Nat.shiftRight (Nat.add (Nat.land (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) m2)
            (Nat.land (Nat.shiftRight (Nat.sub x (Nat.land (Nat.shiftRight x 1) m1)) 2) m2)) 4))
          m4) 8)) m8) H) 304) 65535 =
      ((List.range 320).filter x.testBit).length := by
  have hb : ∀ i, cnt x 0 i < 2 ^ 1 := fun i => cnt_lt x 0 i
  have hx1 : x = lanes 2 (cnt x 1) 160 + lanes 2 (fun i => cnt x 0 (2 * i + 1)) 160 := by
    rw [lanes_add]
    conv_lhs => rw [bits_lanes hx, show (320 : Nat) = 2 * 160 by rfl, lanes_pair]
    congr 1
    funext i
    rw [cnt_succ]
    ring
  have hB1 : Nat.land (Nat.shiftRight x 1) m1 = lanes 2 (fun i => cnt x 0 (2 * i + 1)) 160 := by
    have e : Nat.shiftRight x 1 = lanes 1 (fun i => cnt x 0 (i + 1)) 320 := by
      have e0 := lanes_shr (w := 1) (f := cnt x 0) 320 (hb 0)
      rw [lanes_pad 1 (cnt x 0) 320 (cnt_pad (s := 0) (i := 320) hx (by simp)), ← bits_lanes hx]
        at e0
      exact e0
    rw [e]
    exact lanes_even (n := 160) Nat.one_pos (fun i => hb (i + 1)) h1
  have hA : Nat.sub x (Nat.land (Nat.shiftRight x 1) m1) = lanes 2 (cnt x 1) 160 := by
    rw [hB1]
    change x - _ = _
    omega
  rw [hA]
  have hB : Nat.add (Nat.land (lanes 2 (cnt x 1) 160) m2)
      (Nat.land (Nat.shiftRight (lanes 2 (cnt x 1) 160) 2) m2) = lanes 4 (cnt x 2) 80 := by
    have hc1 : ∀ i, cnt x 1 i < 2 ^ 2 := fun i => cnt_lt x 1 i
    have e1 : Nat.land (lanes 2 (cnt x 1) 160) m2 = lanes (2 * 2) (fun i => cnt x 1 (2 * i)) 80 :=
      lanes_even (n := 80) (by decide) hc1 h2
    have e2 :
        Nat.shiftRight (lanes 2 (cnt x 1) 160) 2 = lanes 2 (fun i => cnt x 1 (i + 1)) 160 := by
      rw [← lanes_pad 2 (cnt x 1) 160 (cnt_pad (s := 1) (i := 160) hx (by simp)),
        lanes_shr 160 (hc1 0)]
    have e3 : Nat.land (lanes 2 (fun i => cnt x 1 (i + 1)) 160) m2 =
        lanes (2 * 2) (fun i => cnt x 1 (2 * i + 1)) 80 :=
      lanes_even (n := 80) (by decide) (fun i => hc1 (i + 1)) h2
    change Nat.land (lanes 2 (cnt x 1) 160) m2 +
      Nat.land (Nat.shiftRight (lanes 2 (cnt x 1) 160) 2) m2 = _
    rw [e2, e1, e3, lanes_add]
    congr 1
    funext i
    exact (cnt_succ x 1 i).symm
  rw [hB]
  have hC : Nat.land (Nat.add (lanes 4 (cnt x 2) 80) (Nat.shiftRight (lanes 4 (cnt x 2) 80) 4)) m4
      = lanes 8 (cnt x 3) 40 := by
    have := lanes_fold (w := 4) (n := 40) (by decide) (v := cnt x 2)
      (fun i => Nat.lt_of_le_of_lt (Nat.add_le_add (cnt_le x 2 i) (cnt_le x 2 (i + 1))) (by decide))
      (cnt_pad hx (by simp)) h4
    refine this.trans ?_
    congr 1
    funext i
    exact (cnt_succ x 2 i).symm
  rw [hC]
  have hD : Nat.land (Nat.add (lanes 8 (cnt x 3) 40) (Nat.shiftRight (lanes 8 (cnt x 3) 40) 8)) m8
      = lanes 16 (cnt x 4) 20 := by
    have := lanes_fold (w := 8) (n := 20) (by decide) (v := cnt x 3)
      (fun i => Nat.lt_of_le_of_lt (Nat.add_le_add (cnt_le x 3 i) (cnt_le x 3 (i + 1))) (by decide))
      (cnt_pad hx (by simp)) h8
    refine this.trans ?_
    congr 1
    funext i
    exact (cnt_succ x 3 i).symm
  rw [hD, hH]
  have hP : ∀ s < 20, ∑ i ∈ Finset.range (s + 1), cnt x 4 i < 2 ^ 16 := by
    intro s hs
    calc ∑ i ∈ Finset.range (s + 1), cnt x 4 i ≤ ∑ _i ∈ Finset.range (s + 1), 16 :=
          Finset.sum_le_sum fun i _ => cnt_le x 4 i
      _ = (s + 1) * 16 := by simp
      _ < 2 ^ 16 := by
        rw [show (2 : Nat) ^ 16 = 65536 by rfl]
        omega
  have hM := lanes_mulH (w := 16) (by decide) 20 (cnt x 4) hP
  have hT : (lanes 16 (fun s => ∑ i ∈ Finset.range (s + 1), cnt x 4 i) 20) / 2 ^ (16 * 19) =
      ∑ i ∈ Finset.range 20, cnt x 4 i := by
    rw [lanes_succ, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (lanes_lt 19 fun s hs => hP s (by omega)), Nat.zero_add]
  have hS : ∑ i ∈ Finset.range 20, cnt x 4 i = ((List.range 320).filter x.testBit).length := by
    rw [sum_cnt, show 2 ^ 4 * 20 = 320 by rfl, sum_toNat_filter]
  rw [← hS, ← hT, ← hM]
  change Nat.land (Nat.shiftRight (lanes 16 (cnt x 4) 20 * lanes 16 (fun _ => 1) 20) 304) 65535 = _
  generalize lanes 16 (cnt x 4) 20 * lanes 16 (fun _ => 1) 20 = y
  apply Nat.eq_of_testBit_eq
  intro q
  change ((y >>> 304) &&& 65535).testBit q = (y % 2 ^ (16 * 20) / 2 ^ (16 * 19)).testBit q
  rw [Nat.testBit_and, Nat.testBit_shiftRight, show (65535 : Nat) = 2 ^ 16 - 1 by rfl,
    Nat.testBit_two_pow_sub_one, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    Nat.testBit_mod_two_pow]
  by_cases hq : q < 16
  · simp [hq, show 304 + q < 16 * 20 by omega]
  · simp [hq, show ¬ 304 + q < 16 * 20 by omega]

theorem popK_eq {x : Nat} (hx : x < 2 ^ 320) :
    popK x = ((List.range 320).filter x.testBit).length := by
  unfold popK
  simp only [CFSG.KC.BfsPin.strictN_app]
  refine pop_gen (fun q => mask_spec (L := 2) (n := 160) (c := 1) (by decide) (by decide) 1 rfl
    (by norm_num) q)
    (fun q => mask_spec (L := 4) (n := 80) (c := 3) (by decide) (by decide) 2 rfl (by norm_num) q)
    (fun q => mask_spec (L := 8) (n := 40) (c := 15) (by decide) (by decide) 4 rfl (by norm_num) q)
    (fun q => mask_spec (L := 16) (n := 20) (c := 255) (by decide) (by decide) 8 rfl
      (by norm_num) q)
    (by norm_num [lanes]) hx

theorem filter_bits_ext {x K K' : Nat} (hx : x < 2 ^ K) (h : K ≤ K') :
    ((List.range K').filter x.testBit).length = ((List.range K).filter x.testBit).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.filter_append, List.length_append]
  have e : (List.map (fun i => K + i) (List.range d)).filter x.testBit = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide)
      (by omega)))]
    decide
  rw [e]
  rfl

theorem popK_count {x K : Nat} (h320 : x < 2 ^ 320) (hK : x < 2 ^ K) :
    popK x = ((List.range K).filter x.testBit).length := by
  rw [popK_eq h320]
  rcases le_total K 320 with h | h
  · exact filter_bits_ext hK h
  · exact (filter_bits_ext h320 h).symm

end CFSG.KC.SHatClosed

public section

namespace CFSG.KC.SHatClosed

open CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.SHatClosed
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] def f1G (inv : Array Tab) : Bool := inv.all fun t => fixCount t == 16

@[expose] def cmG (inv : Array Tab) (i j : Nat) : Bool :=
  ((inv.map fun a => inv.map fun b => comp 64 a b == comp 64 b a)[i]!)[j]!

@[expose] def centIdxG (inv : Array Tab) : Array (Array Nat) :=
  (Array.range inv.size).map fun i => (Array.range inv.size).filter fun j => cmG inv i j

@[expose] def f2G (inv : Array Tab) : Bool :=
  allBelow inv.size fun i =>
    let a := inv[i]!
    let ci := (centIdxG inv)[i]!
    ci.all fun j =>
      inv[j]! == a ||
        (let s₂ := span2 a inv[j]!
         ci.all fun k =>
           !(cmG inv j k) || s₂.contains inv[k]! ||
             (let s₃ := span3 a inv[j]! inv[k]!
              ci.all fun l =>
                !(cmG inv j l && cmG inv k l) || s₃.contains inv[l]! ||
                  (ci.filter fun m => cmG inv j m && cmG inv k m && cmG inv l m).size == 15))

@[expose] def f3G (inv : Array Tab) : Bool :=
  allBelow inv.size fun i =>
    let a := inv[i]!
    let ci := (centIdxG inv)[i]!
    ci.all fun j =>
      inv[j]! == a ||
        (let s₂ := span2 a inv[j]!
         ci.all fun k =>
           !(cmG inv j k) || s₂.contains inv[k]! ||
             (let s₃ := span3 a inv[j]! inv[k]!
              ci.all fun l =>
                !(cmG inv j l && cmG inv k l) || s₃.contains inv[l]! ||
                  fixCount4 a inv[j]! inv[k]! inv[l]! == 2))

end CFSG.KC.SHatClosed

end

namespace CFSG.KC.SHatClosed

open CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.SHatClosed
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.KLie.CT (pw2)

theorem pw2_eq (k : Nat) : pw2 k = 2 ^ k := by
  change 1 <<< k = 2 ^ k
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_lor (a b q : Nat) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem testBit_land (a b q : Nat) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem land_pw2_eq_zero {x k : Nat} (h : x.testBit k = false) : Nat.land x (pw2 k) = 0 :=
  Nat.eq_of_testBit_eq fun q => by
    rw [testBit_land, pw2_eq, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases e : k = q
    · subst e
      rw [h]
      rfl
    · simp [e]

theorem hasB_eq (x k : Nat) : hasB x k = x.testBit k := by
  unfold hasB
  cases h : x.testBit k
  · rw [land_pw2_eq_zero h]
    rfl
  · refine Nat.blt_eq.mpr (Nat.pos_of_ne_zero fun e => ?_)
    have := testBit_land x (pw2 k) k
    rw [e, Nat.zero_testBit, h, pw2_eq, Nat.testBit_two_pow] at this
    simp at this

theorem beq_land_pw2 (x k : Nat) : Nat.beq (Nat.land x (pw2 k)) 0 = !x.testBit k := by
  cases h : x.testBit k
  · rw [land_pw2_eq_zero h]
    rfl
  · have := hasB_eq x k
    rw [h] at this
    unfold hasB at this
    generalize Nat.land x (pw2 k) = y at this
    cases y
    · exact absurd this (by decide)
    · rfl

theorem testBit_sub_land (B s l : Nat) :
    (Nat.sub B (Nat.land B s)).testBit l = (B.testBit l && !s.testBit l) := by
  change (B - (B &&& s)).testBit l = _
  rw [CFSG.KS.StdOdd.Orbit.sub_land_eq, Nat.testBit_xor, Nat.testBit_and]
  cases B.testBit l <;> cases s.testBit l <;> rfl

theorem lt_of_shr {x M : Nat} (h : Nat.shiftRight x M = 0) : x < 2 ^ M := by
  change x >>> M = 0 at h
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos M)).1 h

theorem l320_lt (x t : Nat) : l320 x t < 2 ^ 320 := by
  unfold l320
  change (x >>> (320 * t)) &&& (2 ^ 320 - 1) < 2 ^ 320
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

noncomputable def scanF (p : Nat → Bool) (mt : Nat → Nat → Bool) (i s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 0,
    nIf(p i, nIf(Nat.blt (nat_lit 1) s,
      nIf(mt (Nat.sub s (nat_lit 2)) i, Nat.sub s (nat_lit 1), nat_lit 0), nat_lit 0), s))

theorem scanF_eq (p : Nat → Bool) (mt : Nat → Nat → Bool) (i s : Nat) :
    scanF p mt i s = if s = 0 then 0 else if p i = true then
      (if 1 < s then (if mt (s - 2) i = true then s - 1 else 0) else 0) else s := by
  unfold scanF
  simp only [nIf_ite, Nat.beq_eq, Nat.blt_eq]
  rfl

theorem foldr_scanF_zero (p : Nat → Bool) (mt : Nat → Nat → Bool) :
    ∀ l : List Nat, l.foldr (scanF p mt) 0 = 0
  | [] => rfl
  | a :: l => by
    rw [List.foldr_cons, foldr_scanF_zero p mt l, scanF_eq]
    simp

theorem scan_spec {p : Nat → Bool} {mt : Nat → Nat → Bool} {g : Nat → Nat}
    (hmt : ∀ t k, mt t k = true → g t = k) : ∀ N M,
    (List.range N).foldr (scanF p mt) (M + 1) = 1 →
      (List.range N).filter p = (List.range M).map g ∧ ∀ t < M, mt t (g t) = true
  | 0, M, h => by
    have e : M = 0 := by
      change M + 1 = 1 at h
      omega
    subst e
    exact ⟨rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  | N + 1, M, h => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, scanF_eq,
      ite_eq_right (Nat.add_one_ne_zero M)] at h
    rw [List.range_succ, List.filter_append]
    by_cases hp : p N = true
    · rw [ite_eq_left hp] at h
      by_cases h1 : 1 < M + 1
      · rw [ite_eq_left h1] at h
        by_cases hm : mt (M + 1 - 2) N = true
        · rw [ite_eq_left hm] at h
          obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
          have e1 : M' + 1 + 1 - 2 = M' := by omega
          have e2 : M' + 1 + 1 - 1 = M' + 1 := by omega
          rw [e1] at hm
          rw [e2] at h
          obtain ⟨hf, hx⟩ := scan_spec hmt N M' h
          have hg := hmt _ _ hm
          refine ⟨?_, fun t ht => ?_⟩
          · rw [hf, List.range_succ, List.map_append]
            simp [hp, hg]
          · rcases Nat.lt_or_ge t M' with a | a
            · exact hx t a
            · have e : t = M' := by omega
              subst e
              rw [hg]
              exact hm
        · rw [ite_eq_right hm, foldr_scanF_zero] at h
          exact absurd h (by decide)
      · rw [ite_eq_right h1, foldr_scanF_zero] at h
        exact absurd h (by decide)
    · rw [ite_eq_right hp] at h
      obtain ⟨hf, hx⟩ := scan_spec hmt N M h
      refine ⟨?_, hx⟩
      rw [hf]
      simp [hp]

theorem invIdx_spec {N M : Nat} {T I : Nat → Nat} (h : invIdxK N M T I = true) :
    (List.range N).filter (fun i => invK (pidn 64 7) (T i)) = (List.range M).map I := by
  unfold invIdxK at h
  rw [strictN_app, CFSG.KS.Raw.Orb.foldN_eq] at h
  exact (scan_spec (g := I) (fun t k e => Nat.eq_of_beq_eq_true e) N M
    (Nat.eq_of_beq_eq_true h)).1

theorem ciStep_eq (CM FX : Nat → Nat) (r cx cc fc : Nat) :
    ciStep CM FX r cx cc fc = scanF (hasB r) (fun t k =>
      bAnd(Nat.beq (f9 cx t) k, bAnd(Nat.beq (l320 cc t) (CM k), Nat.beq (l64 fc t) (FX k)))) := by
  funext k s
  unfold ciStep scanF
  rw [strictN_app]

theorem ci_spec {M i : Nat} {CM FX CN CIX CMC FXC : Nat → Nat}
    (h : ciK M CM FX CN CIX CMC FXC i = true) :
    (List.range M).filter (hasB (CM i)) = (List.range (CN i)).map (f9 (CIX i)) ∧
      ∀ t < CN i, l320 (CMC i) t = CM (f9 (CIX i) t) ∧ l64 (FXC i) t = FX (f9 (CIX i) t) := by
  unfold ciK at h
  simp only [strictB_app] at h
  rw [ciStep_eq, CFSG.KS.Raw.Orb.foldN_eq] at h
  obtain ⟨h1, h2⟩ := scan_spec (g := f9 (CIX i)) (fun t k e => by
    rw [bAnd_iff] at e
    exact Nat.eq_of_beq_eq_true e.1) M (CN i) (Nat.eq_of_beq_eq_true h)
  refine ⟨h1, fun t ht => ?_⟩
  have e := h2 t ht
  rw [bAnd_iff, bAnd_iff] at e
  exact ⟨Nat.eq_of_beq_eq_true e.2.1, Nat.eq_of_beq_eq_true e.2.2⟩

theorem row_spec {M j : Nat} {V CM FX PTR : Nat → Nat} (h : rowK M V CM FX PTR j = true) :
    FX j = fixK (V j) ∧ Nat.shiftRight (CM j) M = 0 ∧ ∀ k < M,
      (hasB (CM j) k = true ↔ pc (V j) (V k) = pc (V k) (V j)) ∧
      (pc (V j) (V k) = pc (V k) (V j) → k ≠ j →
        f9 (PTR j) k < M ∧ V (f9 (PTR j) k) = pc (V j) (V k)) := by
  unfold rowK at h
  simp only [strictB_app] at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun k hk => ?_⟩
  have e := allN_spec h3 k hk
  cases hb : Nat.beq (pc (V j) (V k)) (pc (V k) (V j))
  · have hc : pc (V j) (V k) ≠ pc (V k) (V j) := fun e' => by
      rw [Nat.beq_eq.mpr e'] at hb
      exact absurd hb (by decide)
    rw [hb] at e
    dsimp only at e
    have hr : hasB (CM j) k = false := by
      cases h' : hasB (CM j) k
      · rfl
      · rw [h'] at e
        dsimp only at e
        exact absurd e (by decide)
    rw [hr]
    exact ⟨⟨fun e' => absurd e' (by decide), fun e' => absurd e' hc⟩, fun e' => absurd e' hc⟩
  · have hc : pc (V j) (V k) = pc (V k) (V j) := Nat.eq_of_beq_eq_true hb
    rw [hb] at e
    dsimp only at e
    rw [bAnd_iff] at e
    refine ⟨⟨fun _ => hc, fun _ => e.1⟩, fun _ hkj => ?_⟩
    have hkb : Nat.beq k j = false := by
      cases h' : Nat.beq k j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') hkj
    have e2 := e.2
    rw [hkb] at e2
    dsimp only at e2
    rw [bAnd_iff] at e2
    exact ⟨Nat.blt_eq.mp e2.1, Nat.eq_of_beq_eq_true e2.2⟩

theorem foldr_bits (c : Nat → Bool) (q : Nat) : ∀ L : List Nat,
    (L.foldr (fun p s => Bool.rec (motive := fun _ => Nat) s (Nat.lor s (pw2 p)) (c p)) 0).testBit q
      = (decide (q ∈ L) && c q)
  | [] => by simp
  | p :: L => by
    rw [List.foldr_cons, nIf_ite]
    split_ifs with hc
    · rw [testBit_lor, foldr_bits c q L, pw2_eq, Nat.testBit_two_pow]
      by_cases e : p = q
      · subst e
        simp [hc]
      · simp [e, Ne.symm e]
    · rw [foldr_bits c q L]
      by_cases e : p = q
      · subst e
        simp [hc]
      · simp [Ne.symm e]

theorem fixK_testBit (a q : Nat) :
    (fixK a).testBit q = (decide (q < 64) && Nat.beq (pg 7 127 a q) q) := by
  unfold fixK
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  refine (foldr_bits (fun p => Nat.beq (pg 7 127 a p) p) q (List.range 64)).trans ?_
  simp

theorem fixK_lt (a : Nat) : fixK a < 2 ^ 64 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [fixK_testBit]
    simp
    omega

theorem unpack_get64 {v p : Nat} (hp : p < 64) : (unpack 64 7 v)[p]! = pg 7 127 v p :=
  unpack_get' hp

abbrev Cn (v : Nat) : Prop := canonK 64 7 (mask 7) (64 * 7) v = true

theorem comp_U {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 64 (unpack 64 7 p) (unpack 64 7 q) = unpack 64 7 (pc p q) :=
  CFSG.KS.PEnum.comp_unpack hp hq

theorem can_pc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) :=
  canonK_pcomp hp hq

theorem ubeq {x y : Nat} (hx : Cn x) (hy : Cn y) :
    (unpack 64 7 x == unpack 64 7 y) = Nat.beq x y := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨CFSG.KS.PEnum.unpack_inj hx hy, fun e => e ▸ rfl⟩

theorem isInvol_U {t : Nat} (hsz : szOK 64 7 = true) (hid : Cn (pidn 64 7)) (ht : Cn t) :
    isInvol (unpack 64 7 t) = invK (pidn 64 7) t := by
  unfold isInvol invK
  rw [comp_U ht ht, CFSG.KS.PEnum.idTab_unpack hsz, ubeq (can_pc ht ht) hid, ubeq ht hid]
  cases Nat.beq (pc t t) (pidn 64 7) <;> cases Nat.beq t (pidn 64 7) <;> rfl

noncomputable def invA (M : Nat) (V : Nat → Nat) : Array Tab :=
  Array.ofFn (n := M) fun j => unpack 64 7 (V j.val)

theorem invA_size (M : Nat) (V : Nat → Nat) : (invA M V).size = M := by
  simp [invA]

theorem invA_get {M j : Nat} {V : Nat → Nat} (hj : j < M) : (invA M V)[j]! = unpack 64 7 (V j) := by
  rw [getElem!_pos _ j (by rw [invA_size]; exact hj)]
  simp [invA]

def skelG (inv : Array Tab) (leaf : Nat → Nat → Nat → Nat → Bool) : Bool :=
  allBelow inv.size fun i =>
    let a := inv[i]!
    let ci := (centIdxG inv)[i]!
    ci.all fun j =>
      inv[j]! == a ||
        (let s₂ := span2 a inv[j]!
         ci.all fun k =>
           !(cmG inv j k) || s₂.contains inv[k]! ||
             (let s₃ := span3 a inv[j]! inv[k]!
              ci.all fun l =>
                !(cmG inv j l && cmG inv k l) || s₃.contains inv[l]! || leaf i j k l))

structure SF (M : Nat) (V CM FX PTR CN CIX CMC FXC : Nat → Nat) : Prop where
  sz : szOK 64 7 = true
  can : ∀ j < M, Cn (V j)
  inj : ∀ a < M, ∀ b < M, V a = V b → a = b
  row : ∀ j < M, rowK M V CM FX PTR j = true
  ci : ∀ i < M, ciK M CM FX CN CIX CMC FXC i = true

section Facts

variable {M : Nat} {V CM FX PTR CN CIX CMC FXC : Nat → Nat}
  (F : SF M V CM FX PTR CN CIX CMC FXC)
include F

theorem SF.cm {a b : Nat} (ha : a < M) (hb : b < M) : cmG (invA M V) a b = hasB (CM a) b := by
  unfold cmG
  rw [getElem!_pos _ a (by simp [invA_size, ha]), Array.getElem_map,
    getElem!_pos _ b (by simp [invA_size, hb]), Array.getElem_map,
    ← getElem!_pos (invA M V) a (by simp [invA_size, ha]),
    ← getElem!_pos (invA M V) b (by simp [invA_size, hb]), invA_get ha, invA_get hb,
    comp_U (F.can a ha) (F.can b hb), comp_U (F.can b hb) (F.can a ha),
    ubeq (can_pc (F.can a ha) (F.can b hb)) (can_pc (F.can b hb) (F.can a ha)),
    Bool.eq_iff_iff, Nat.beq_eq]
  exact ((row_spec (F.row a ha)).2.2 b hb).1.symm

theorem SF.ptr {a b : Nat} (ha : a < M) (hb : b < M) (hab : hasB (CM a) b = true) (hne : b ≠ a) :
    f9 (PTR a) b < M ∧
      comp 64 (unpack 64 7 (V a)) (unpack 64 7 (V b)) = unpack 64 7 (V (f9 (PTR a) b)) := by
  obtain ⟨h1, h2⟩ := (row_spec (F.row a ha)).2.2 b hb
  obtain ⟨h3, h4⟩ := h2 (h1.1 hab) hne
  exact ⟨h3, by rw [comp_U (F.can a ha) (F.can b hb), h4]⟩

theorem SF.ci_toList {i : Nat} (hi : i < M) :
    ((centIdxG (invA M V))[i]!).toList = (List.range (CN i)).map (f9 (CIX i)) := by
  unfold centIdxG
  rw [getElem!_pos _ i (by simp [invA_size, hi]), Array.getElem_map, Array.getElem_range,
    Array.toList_filter, Array.toList_range, invA_size,
    List.filter_congr (fun m hm => F.cm hi (List.mem_range.1 hm))]
  exact (ci_spec (F.ci i hi)).1

theorem SF.ci_all {i : Nat} (hi : i < M) (f : Nat → Bool) :
    ((centIdxG (invA M V))[i]!).all f = true ↔ ∀ t < CN i, f (f9 (CIX i) t) = true := by
  rw [← Array.all_toList, F.ci_toList hi, List.all_map, List.all_eq_true]
  simp

theorem SF.ci_mem {i t : Nat} (hi : i < M) (ht : t < CN i) :
    f9 (CIX i) t < M ∧ hasB (CM i) (f9 (CIX i) t) = true := by
  have h : f9 (CIX i) t ∈ (List.range M).filter (hasB (CM i)) := by
    rw [(ci_spec (F.ci i hi)).1]
    exact List.mem_map_of_mem (List.mem_range.2 ht)
  rw [List.mem_filter, List.mem_range] at h
  exact h

theorem SF.cm_lt {i t : Nat} (hi : i < M) (ht : t < CN i) : CM (f9 (CIX i) t) < 2 ^ 320 := by
  rw [← ((ci_spec (F.ci i hi)).2 t ht).1]
  exact l320_lt _ _

theorem SF.fixU {j p : Nat} (hj : j < M) (hp : p < 64) :
    (((invA M V)[j]!)[p]! == p) = (FX j).testBit p := by
  rw [invA_get hj, unpack_get64 hp, (row_spec (F.row j hj)).1, fixK_testBit,
    decide_eq_true hp, Bool.true_and]
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem SF.fx_lt {j : Nat} (hj : j < M) : FX j < 2 ^ 64 := by
  rw [(row_spec (F.row j hj)).1]
  exact fixK_lt _

theorem SF.cmM_lt {j : Nat} (hj : j < M) : CM j < 2 ^ M :=
  lt_of_shr (row_spec (F.row j hj)).2.1

theorem SF.fixC {j : Nat} (hj : j < M) : fixCount (invA M V)[j]! = popK (FX j) := by
  unfold fixCount countBelow
  rw [popK_count (x := FX j) (Nat.lt_of_lt_of_le (F.fx_lt hj) (Nat.pow_le_pow_right (by decide)
    (by decide))) (F.fx_lt hj), List.filter_congr fun p hp => F.fixU hj (List.mem_range.1 hp)]

theorem SF.fix4 {i j k l : Nat} (hi : i < M) (hj : j < M) (hk : k < M) (hl : l < M) :
    fixCount4 (invA M V)[i]! (invA M V)[j]! (invA M V)[k]! (invA M V)[l]! =
      popK (Nat.land (Nat.land (FX i) (Nat.land (FX j) (FX k))) (FX l)) := by
  have hlt : Nat.land (Nat.land (FX i) (Nat.land (FX j) (FX k))) (FX l) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (F.fx_lt hl)
  unfold fixCount4 countBelow
  rw [popK_count (x := Nat.land (Nat.land (FX i) (Nat.land (FX j) (FX k))) (FX l))
    (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by decide))) hlt]
  refine congrArg List.length (List.filter_congr fun p hp => ?_)
  have hp' := List.mem_range.1 hp
  rw [F.fixU hi hp', F.fixU hj hp', F.fixU hk hp', F.fixU hl hp', testBit_land, testBit_land,
    testBit_land]
  cases (FX i).testBit p <;> cases (FX j).testBit p <;> cases (FX k).testBit p <;>
    cases (FX l).testBit p <;> rfl

theorem SF.cent4 {i j k l : Nat} (hi : i < M) (hj : j < M) (hk : k < M) (hl : l < M)
    (h320 : CM l < 2 ^ 320) :
    (((centIdxG (invA M V))[i]!).filter fun m =>
        cmG (invA M V) j m && cmG (invA M V) k m && cmG (invA M V) l m).size =
      popK (Nat.land (Nat.land (CM i) (Nat.land (CM j) (CM k))) (CM l)) := by
  have hlt : Nat.land (Nat.land (CM i) (Nat.land (CM j) (CM k))) (CM l) < 2 ^ M :=
    Nat.lt_of_le_of_lt (Nat.le_trans Nat.and_le_left Nat.and_le_left) (F.cmM_lt hi)
  rw [popK_count (x := Nat.land (Nat.land (CM i) (Nat.land (CM j) (CM k))) (CM l))
    (Nat.lt_of_le_of_lt Nat.and_le_right h320) hlt, ← Array.length_toList, Array.toList_filter]
  unfold centIdxG
  rw [getElem!_pos _ i (by simp [invA_size, hi]), Array.getElem_map, Array.getElem_range,
    Array.toList_filter, Array.toList_range, invA_size, List.filter_filter]
  refine congrArg List.length (List.filter_congr fun m hm => ?_)
  have hm' := List.mem_range.1 hm
  rw [F.cm hi hm', F.cm hj hm', F.cm hk hm', F.cm hl hm', hasB_eq, hasB_eq, hasB_eq, hasB_eq,
    testBit_land, testBit_land, testBit_land]
  cases (CM i).testBit m <;> cases (CM j).testBit m <;> cases (CM k).testBit m <;>
    cases (CM l).testBit m <;> rfl

omit F in
theorem SF.mem2 {i j k p : Nat} (hi : i < M) (hj : j < M) (hk : k < M)
    (hp : comp 64 (unpack 64 7 (V i)) (unpack 64 7 (V j)) = unpack 64 7 (V p))
    (h : k = i ∨ k = j ∨ k = p) :
    (span2 (invA M V)[i]! (invA M V)[j]!).contains (invA M V)[k]! = true := by
  rw [invA_get hi, invA_get hj, invA_get hk, Array.contains_eq_mem, decide_eq_true_iff]
  unfold span2
  rw [hp]
  rcases h with rfl | rfl | rfl <;> simp

omit F in
theorem SF.mem3 {i j k l p a b c : Nat} (hi : i < M) (hj : j < M) (hk : k < M) (hl : l < M)
    (hp : comp 64 (unpack 64 7 (V i)) (unpack 64 7 (V j)) = unpack 64 7 (V p))
    (ha : comp 64 (unpack 64 7 (V i)) (unpack 64 7 (V k)) = unpack 64 7 (V a))
    (hb : comp 64 (unpack 64 7 (V j)) (unpack 64 7 (V k)) = unpack 64 7 (V b))
    (hc : comp 64 (unpack 64 7 (V p)) (unpack 64 7 (V k)) = unpack 64 7 (V c))
    (h : l = i ∨ l = j ∨ l = p ∨ l = k ∨ l = a ∨ l = b ∨ l = c) :
    (span3 (invA M V)[i]! (invA M V)[j]! (invA M V)[k]!).contains (invA M V)[l]! = true := by
  rw [invA_get hi, invA_get hj, invA_get hk, invA_get hl, Array.contains_eq_mem,
    decide_eq_true_iff]
  unfold span3 span2
  rw [hp]
  simp only [List.map_toArray, List.map_cons, List.map_nil, ha, hb, hc]
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

omit F in
theorem testBit_pw2s (q i : Nat) : (pw2 i).testBit q = decide (q = i) := by
  rw [pw2_eq, Nat.testBit_two_pow]
  exact decide_eq_decide.2 eq_comm

theorem SF.skel (h23 : ∀ i < M, f23K CM FX PTR CN CIX CMC FXC i = true)
    (leaf : Nat → Nat → Nat → Nat → Bool)
    (hleaf : ∀ i j k l, i < M → j < M → k < M → l < M → CM l < 2 ^ 320 →
      popK (Nat.land (Nat.land (CM i) (Nat.land (CM j) (CM k))) (CM l)) = 15 →
      popK (Nat.land (Nat.land (FX i) (Nat.land (FX j) (FX k))) (FX l)) = 2 →
      leaf i j k l = true) :
    skelG (invA M V) leaf = true := by
  unfold skelG
  rw [invA_size]
  refine CFSG.KS.BfsReplay.allBelow_iff.2 fun i hi => ?_
  dsimp only
  have hK := h23 i hi
  unfold f23K at hK
  simp only [strictB_app] at hK
  rw [F.ci_all hi]
  intro tj htj
  obtain ⟨hjM, hij⟩ := F.ci_mem hi htj
  have hKj := allN_spec hK tj htj
  obtain ⟨hcmj, hfxj⟩ := (ci_spec (F.ci i hi)).2 tj htj
  rw [hcmj, hfxj] at hKj
  generalize f9 (CIX i) tj = j at hjM hij hKj
  rw [Bool.or_eq_true]
  by_cases hji : j = i
  · subst hji
    exact Or.inl (beq_self_eq_true _)
  right
  have hb : Nat.beq j i = false := by
    cases h' : Nat.beq j i
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') hji
  rw [hb] at hKj
  dsimp only at hKj
  obtain ⟨hpM, hcij⟩ := F.ptr hi hjM hij hji
  generalize f9 (PTR i) j = p at hpM hcij hKj
  unfold kLoopK at hKj
  simp only [strictB_app] at hKj
  rw [F.ci_all hi]
  intro tk htk
  obtain ⟨hkM, hik⟩ := F.ci_mem hi htk
  have hKk := allN_spec hKj tk htk
  obtain ⟨hcmk, hfxk⟩ := (ci_spec (F.ci i hi)).2 tk htk
  rw [hcmk, hfxk] at hKk
  generalize f9 (CIX i) tk = k at hkM hik hKk
  rw [F.cm hjM hkM, Bool.or_eq_true, Bool.or_eq_true]
  by_cases hjk : hasB (CM j) k = true
  swap
  · left
    left
    simp [hjk]
  by_cases hin : k = i ∨ k = j ∨ k = p
  · exact Or.inl (Or.inr (SF.mem2 hi hjM hkM hcij hin))
  right
  have hs2 : hasB (Nat.lor (pw2 i) (Nat.lor (pw2 j) (pw2 p))) k = false := by
    rw [hasB_eq, testBit_lor, testBit_lor, testBit_pw2s, testBit_pw2s, testBit_pw2s]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  rw [hjk, hs2] at hKk
  dsimp only at hKk
  rw [bAnd_iff] at hKk
  obtain ⟨hpk, hKl0⟩ := hKk
  have hki : k ≠ i := fun e => hin (Or.inl e)
  have hkj : k ≠ j := fun e => hin (Or.inr (Or.inl e))
  have hkp : k ≠ p := fun e => hin (Or.inr (Or.inr e))
  obtain ⟨haM, hca⟩ := F.ptr hi hkM hik hki
  obtain ⟨hbM, hcb⟩ := F.ptr hjM hkM hjk hkj
  obtain ⟨hcM, hcc⟩ := F.ptr hpM hkM hpk hkp
  generalize f9 (PTR i) k = a at haM hca hKl0
  generalize f9 (PTR j) k = b at hbM hcb hKl0
  generalize f9 (PTR p) k = c at hcM hcc hKl0
  unfold leafK at hKl0
  rw [F.ci_all hi]
  intro tl htl
  obtain ⟨hlM, -⟩ := F.ci_mem hi htl
  have h320 := F.cm_lt hi htl
  have hKl := allN_spec hKl0 tl htl
  obtain ⟨hcml, hfxl⟩ := (ci_spec (F.ci i hi)).2 tl htl
  rw [hcml, hfxl] at hKl
  generalize f9 (CIX i) tl = l at hlM h320 hKl
  rw [F.cm hjM hlM, F.cm hkM hlM, Bool.or_eq_true, Bool.or_eq_true]
  by_cases hjl : hasB (CM j) l = true ∧ hasB (CM k) l = true
  swap
  · left
    left
    revert hjl
    cases hasB (CM j) l <;> cases hasB (CM k) l <;> simp
  by_cases hin3 : l = i ∨ l = j ∨ l = p ∨ l = k ∨ l = a ∨ l = b ∨ l = c
  · exact Or.inl (Or.inr (SF.mem3 hi hjM hkM hlM hcij hca hcb hcc hin3))
  right
  have hs3 : (Nat.lor (Nat.lor (pw2 i) (Nat.lor (pw2 j) (pw2 p))) (Nat.lor (pw2 k)
      (Nat.lor (pw2 a) (Nat.lor (pw2 b) (pw2 c))))).testBit l = false := by
    simp only [testBit_lor, testBit_pw2s, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  have hG : Nat.beq (Nat.land (Nat.sub (Nat.land (CM j) (CM k)) (Nat.land (Nat.land (CM j) (CM k))
      (Nat.lor (Nat.lor (pw2 i) (Nat.lor (pw2 j) (pw2 p))) (Nat.lor (pw2 k) (Nat.lor (pw2 a)
        (Nat.lor (pw2 b) (pw2 c))))))) (pw2 l)) 0 = false := by
    rw [beq_land_pw2, testBit_sub_land, testBit_land, ← hasB_eq (CM j) l, ← hasB_eq (CM k) l,
      hjl.1, hjl.2, hs3]
    rfl
  rw [hG] at hKl
  dsimp only at hKl
  rw [bAnd_iff] at hKl
  exact hleaf i j k l hi hjM hkM hlM h320 (Nat.eq_of_beq_eq_true hKl.1)
    (Nat.eq_of_beq_eq_true hKl.2)

end Facts

theorem f2G_eq (inv : Array Tab) : f2G inv = skelG inv fun i j k l =>
    (((centIdxG inv)[i]!).filter fun m => cmG inv j m && cmG inv k m && cmG inv l m).size == 15 :=
  rfl

theorem f3G_eq (inv : Array Tab) : f3G inv = skelG inv fun i j k l =>
    fixCount4 inv[i]! inv[j]! inv[k]! inv[l]! == 2 :=
  rfl

end CFSG.KC.SHatClosed

public section

namespace CFSG.KC.SHatClosed

open CFSG.PSL3Four.Native CFSG.ComponentClassification.AS81.SHatClosed
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

theorem shatK_sound {ng N M : Nat} {G T E S I V CM FX PTR CN CIX CMC FXC : Nat → Nat}
    (hk : bfsK (nat_lit 64) (nat_lit 7) ng G N T E S = true)
    (hI : invIdxK N M T I = true) (hV : bindK M T I V = true)
    (hrow : ∀ j < M, rowK M V CM FX PTR j = true)
    (hci : ∀ i < M, ciK M CM FX CN CIX CMC FXC i = true)
    (h1 : f1K M FX = true)
    (h23 : ∀ i < M, f23K CM FX PTR CN CIX CMC FXC i = true) :
    f1G ((Array.ofFn (n := N) fun i => unpack 64 7 (T i.val)).filter isInvol) = true ∧
      f2G ((Array.ofFn (n := N) fun i => unpack 64 7 (T i.val)).filter isInvol) = true ∧
      f3G ((Array.ofFn (n := N) fun i => unpack 64 7 (T i.val)).filter isInvol) = true := by
  have hk' := hk
  unfold bfsK at hk'
  simp only [CFSG.KS.bAnd_iff] at hk'
  obtain ⟨hsz, -, -, hT0, hdist, -⟩ := hk'
  have hcT := bfsK_canon hk
  obtain ⟨hN0, -, -, -⟩ := bfsK_points (fun _ => True) trivial (fun _ _ _ _ => trivial) hk
  have hid : Cn (pidn 64 7) := by
    rw [← Nat.eq_of_beq_eq_true hT0]
    exact hcT 0 hN0
  have hinjT := distinctK_inj hdist
  have hL := invIdx_spec hI
  have hIlt : ∀ t < M, I t < N := fun t ht => by
    have hm : I t ∈ (List.range N).filter (fun i => invK (pidn 64 7) (T i)) := by
      rw [hL]
      exact List.mem_map_of_mem (List.mem_range.2 ht)
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have hIinj : ∀ a < M, ∀ b < M, I a = I b → a = b := fun a ha b hb e => by
    have hnd : ((List.range M).map I).Nodup := by
      rw [← hL]
      exact List.Nodup.filter _ List.nodup_range
    exact List.inj_on_of_nodup_map hnd (List.mem_range.2 ha) (List.mem_range.2 hb) e
  have hVT : ∀ j < M, V j = T (I j) := fun j hj => Nat.eq_of_beq_eq_true (allN_spec hV j hj)
  have F : SF M V CM FX PTR CN CIX CMC FXC :=
    ⟨hsz, fun j hj => by rw [hVT j hj]; exact hcT _ (hIlt j hj),
      fun a ha b hb e => by
        rw [hVT a ha, hVT b hb] at e
        exact hIinj a ha b hb (hinjT _ (hIlt a ha) _ (hIlt b hb) e),
      hrow, hci⟩
  have hA : (Array.ofFn (n := N) fun i => unpack 64 7 (T i.val)).filter isInvol = invA M V := by
    apply Array.toList_inj.1
    rw [Array.toList_filter, pts_toList (N := N) (fun i => unpack 64 7 (T i)), List.filter_map]
    simp only [Function.comp_def]
    rw [List.filter_congr fun i hi => isInvol_U hsz hid (hcT i (List.mem_range.1 hi)), hL,
      List.map_map]
    unfold invA
    rw [Array.toList_ofFn]
    apply List.ext_getElem (by simp)
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, Function.comp]
    rw [hVT t (by simpa using h1)]
  rw [hA, f2G_eq, f3G_eq]
  refine ⟨?_, F.skel h23 _ fun i j k l hi hj hk hl h320 h15 _ => ?_,
    F.skel h23 _ fun i j k l hi hj hk hl _ _ h2 => ?_⟩
  · unfold f1G
    rw [Array.all_eq_true]
    intro j hj
    rw [invA_size] at hj
    rw [← getElem!_pos (invA M V) j (by rw [invA_size]; exact hj), F.fixC hj,
      Nat.eq_of_beq_eq_true (allN_spec h1 j hj)]
    rfl
  · rw [F.cent4 hi hj hk hl h320, h15]
    rfl
  · rw [F.fix4 hi hj hk hl, h2]
    rfl

end CFSG.KC.SHatClosed

end
