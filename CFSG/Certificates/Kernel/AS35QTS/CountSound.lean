module

public import CFSG.Certificates.Kernel.AS35QTS.ListSound
public import CFSG.Certificates.Kernel.LceSP.Popcount
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC CFSG.KC.F4M3B CFSG.Fischer CFSG.Certificates.LceP Finset
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 I3 unitB cgens commB codes sl gu3s t0c)

theorem popcount_sum (x k : ℕ) (hk : 32 * (k + 1) ≤ 4294967295) :
    popcount x (32 * (k + 1)) = ∑ j ∈ range (32 * (k + 1)), x / 2 ^ j % 2 := by
  set n := 32 * (k + 1) with hn
  set x1 := swarStep n 1 x
  set x2 := swarStep n 2 x1
  set x3 := swarStep n 4 x2
  set x4 := swarStep n 8 x3
  have c1 : ds 2 x1 (16 * (k + 1)) = ds 1 x n :=
    ds_swarStep (b := 1) (b2 := 2) (m := 16 * (k + 1)) (m2 := n) (n := n) (by norm_num) rfl
      (by omega) (by omega) x
  have c2 : ds 4 x2 (8 * (k + 1)) = ds 2 x1 (16 * (k + 1)) :=
    ds_swarStep (b := 2) (b2 := 4) (m := 8 * (k + 1)) (m2 := 16 * (k + 1)) (n := n) (by norm_num)
      rfl (by omega) (by omega) x1
  have c3 : ds 8 x3 (4 * (k + 1)) = ds 4 x2 (8 * (k + 1)) :=
    ds_swarStep (b := 4) (b2 := 8) (m := 4 * (k + 1)) (m2 := 8 * (k + 1)) (n := n) (by norm_num)
      rfl (by omega) (by omega) x2
  have c4 : ds 16 x4 (2 * (k + 1)) = ds 8 x3 (4 * (k + 1)) :=
    ds_swarStep (b := 8) (b2 := 16) (m := 2 * (k + 1)) (m2 := 4 * (k + 1)) (n := n)
      (by norm_num) rfl (by omega) (by omega) x3
  have hrep := swarStep_rep (b := 16) (b2 := 32) (m := k + 1) (n := n) (by norm_num) rfl
    (by omega) x4
  set e : ℕ → ℕ := fun t => x4 / 2 ^ (16 * (2 * t)) % 2 ^ 16 + x4 / 2 ^ (16 * (2 * t + 1)) % 2 ^ 16
  have hT : ∑ t ∈ range (k + 1), e t = ds 1 x n := by
    rw [← c1, ← c2, ← c3, ← c4]
    unfold ds
    exact sum_pairs (fun j => x4 / 2 ^ (16 * j) % 2 ^ 16) (k + 1)
  have hTle : ∑ t ∈ range (k + 1), e t ≤ n := by
    rw [hT]
    exact ds_one_le x n
  obtain ⟨Lw, Hh, hm, hL⟩ := mul_gs (2 ^ 32) k e
  have h3 : (2 : ℕ) ^ 32 = 4294967295 + 1 := by norm_num
  have hG : Nat.div (Nat.sub (Nat.shiftLeft 1 n) 1) 4294967295 = gs (2 ^ 32) (k + 1) := by
    rw [h3]
    exact gs_shl 4294967295 (k + 1) n (by norm_num) (by rw [← h3, ← pow_mul])
  generalize hX : (2 : ℕ) ^ 32 = X at hm hL hG
  have hX1 : X = 4294967295 + 1 := by rw [← hX, h3]
  have hLw : Lw < X ^ k := by
    have h1 := gs_mul 4294967295 k
    rw [← hX1] at h1
    have h2 : Lw ≤ 4294967295 * gs X k :=
      le_trans hL (Nat.mul_le_mul_right _ (by omega))
    omega
  have hs : n - 32 = 32 * k := by omega
  change Nat.land (Nat.shiftRight (Nat.mul (swarStep n 16 x4)
    (Nat.div (Nat.sub (Nat.shiftLeft 1 n) 1) 4294967295)) (Nat.sub n 32)) 4294967295 = _
  rw [hG]
  change (swarStep n 16 x4 * gs X (k + 1)) >>> (n - 32) &&& (2 ^ 32 - 1) = _
  rw [hs, hrep, Nat.and_two_pow_sub_one_eq_mod, shr32, hX]
  change (∑ t ∈ range (k + 1), e t * X ^ t) * gs X (k + 1) / X ^ k % X = _
  rw [hm]
  have e2 : Lw + X ^ k * (∑ t ∈ range (k + 1), e t) + X ^ (k + 1) * Hh =
      Lw + X ^ k * ((∑ t ∈ range (k + 1), e t) + X * Hh) := by ring
  have hX0 : 0 < X := by
    rw [hX1]
    exact Nat.succ_pos _
  have hpos : 0 < X ^ k := pow_pos hX0 _
  rw [e2, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hLw, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), hT, ds_one]

theorem sumBits_card (x N : ℕ) :
    ∑ j ∈ range N, x / 2 ^ j % 2 = #((range N).filter (fun j => x.testBit j = true)) := by
  rw [card_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

theorem popcount_card (x k : ℕ) (hk : 32 * (k + 1) ≤ 4294967295) :
    popcount x (32 * (k + 1)) =
      ((List.range (32 * (k + 1))).filter fun j => x.testBit j).length := by
  rw [popcount_sum x k hk, sumBits_card, ← List.toFinset_range, ← List.toFinset_filter,
    List.toFinset_card_of_nodup (List.nodup_range.filter _)]

theorem popP_card (x : ℕ) :
    popP x = ((List.range 82944).filter fun j => x.testBit j).length := by
  unfold popP
  exact popcount_card x 2591 (by norm_num)

theorem beq_comm' (x y : Cd) : (x == y) = (y == x) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

theorem small_spec : unitB I3 = true ∧ mulC e0 e0 = e0 ∧ ∀ g ∈ cgens, unitB g.m = true := by
  have hI : ∀ z : Cd, unitB z.m = unitT bOps (ofCd z) := fun z => (unitT_ofCd z).symm
  refine ⟨(hI ⟨0, CFSG.LargeExtraspecial.AS35QTS.v0, I3⟩).trans (by decide),
    (eqP_e _ _).1 (by rw [← mulD_ofCd]; decide), ?_⟩
  have h : (cgens.all fun g => unitT bOps (ofCd g)) = true := by decide
  rw [List.all_eq_true] at h
  exact fun g hg => (hI g).trans (h g hg)

theorem decN_lo {c : Nat} (hc : c < 2 ^ 18) : decN c = ⟨0, ⟨e4 0, e4 0, e4 0⟩, dmN c⟩ := by
  have hp : ∀ k, 18 ≤ k → c >>> k = 0 := fun k hk => by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hk))
  have hb : c.testBit 24 = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  unfold dmN
  unfold decN
  rw [hp 22 (by norm_num), hp 20 (by norm_num), hp 18 (by norm_num), hb]
  rfl

theorem dmN_inj {x y : Nat} (hx : x < 2 ^ 18) (hy : y < 2 ^ 18) (h : dmN x = dmN y) : x = y := by
  refine decN_inj (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by norm_num))) ?_
  rw [decN_lo hx, decN_lo hy, h]

section Lanes

variable {G : List Nat} (hg : gOK G = true) (hG : G.length = 648)
include hg hG

theorem lists_spec {S : List Nat} (hs : slOK G S = true) (hS : lenR S = 36) :
    gu3s.length = 648 ∧ gu3s.Nodup ∧ sl.length = 36 ∧ sl.Nodup := by
  have hinc : incB 82944 S = true := by
    unfold slOK at hs
    rw [and'_eq, Bool.and_eq_true] at hs
    exact hs.1
  have hSb := incB_lt hinc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gu3s_eq hg, List.length_map, hG]
  · rw [gu3s_eq hg]
    refine List.Nodup.map_on (fun x hx y hy h => dmN_inj (gb_of hg x hx) (gb_of hg y hy) h) ?_
    exact List.Pairwise.imp (fun h => Nat.ne_of_lt h) (gpw_of hg)
  · rw [sl_eq hg hG hs, List.length_map, ← lenR_eq, hS]
  · rw [sl_eq hg hG hs]
    refine List.Nodup.map_on (fun x hx y hy h => dc_inj hg hG (hSb x hx) (hSb y hy) h) ?_
    exact List.Pairwise.imp (fun h => Nat.ne_of_lt h) (incB_go S 0 hinc).2

theorem t0c_eq {S : List Nat} (hs : slOK G S = true) {s0 : Nat} {S' : List Nat}
    (hS : S = s0 :: S') : t0c = dcG G s0 := by
  change (CFSG.LargeExtraspecial.AS35QTS.sl).headD e0 = _
  rw [sl_eq hg hG hs, hS]
  rfl

theorem centOK_spec {S : List Nat} (hs : slOK G S = true) (h : centOK G S = true) :
    (codes.filter (commB t0c)).toFinset.card = 2304 := by
  have hinc : incB 82944 S = true := by
    unfold slOK at hs
    rw [and'_eq, Bool.and_eq_true] at hs
    exact hs.1
  rcases hS : S with _ | ⟨s0, S'⟩
  · rw [hS] at h
    exact absurd h (by unfold centOK; rw [frc_eqL, lanesK_eq]; exact Bool.false_ne_true)
  have hs0 : s0 < 82944 := incB_lt hinc s0 (by rw [hS]; exact List.mem_cons_self)
  rw [t0c_eq hg hG hs hS, List.toFinset_card_of_nodup ((codes_nodup hg hG).filter _),
    codes_dc hg hG, List.filter_map, List.length_map]
  unfold centOK at h
  rw [frc_eqL, lanesK_eq, hS] at h
  have he := Nat.eq_of_beq_eq_true h
  rw [popP_card] at he
  rw [← he]
  refine congrArg List.length (List.filter_congr fun c hc => ?_)
  have hc' := List.mem_range.1 hc
  have ht := allT_testBit hc'
  have h0 : laneOf c (atLane allT (ofIx (lanePl G)) s0) = ofCd (dcG G s0) := by
    rw [lane_atLane ht]
    exact lane_dc hg hG hs0
  rw [commP_lane ht, lane_mulP _ _ (lane_dc hg hG hc') h0, lane_mulP _ _ h0 (lane_dc hg hG hc'),
    eqP_beq]
  exact beq_comm' _ _

end Lanes

end CFSG.KC.AS35QTS

end
