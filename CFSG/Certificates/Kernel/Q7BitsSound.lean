module

public import Certificates.Data.Kernel.Q7Bits.Defs
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastC
import CFSG.Certificates.Kernel.Q7BitsLanes

public section

namespace CFSG.Certificates.Kernel.Q7Bits

open CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

theorem forceN_eq {β : Sort _} (y : Nat) (k : Nat → β) : forceN y k = k y := by
  unfold forceN
  cases h : Nat.beq y 0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]
    rfl

theorem forceV7_eq {β : Sort _} (v : N7) (k : N7 → β) : forceV7 v k = k v := by
  simp only [forceV7, forceN_eq]

@[expose] def VtxL (c : N7) (L : Nat) : Prop :=
  vtxF c (herN c c) (laneVec c L) (hDiag (laneVec c L)) = true

theorem rowCore_lanes {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {rootL : Nat}
    {lvls : List (List Nat)} (hr : rootL < NL) (h : rowCore c rootL lvls = true) :
    VtxL c rootL ∧ ∀ L < NL, VtxL c L → ∃ n, n ≤ lvls.length ∧
      Wk colN (fun u => ∃ L' < NL, u = laneVec c L' ∧ VtxL c L') n (laneVec c rootL)
        (laneVec c L) :=
  Lanes.rowCore_spec hc hr h

theorem laneArgs_A {L : Nat} (h : L < 117649) :
    laneArgs L = (1, L / 2401, gfAdd (gfNeg (gfMul (L / 2401) (L / 49 % 49)))
      (gfMul (L % 49) (L % 49)), L / 49 % 49, L % 49) := if_pos h

theorem laneArgs_B {L : Nat} (h1 : ¬L < 117649) (h2 : L < 120050) :
    laneArgs L = (0, 1, (L - 117649) / 49, gfMul ((L - 117649) % 49) ((L - 117649) % 49),
      (L - 117649) % 49) := by
  rw [laneArgs, if_neg h1, if_pos h2]

theorem laneArgs_C {L : Nat} (h1 : ¬L < 117649) (h2 : ¬L < 120050) (h3 : L < 120099) :
    laneArgs L = (0, 0, 1, L - 120050, 0) := by
  rw [laneArgs, if_neg h1, if_neg h2, if_pos h3]

theorem laneArgs_D {L : Nat} (h1 : ¬L < 117649) (h2 : ¬L < 120050) (h3 : ¬L < 120099) :
    laneArgs L = (0, 0, 0, 1, 0) := by
  rw [laneArgs, if_neg h1, if_neg h2, if_neg h3]

theorem laneVec_spec {c : N7} {L : Nat} (hL : L < NL) :
    laneVec c L ∈ q7Cands c ∧ (laneArgs L).1 < 49 ∧ (laneArgs L).2.1 < 49 ∧
      (laneArgs L).2.2.1 < 49 ∧ (laneArgs L).2.2.2.1 < 49 ∧ (laneArgs L).2.2.2.2 < 49 ∧
      gfDec (laneArgs L).1 * gfDec (laneArgs L).2.2.1 +
        gfDec (laneArgs L).2.1 * gfDec (laneArgs L).2.2.2.1 = gfDec (laneArgs L).2.2.2.2 ^ 2 := by
  unfold NL at hL
  unfold laneVec
  by_cases h1 : L < 117649
  · rw [laneArgs_A h1]
    have h2 : L / 2401 < 49 := by omega
    have h5 : L / 49 % 49 < 49 := Nat.mod_lt _ (by norm_num)
    have h6 : L % 49 < 49 := Nat.mod_lt _ (by norm_num)
    refine ⟨candN_mem_A h2 h5 h6, by norm_num, h2, gfAdd_lt _ _, h5, h6, ?_⟩
    simp only [gfDec_one, gfDec_add, gfDec_neg, gfDec_mul]
    ring
  by_cases h2 : L < 120050
  · rw [laneArgs_B h1 h2]
    have h4 : (L - 117649) / 49 < 49 := by omega
    have h6 : (L - 117649) % 49 < 49 := Nat.mod_lt _ (by norm_num)
    refine ⟨candN_mem_B h4 h6, by norm_num, by norm_num, h4, gfMul_lt _ _, h6, ?_⟩
    simp only [gfDec_zero, gfDec_one, gfDec_mul]
    ring
  by_cases h3 : L < 120099
  · rw [laneArgs_C h1 h2 h3]
    have h5 : L - 120050 < 49 := by omega
    refine ⟨candN_mem_C h5, by norm_num, by norm_num, by norm_num, h5, by norm_num, ?_⟩
    simp only [gfDec_zero]
    ring
  · rw [laneArgs_D h1 h2 h3]
    refine ⟨candN_mem_D c, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [gfDec_zero]
    ring

theorem laneVec_mem_iff {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {L : Nat} (hL : L < NL) :
    laneVec c L ∈ q7Pts c ↔ VtxL c L := by
  obtain ⟨hm, h1, h2, h4, h5, h6, hq⟩ := laneVec_spec (c := c) hL
  rw [mem_q7Pts_iff hm]
  exact vert_iff_vtxF hc hc3 rfl h1 h2 h4 h5 h6 hq

theorem exists_lane_of_mem {c p : N7} (hp : p ∈ q7Cands c) : ∃ L < NL, p = laneVec c L := by
  unfold NL
  simp only [q7Cands, candsA, candsB, candsC, candsD, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with ((⟨x2, h2, x5, h5, x6, h6, e⟩ | ⟨x4, h4, x6, h6, e⟩) | ⟨x5, h5, e⟩) | e
  · refine ⟨2401 * x2 + 49 * x5 + x6, by omega, ?_⟩
    rw [laneVec, laneArgs_A (by omega), ← e]
    have a : (2401 * x2 + 49 * x5 + x6) / 2401 = x2 := by omega
    have b : (2401 * x2 + 49 * x5 + x6) / 49 % 49 = x5 := by omega
    have d : (2401 * x2 + 49 * x5 + x6) % 49 = x6 := by omega
    rw [a, b, d]
  · refine ⟨117649 + 49 * x4 + x6, by omega, ?_⟩
    rw [laneVec, laneArgs_B (by omega) (by omega), ← e]
    have a : (117649 + 49 * x4 + x6 - 117649) / 49 = x4 := by omega
    have d : (117649 + 49 * x4 + x6 - 117649) % 49 = x6 := by omega
    rw [a, d]
  · refine ⟨120050 + x5, by omega, ?_⟩
    rw [laneVec, laneArgs_C (by omega) (by omega) (by omega), ← e]
    have a : 120050 + x5 - 120050 = x5 := by omega
    rw [a]
  · refine ⟨120099, by omega, ?_⟩
    rw [laneVec, laneArgs_D (by omega) (by omega) (by omega), ← e]

theorem rowCore_walks {c : N7} (hc : Lt49 c) (hc3 : c.x3 = 1) {rootL : Nat}
    {lvls : List (List Nat)} (hl : lvls.length ≤ 6) (hr : rootL < NL)
    (h : rowCore c rootL lvls = true) :
    ∃ r, r ∈ q7Pts c ∧ ∀ p ∈ q7Pts c, ∃ n, n ≤ 6 ∧ Wk colN (· ∈ q7Pts c) n r p := by
  obtain ⟨hroot, hall⟩ := rowCore_lanes hc hc3 hr h
  refine ⟨laneVec c rootL, (laneVec_mem_iff hc hc3 hr).2 hroot, ?_⟩
  intro p hp
  obtain ⟨L, hL, rfl⟩ := exists_lane_of_mem (List.mem_filter.1 hp).1
  obtain ⟨n, hn, w⟩ := hall L hL ((laneVec_mem_iff hc hc3 hL).1 hp)
  refine ⟨n, by omega, w.mono ?_⟩
  rintro u ⟨L', hL', rfl, hv⟩
  exact (laneVec_mem_iff hc hc3 hL').2 hv

theorem rowCheck_sound {row : Array Nat} {rootL : Nat} {lvls : List (List Nat)}
    (h : rowCheck row rootL lvls = true) : q7RowCheck row = true := by
  unfold rowCheck at h
  rw [forceV7_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hc3⟩, hff⟩, hl⟩, hr⟩, hcore⟩ := h
  have hc : Lt49 (rowN row) := ⟨h0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r, hrL, hwalk⟩ := rowCore_walks hc hc3 hl hr hcore
  unfold q7RowCheck
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hc3, hff⟩, ?_⟩
  rcases hL : q7Pts (rowN row) with _ | ⟨r₀, rest⟩
  · rfl
  · apply bfsOk_of_walks (r := r₀) (rest := rest)
    · have hnd := q7Pts_nodup (rowN row)
      rw [hL] at hnd
      exact (List.nodup_cons.1 hnd).1
    · intro u hu
      have hr₀L : r₀ ∈ q7Pts (rowN row) := by
        rw [hL]
        exact List.mem_cons_self
      have huL : u ∈ q7Pts (rowN row) := by
        rw [hL]
        exact List.mem_cons_of_mem _ hu
      obtain ⟨n1, hn1, w1⟩ := hwalk r₀ hr₀L
      obtain ⟨n2, hn2, w2⟩ := hwalk u huL
      have w1' := w1.symm (fun a b hab => colN_symm hab) hrL
      refine ⟨n1 + n2, by omega, ?_⟩
      rw [hL] at w1' w2
      exact w1'.trans w2

theorem q7MuCheck_of_rows (rt : Nat → Nat) (lv : Nat → List (List Nat))
    (h : ∀ i < 91, rowCheck q7RepsData[i]! (rt i) (lv i) = true) : q7MuCheck = true := by
  unfold q7MuCheck
  refine Array.all_eq_true.2 fun i hi => ?_
  have hs : q7RepsData.size = 91 := rfl
  have h1 := rowCheck_sound (h i (hs ▸ hi))
  rwa [getElem!_pos q7RepsData i hi] at h1

end CFSG.Certificates.Kernel.Q7Bits
