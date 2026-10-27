module

public import Certificates.Data.Kernel.S1277KMod
public import Certificates.Data.S1277Struct
public import CFSG.Certificates.Kernel.S1277KGmSound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.S1277Mod

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct CFSG.KC.S1277Gm CFSG.KC.S1277Mod
  CFSG.KS.S1277Gm

structure ModFacts (G0 : List B6) (nb AP CP IP idb : ℕ) : Prop where
  nodup : G0.Nodup
  valid : ∀ B ∈ G0, B.Valid
  closed : ∀ B ∈ G0, ∀ C ∈ G0, B.comp C ∈ G0
  idMem : B6.id ∈ G0
  length : G0.length = nb
  mul : mulN (mkTab G0) = mulP nb AP CP
  inv : invN (mkTab G0) = invP AP IP
  one : oneN (mkTab G0) = idb * 64
  idB : (mkTab G0).idB = idb
  kl : klist (mkTab G0) = List.range (nb * 64)
  modelInv : ∀ n ∈ klist (mkTab G0),
    invN (mkTab G0) n ∈ klist (mkTab G0) ∧ mulN (mkTab G0) n (invN (mkTab G0) n) = oneN (mkTab G0)

theorem allLt_iff {n : ℕ} {f : ℕ → Bool} : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change (f n && allLt n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem rd6_lt (P n : ℕ) : rd6 P n < 64 := Nat.mod_lt _ (by norm_num)

theorem rd6_zero {P m n : ℕ} (h : P >>> (6 * m) = 0) (hn : m ≤ n) : rd6 P n = 0 := by
  rw [Nat.shiftRight_eq_div_pow] at h
  have hP : P < 2 ^ (6 * m) := by
    rcases Nat.div_eq_zero_iff.1 h with h | h
    · exact absurd h (pow_ne_zero _ two_ne_zero)
    · exact h
  have hP' : P < 2 ^ (6 * n) := lt_of_lt_of_le hP (Nat.pow_le_pow_right two_pos (by omega))
  rw [rd6, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hP']

theorem appP_b0 (p : ℕ) : appP p (2 ^ 0) = p % 64 := by simp [appP]
theorem appP_b1 (p : ℕ) : appP p (2 ^ 1) = (p >>> 6) % 64 := by simp [appP]
theorem appP_b2 (p : ℕ) : appP p (2 ^ 2) = (p >>> 12) % 64 := by simp [appP]
theorem appP_b3 (p : ℕ) : appP p (2 ^ 3) = (p >>> 18) % 64 := by simp [appP]
theorem appP_b4 (p : ℕ) : appP p (2 ^ 4) = (p >>> 24) % 64 := by simp [appP]
theorem appP_b5 (p : ℕ) : appP p (2 ^ 5) = (p >>> 30) % 64 := by simp [appP]

def bAt (AP k : ℕ) : B6 :=
  ⟨rd6 AP (k * 64 + 2 ^ 0), rd6 AP (k * 64 + 2 ^ 1), rd6 AP (k * 64 + 2 ^ 2),
    rd6 AP (k * 64 + 2 ^ 3), rd6 AP (k * 64 + 2 ^ 4), rd6 AP (k * 64 + 2 ^ 5)⟩

theorem bAt_eq_iff {AP i k : ℕ} : bAt AP i = bAt AP k ↔ agree AP i k = true := by
  rw [agree, allLt_iff]
  constructor
  · intro h f hf
    simp only [bAt, B6.mk.injEq] at h
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
    rw [Nat.beq_eq]
    interval_cases f
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro h
    have e : ∀ f < 6, rd6 AP (i * 64 + 2 ^ f) = rd6 AP (k * 64 + 2 ^ f) := fun f hf =>
      Nat.eq_of_beq_eq_true (h f hf)
    simp only [bAt, B6.mk.injEq]
    exact ⟨e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
      e 4 (by norm_num), e 5 (by norm_num)⟩

section Checks

variable {L : List ℕ} {AP CP IP idb : ℕ}

theorem apChk_spec (h : apChk L AP = true) :
    AP >>> (6 * (L.length * 64)) = 0 ∧
      ∀ i < L.length, ∀ c < 64, rd6 AP (i * 64 + c) = appP (L.getD i 0) c := by
  rw [apChk, Bool.and_eq_true, Nat.beq_eq, allLt_iff] at h
  refine ⟨h.1, fun i hi c hc => ?_⟩
  have := h.2 i hi
  rw [allLt_iff] at this
  exact Nat.eq_of_beq_eq_true (this c hc)

theorem ofP_eq_bAt (h : apChk L AP = true) {i : ℕ} (hi : i < L.length) :
    B6.ofP (L.getD i 0) = bAt AP i := by
  have e := (apChk_spec h).2 i hi
  rw [bAt, e _ (by norm_num), e _ (by norm_num), e _ (by norm_num), e _ (by norm_num),
    e _ (by norm_num), e _ (by norm_num), appP_b0, appP_b1, appP_b2, appP_b3, appP_b4, appP_b5,
    B6.ofP]

theorem bAt_app (h : apChk L AP = true) {i : ℕ} (hi : i < L.length) {c : ℕ} (hc : c < 64) :
    (bAt AP i).app c = rd6 AP (i * 64 + c) := by
  rw [← ofP_eq_bAt h hi, ← appP_eq, (apChk_spec h).2 i hi c hc]

theorem cpChk_spec (h : cpChk L.length AP CP = true) :
    CP >>> (6 * (L.length * L.length)) = 0 ∧
      ∀ i < L.length, ∀ j < L.length, rd6 CP (i * L.length + j) < L.length ∧
        ∀ f < 6, rd6 AP (rd6 CP (i * L.length + j) * 64 + 2 ^ f) =
          rd6 AP (i * 64 + rd6 AP (j * 64 + 2 ^ f)) := by
  rw [cpChk, Bool.and_eq_true, Nat.beq_eq, allLt_iff] at h
  refine ⟨h.1, fun i hi j hj => ?_⟩
  have h2 := h.2 i hi
  rw [allLt_iff] at h2
  have h3 := h2 j hj
  rw [Bool.and_eq_true, Nat.blt_eq, allLt_iff] at h3
  exact ⟨h3.1, fun f hf => Nat.eq_of_beq_eq_true (h3.2 f hf)⟩

theorem bAt_comp (ha : apChk L AP = true) (hc : cpChk L.length AP CP = true) {i j : ℕ}
    (hi : i < L.length) (hj : j < L.length) :
    (bAt AP i).comp (bAt AP j) = bAt AP (rd6 CP (i * L.length + j)) := by
  have e := ((cpChk_spec hc).2 i hi j hj).2
  have a : ∀ f : ℕ, (bAt AP i).app (rd6 AP (j * 64 + 2 ^ f)) =
      rd6 AP (i * 64 + rd6 AP (j * 64 + 2 ^ f)) := fun f => bAt_app ha hi (rd6_lt _ _)
  simp only [B6.comp, bAt, B6.mk.injEq]
  rw [← bAt, a, a, a, a, a, a, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
    e 3 (by norm_num), e 4 (by norm_num), e 5 (by norm_num)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ipChk_spec (h : ipChk L.length AP CP IP idb = true) :
    idb < L.length ∧ bAt AP idb = B6.id ∧ IP >>> (6 * L.length) = 0 ∧
      ∀ i < L.length, rd6 IP i = pwP L.length CP idb i 59 := by
  rw [ipChk] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, allLt_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, ?_, h3, fun i hi => h4 i hi⟩
  simp only [bAt, B6.id, B6.mk.injEq]
  exact ⟨h2 0 (by norm_num), h2 1 (by norm_num), h2 2 (by norm_num), h2 3 (by norm_num),
    h2 4 (by norm_num), h2 5 (by norm_num)⟩

theorem bAt_pow (ha : apChk L AP = true) (hc : cpChk L.length AP CP = true)
    (hp : ipChk L.length AP CP IP idb = true) {i : ℕ} (hi : i < L.length) :
    ∀ n, pwP L.length CP idb i n < L.length ∧ (bAt AP i).pow n = bAt AP (pwP L.length CP idb i n)
  | 0 => ⟨(ipChk_spec hp).1, by rw [B6.pow, pwP, (ipChk_spec hp).2.1]⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := bAt_pow ha hc hp hi n
    refine ⟨((cpChk_spec hc).2 i hi _ h1).1, ?_⟩
    rw [B6.pow, h2, bAt_comp ha hc hi h1, pwP]

end Checks

theorem getD_range_map (f : ℕ → ℕ) (m k : ℕ) :
    ((List.range m).map f).toArray.getD k 0 = if k < m then f k else 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  by_cases h : k < m
  · rw [List.getElem?_range h, if_pos h]
    rfl
  · rw [if_neg h, List.getElem?_eq_none (by simpa using h)]
    rfl

theorem getD_eq_get {α : Type} {l : List α} {i : ℕ} (d : α) (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem getD_ofP {L : List ℕ} {i : ℕ} (hi : i < L.length) :
    (L.map B6.ofP).getD i B6.id = B6.ofP (L.getD i 0) := by
  rw [getD_eq_get _ (by simpa using hi), getD_eq_get _ hi, List.getElem_map]

theorem modFacts_of {L : List ℕ} {AP CP IP idb : ℕ} (h : modChk L AP CP IP idb = true) :
    ModFacts (L.map B6.ofP) L.length AP CP IP idb := by
  rw [modChk] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ha, hc⟩, hd⟩, hp⟩, hv⟩ := h
  set n := L.length with hn
  set G0 := L.map B6.ofP with hG0
  have hlen : G0.length = n := by rw [hG0, List.length_map]
  have hmem : ∀ i < n, G0.getD i B6.id = bAt AP i := fun i hi => by
    rw [hG0, getD_ofP hi, ofP_eq_bAt ha hi]
  have hget : ∀ i (hi : i < G0.length), G0[i] = bAt AP i := fun i hi => by
    rw [← hmem i (hlen ▸ hi), getD_eq_get]
  have hnd : G0.Nodup := by
    rw [List.nodup_iff_injective_get]
    rintro ⟨i, hi⟩ ⟨k, hk⟩ e
    simp only [List.get_eq_getElem, hget] at e
    have hik := (allLt_iff.1 ((allLt_iff.1 hd) i (hlen ▸ hi))) k (hlen ▸ hk)
    rw [bAt_eq_iff.1 e, Bool.not_true, Bool.or_false, Nat.beq_eq] at hik
    exact Fin.ext hik
  have hidx : ∀ k < n, G0.idxOf (bAt AP k) = k := fun k hk => by
    rw [← hget k (hlen ▸ hk)]
    exact hnd.idxOf_getElem k _
  have hnb : (mkTab G0).nb = n := hlen
  have happ : ∀ m, (mkTab G0).appA.getD m 0 = rd6 AP m := by
    intro m
    change ((List.range (G0.length * 64)).map _).toArray.getD m 0 = _
    rw [getD_range_map, hlen]
    split_ifs with hm
    · have hq : m / 64 < n := by omega
      rw [hmem _ hq, bAt_app ha hq (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod']
    · exact (rd6_zero (apChk_spec ha).1 (by omega)).symm
  have hcomp : ∀ m, (mkTab G0).compA.getD m 0 = rd6 CP m := by
    intro m
    change ((List.range (G0.length * G0.length)).map _).toArray.getD m 0 = _
    rw [getD_range_map, hlen]
    split_ifs with hm
    · have hpos : 0 < n := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hm; simp at hm
      have hq : m / n < n := Nat.div_lt_of_lt_mul hm
      have hr : m % n < n := Nat.mod_lt _ hpos
      rw [hmem _ hq, hmem _ hr, bAt_comp ha hc hq hr,
        hidx _ ((cpChk_spec hc).2 _ hq _ hr).1, Nat.div_add_mod']
    · exact (rd6_zero (cpChk_spec hc).1 (by rw [← hn]; omega)).symm
  have hinvA : ∀ m, (mkTab G0).invA.getD m 0 = rd6 IP m := by
    intro m
    change (G0.map fun B => invIdx G0 B).toArray.getD m 0 = _
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
    by_cases hm : m < n
    · rw [List.getElem?_eq_getElem (hlen ▸ hm)]
      change invIdx G0 G0[m] = _
      rw [hget, invIdx, (bAt_pow ha hc hp hm 59).2,
        hidx _ (bAt_pow ha hc hp hm 59).1, (ipChk_spec hp).2.2.2 m hm]
    · rw [List.getElem?_eq_none (by omega)]
      exact (rd6_zero (ipChk_spec hp).2.2.1 (by omega)).symm
  have hidB : (mkTab G0).idB = idb := by
    change G0.idxOf B6.id = idb
    rw [← (ipChk_spec hp).2.1, hidx _ (ipChk_spec hp).1]
  have hmul : mulN (mkTab G0) = mulP n AP CP := by
    funext x y
    rw [mulN, mulP, hnb, hcomp, happ]
  have hinv : invN (mkTab G0) = invP AP IP := by
    funext x
    rw [invN, invP, hinvA, happ]
  have hone : oneN (mkTab G0) = idb * 64 := by rw [oneN, hidB]
  have hkl : klist (mkTab G0) = List.range (n * 64) := by rw [klist, hnb]
  have hval : ∀ B ∈ G0, B.Valid := by
    intro B hB
    rw [hG0, List.mem_map] at hB
    obtain ⟨p, -, rfl⟩ := hB
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.mod_lt _ (by norm_num)
  have hmemi : ∀ B ∈ G0, ∃ i < n, B = bAt AP i := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    exact ⟨i, hlen ▸ hi, hget i hi⟩
  have hbmem : ∀ i < n, bAt AP i ∈ G0 := fun i hi => by
    rw [← hget i (hlen.symm ▸ hi)]
    exact List.getElem_mem _
  have hcl : ∀ B ∈ G0, ∀ C ∈ G0, B.comp C ∈ G0 := by
    intro B hB C hC
    obtain ⟨i, hi, rfl⟩ := hmemi B hB
    obtain ⟨j, hj, rfl⟩ := hmemi C hC
    rw [bAt_comp ha hc hi hj]
    exact hbmem _ ((cpChk_spec hc).2 i hi j hj).1
  have hid : B6.id ∈ G0 := by
    rw [← (ipChk_spec hp).2.1]
    exact hbmem _ (ipChk_spec hp).1
  refine ⟨hnd, hval, hcl, hid, hlen, hmul, hinv, hone, hidB, hkl, ?_⟩
  intro m hm
  rw [hkl, List.mem_range] at hm
  have e := (allLt_iff.1 hv) m hm
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
  rw [hkl, hmul, hinv, hone, List.mem_range]
  exact e

end CFSG.KS.S1277Mod

end
