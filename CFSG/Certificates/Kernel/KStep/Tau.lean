module

public import CFSG.Certificates.Kernel.KStep.Native
public import CFSG.Certificates.Kernel.KStep.Laws
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
public import Certificates.Data.Kernel.KDense.LetterOK
public import Certificates.Data.Kernel.KDense.Plan
public import Certificates.Data.Kernel.KDenseP.Chunk
public import Certificates.Data.Kernel.KDenseP.MonoBind

public section

namespace CFSG.KC.KStep

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371.Native CFSG.KC.MonsterConv.Perm

namespace TauAux

@[expose] def tb : Native.TauTab := Native.mkTauTab ()

theorem filt_sum (L : List (ℕ × ℤ)) (k : ℕ) :
    ((L.filter fun t => decide (t.1 = k)).map Prod.snd).sum =
      (L.map fun t => if t.1 = k then t.2 else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : a.1 = k <;> simp [h, ih]

theorem scat_eq (T : ℕ → List (ℕ × ℤ)) (p k : ℕ) :
    scat T p k = ((T p).map fun t => if t.1 = k then t.2 else 0).sum := filt_sum _ _

@[expose] def TG (p k : ℕ) : Prop :=
  (p < 24 ∧ k = p) ∨ (24 ≤ p ∧ p < 300 ∧ (k = 300 + 2 * (p - 24) ∨ k = 300 + 2 * (p - 24) + 1)) ∨
  (300 ≤ p ∧ p < 852 ∧ (k = 24 + (p - 300) / 2 ∨ k = 300 + 2 * ((p - 300) / 2) ∨
    k = 300 + 2 * ((p - 300) / 2) + 1)) ∨
  (852 ≤ p ∧ p < 50004 ∧ k = 98580 + (2048 + (p - 852) / 24) * 24 + (p - 852) % 24) ∨
  (50004 ≤ p ∧ p < 98580 ∧ 50004 + (p - 50004) / 64 * 64 ≤ k ∧
    k < 50004 + (p - 50004) / 64 * 64 + 64) ∨
  (98580 ≤ p ∧ (p - 98580) / 24 < 2048 ∧ k = 852 + 24 * ((p - 98580) / 24) + (p - 98580) % 24) ∨
  (98580 ≤ p ∧ 2048 ≤ (p - 98580) / 24 ∧
    k = 98580 + ((p - 98580) / 24 - 2048) * 24 + (p - 98580) % 24)

theorem mem_range_map {B k : ℕ} {g : ℕ → ℤ} {t : ℕ × ℤ}
    (ht : t ∈ (List.range 64).map fun q' => (B + q', g q')) (hk : t.1 = k) : B ≤ k ∧ k < B + 64 := by
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 ht
  simp only [List.mem_range] at hq'
  simp only at hk
  omega

theorem tauT_targets {p k : ℕ} {t : ℕ × ℤ} (ht : t ∈ Native.tauT tb p) (hk : t.1 = k) : TG p k := by
  unfold Native.tauT at ht
  unfold TG
  split_ifs at ht with h1 h2 h3 h4 h5 h6 h7
  · simp only [List.mem_singleton] at ht
    subst ht
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> omega
  · simp only [List.mem_singleton] at ht
    subst ht
    omega
  · have := mem_range_map ht hk
    omega
  · simp only [List.mem_singleton] at ht
    subst ht
    omega
  · simp only [List.mem_singleton] at ht
    subst ht
    omega

theorem scat_zero {p k : ℕ} (h : ¬ TG p k) : scat (Native.tauT tb) p k = 0 := by
  rw [scat_eq]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact if_neg fun hk => h (tauT_targets ht hk)

theorem sum_supp {R : Type} [AddCommMonoid R] {N : ℕ} (s : Finset ℕ) (f : ℕ → R)
    (hs : ∀ p ∈ s, p < N) (hz : ∀ p < N, p ∉ s → f p = 0) :
    ∑ p ∈ Finset.range N, f p = ∑ p ∈ s, f p :=
  (Finset.sum_subset (fun p hp => Finset.mem_range.2 (hs p hp))
    (fun p hp hn => hz p (Finset.mem_range.1 hp) hn)).symm

theorem scat_lo {p : ℕ} (h1 : p < 24) (k : ℕ) :
    scat (Native.tauT tb) p k = (if p = k then 8 else 0) + 0 := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_pos h1]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem scat_H {p : ℕ} (h1 : 24 ≤ p) (h2 : p < 300) (k : ℕ) :
    scat (Native.tauT tb) p k = (if 300 + 2 * (p - 24) = k then 8 else 0) +
      ((if 300 + 2 * (p - 24) + 1 = k then -8 else 0) + 0) := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_pos h2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem scat_Xe {p : ℕ} (h1 : 300 ≤ p) (h2 : p < 852) (h3 : (p - 300) % 2 = 0) (k : ℕ) :
    scat (Native.tauT tb) p k = (if 24 + (p - 300) / 2 = k then 4 else 0) +
      ((if 300 + 2 * ((p - 300) / 2) = k then 4 else 0) +
      ((if 300 + 2 * ((p - 300) / 2) + 1 = k then 4 else 0) + 0)) := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_neg (by omega), if_pos h2, if_pos h3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem scat_Xo {p : ℕ} (h1 : 300 ≤ p) (h2 : p < 852) (h3 : (p - 300) % 2 = 1) (k : ℕ) :
    scat (Native.tauT tb) p k = (if 24 + (p - 300) / 2 = k then 4 else 0) +
      ((if 300 + 2 * ((p - 300) / 2) = k then -4 else 0) +
      ((if 300 + 2 * ((p - 300) / 2) + 1 = k then -4 else 0) + 0)) := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_neg (by omega), if_pos h2, if_neg (by omega)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem scat_odd {p : ℕ} (h1 : 852 ≤ p) (h2 : p < 50004) (k : ℕ) :
    scat (Native.tauT tb) p k =
      (if 98580 + (2048 + (p - 852) / 24) * 24 + (p - 852) % 24 = k then
        8 * sgnI (tb.w[(p - 852) / 24]!.testBit ((p - 852) % 24)) else 0) + 0 := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

set_option maxRecDepth 100000 in
theorem scat_Wlo {p : ℕ} (h1 : 98580 ≤ p) (h2 : (p - 98580) / 24 < 2048) (k : ℕ) :
    scat (Native.tauT tb) p k =
      (if 852 + 24 * ((p - 98580) / 24) + (p - 98580) % 24 = k then
        8 * sgnI tb.pb[(p - 98580) / 24]! else 0) + 0 := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

set_option maxRecDepth 100000 in
theorem scat_Whi {p : ℕ} (h1 : 98580 ≤ p) (h2 : 2048 ≤ (p - 98580) / 24) (k : ℕ) :
    scat (Native.tauT tb) p k =
      (if 98580 + ((p - 98580) / 24 - 2048) * 24 + (p - 98580) % 24 = k then
        8 * sgnI (tb.w[(p - 98580) / 24 - 2048]!.testBit ((p - 98580) % 24)) *
          sgnI tb.pb[(p - 98580) / 24 - 2048]! else 0) + 0 := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

theorem sum_range_map (B k : ℕ) (g : ℕ → ℤ) : ∀ n,
    (((List.range n).map fun q' => (B + q', g q')).map fun t => if t.1 = k then t.2 else 0).sum =
      if B ≤ k ∧ k < B + n then g (k - B) else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, sum_range_map B k g n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h : B + n = k
    · rw [if_pos h, if_neg (by omega), if_pos (by omega), zero_add]
      congr 1
      omega
    · rw [if_neg h, add_zero]
      by_cases h' : B ≤ k ∧ k < B + n
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega)]

theorem scat_oct {p : ℕ} (h1 : 50004 ≤ p) (h2 : p < 98580) (k : ℕ) :
    scat (Native.tauT tb) p k =
      if 50004 + (p - 50004) / 64 * 64 ≤ k ∧ k < 50004 + (p - 50004) / 64 * 64 + 64 then
        tb.S[(p - 50004) % 64 * 64 + (k - (50004 + (p - 50004) / 64 * 64))]! else 0 := by
  rw [scat_eq]
  unfold Native.tauT
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2,
    sum_range_map]

variable {M : ℕ}

@[expose] noncomputable def tsum (r : ℕ → ZMod M) (k : ℕ) : ZMod M :=
  ∑ p ∈ Finset.range 196884, ((scat (Native.tauT tb) p k : ℤ) : ZMod M) * r p

theorem tsum_diag (r : ℕ → ZMod M) {k : ℕ} (hk : k < 24) : tsum r k = 8 * r k := by
  unfold tsum
  rw [sum_supp {k} _ (fun p hp => by simp at hp; omega) fun p hp hn => by
    rw [scat_zero (by simp at hn; unfold TG; omega)]; simp, Finset.sum_singleton,
    scat_lo hk, if_pos rfl]
  simp

theorem tsum_pairA (r : ℕ → ZMod M) {tp : ℕ} (htp : tp < 276) :
    tsum r (24 + tp) = 4 * r (300 + 2 * tp) + 4 * r (300 + 2 * tp + 1) := by
  unfold tsum
  rw [sum_supp {300 + 2 * tp, 300 + 2 * tp + 1} _ (fun p hp => by simp at hp; omega)
    fun p hp hn => by rw [scat_zero (by simp at hn; unfold TG; omega)]; simp,
    Finset.sum_pair (by omega), scat_Xe (by omega) (by omega) (by omega),
    scat_Xo (by omega) (by omega) (by omega)]
  have e1 : (if 24 + (300 + 2 * tp - 300) / 2 = 24 + tp then (4 : ℤ) else 0) +
      ((if 300 + 2 * ((300 + 2 * tp - 300) / 2) = 24 + tp then 4 else 0) +
      ((if 300 + 2 * ((300 + 2 * tp - 300) / 2) + 1 = 24 + tp then 4 else 0) + 0)) = 4 := by
    split_ifs <;> omega
  have e2 : (if 24 + (300 + 2 * tp + 1 - 300) / 2 = 24 + tp then (4 : ℤ) else 0) +
      ((if 300 + 2 * ((300 + 2 * tp + 1 - 300) / 2) = 24 + tp then -4 else 0) +
      ((if 300 + 2 * ((300 + 2 * tp + 1 - 300) / 2) + 1 = 24 + tp then -4 else 0) + 0)) = 4 := by
    split_ifs <;> omega
  rw [e1, e2]
  simp

theorem tsum_pairX (r : ℕ → ZMod M) {tp : ℕ} (htp : tp < 276) :
    tsum r (300 + 2 * tp) = 8 * r (24 + tp) + 4 * r (300 + 2 * tp) - 4 * r (300 + 2 * tp + 1) := by
  unfold tsum
  rw [sum_supp {24 + tp, 300 + 2 * tp, 300 + 2 * tp + 1} _ (fun p hp => by simp at hp; omega)
    fun p hp hn => by rw [scat_zero (by simp at hn; unfold TG; omega)]; simp,
    Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega), scat_H (by omega) (by omega),
    scat_Xe (by omega) (by omega) (by omega), scat_Xo (by omega) (by omega) (by omega)]
  have e0 : (if 300 + 2 * (24 + tp - 24) = 300 + 2 * tp then (8 : ℤ) else 0) +
      ((if 300 + 2 * (24 + tp - 24) + 1 = 300 + 2 * tp then -8 else 0) + 0) = 8 := by
    split_ifs <;> omega
  have e1 : (if 24 + (300 + 2 * tp - 300) / 2 = 300 + 2 * tp then (4 : ℤ) else 0) +
      ((if 300 + 2 * ((300 + 2 * tp - 300) / 2) = 300 + 2 * tp then 4 else 0) +
      ((if 300 + 2 * ((300 + 2 * tp - 300) / 2) + 1 = 300 + 2 * tp then 4 else 0) + 0)) = 4 := by
    split_ifs <;> omega
  have e2 : (if 24 + (300 + 2 * tp + 1 - 300) / 2 = 300 + 2 * tp then (4 : ℤ) else 0) +
      ((if 300 + 2 * ((300 + 2 * tp + 1 - 300) / 2) = 300 + 2 * tp then -4 else 0) +
      ((if 300 + 2 * ((300 + 2 * tp + 1 - 300) / 2) + 1 = 300 + 2 * tp then -4 else 0) + 0)) =
        -4 := by
    split_ifs <;> omega
  rw [e0, e1, e2]
  push_cast
  ring

theorem tsum_pairX1 (r : ℕ → ZMod M) {tp : ℕ} (htp : tp < 276) :
    tsum r (300 + 2 * tp + 1) =
      -(8 * r (24 + tp)) + 4 * r (300 + 2 * tp) - 4 * r (300 + 2 * tp + 1) := by
  unfold tsum
  rw [sum_supp {24 + tp, 300 + 2 * tp, 300 + 2 * tp + 1} _ (fun p hp => by simp at hp; omega)
    fun p hp hn => by rw [scat_zero (by simp at hn; unfold TG; omega)]; simp,
    Finset.sum_insert (by simp; omega), Finset.sum_pair (by omega), scat_H (by omega) (by omega),
    scat_Xe (by omega) (by omega) (by omega), scat_Xo (by omega) (by omega) (by omega)]
  have e0 : (if 300 + 2 * (24 + tp - 24) = 300 + 2 * tp + 1 then (8 : ℤ) else 0) +
      ((if 300 + 2 * (24 + tp - 24) + 1 = 300 + 2 * tp + 1 then -8 else 0) + 0) = -8 := by
    split_ifs <;> omega
  have e1 : (if 24 + (300 + 2 * tp - 300) / 2 = 300 + 2 * tp + 1 then (4 : ℤ) else 0) +
      ((if 300 + 2 * ((300 + 2 * tp - 300) / 2) = 300 + 2 * tp + 1 then 4 else 0) +
      ((if 300 + 2 * ((300 + 2 * tp - 300) / 2) + 1 = 300 + 2 * tp + 1 then 4 else 0) + 0)) =
        4 := by
    split_ifs <;> omega
  have e2 : (if 24 + (300 + 2 * tp + 1 - 300) / 2 = 300 + 2 * tp + 1 then (4 : ℤ) else 0) +
      ((if 300 + 2 * ((300 + 2 * tp + 1 - 300) / 2) = 300 + 2 * tp + 1 then -4 else 0) +
      ((if 300 + 2 * ((300 + 2 * tp + 1 - 300) / 2) + 1 = 300 + 2 * tp + 1 then -4 else 0) +
        0)) = -4 := by
    split_ifs <;> omega
  rw [e0, e1, e2]
  push_cast
  ring

theorem tsum_odd (r : ℕ → ZMod M) {t i : ℕ} (ht : t < 2048) (hi : i < 24) :
    tsum r (852 + 24 * t + i) = ((8 * sgnI tb.pb[t]! : ℤ) : ZMod M) * r (98580 + 24 * t + i) := by
  unfold tsum
  rw [sum_supp {98580 + 24 * t + i} _ (fun p hp => by simp at hp; omega) fun p hp hn => by
    rw [scat_zero (by simp at hn; unfold TG; omega)]; simp, Finset.sum_singleton,
    scat_Wlo (by omega) (by omega)]
  have e1 : (98580 + 24 * t + i - 98580) / 24 = t := by omega
  rw [e1, if_pos (by omega), add_zero]

theorem tsum_Wlo (r : ℕ → ZMod M) {t j : ℕ} (ht : t < 2048) (hj : j < 24) :
    tsum r (98580 + 24 * t + j) = ((8 * sgnI (tb.w[t]!.testBit j) * sgnI tb.pb[t]! : ℤ) : ZMod M) *
      r (98580 + 24 * (2048 + t) + j) := by
  unfold tsum
  rw [sum_supp {98580 + 24 * (2048 + t) + j} _ (fun p hp => by simp at hp; omega) fun p hp hn => by
    rw [scat_zero (by simp at hn; unfold TG; omega)]; simp, Finset.sum_singleton,
    scat_Whi (by omega) (by omega)]
  have e1 : (98580 + 24 * (2048 + t) + j - 98580) / 24 - 2048 = t := by omega
  have e2 : (98580 + 24 * (2048 + t) + j - 98580) % 24 = j := by omega
  rw [e1, e2, if_pos (by omega), add_zero]

theorem tsum_Whi (r : ℕ → ZMod M) {t j : ℕ} (ht : t < 2048) (hj : j < 24) :
    tsum r (98580 + 24 * (2048 + t) + j) =
      ((8 * sgnI (tb.w[t]!.testBit j) : ℤ) : ZMod M) * r (852 + 24 * t + j) := by
  unfold tsum
  rw [sum_supp {852 + 24 * t + j} _ (fun p hp => by simp at hp; omega) fun p hp hn => by
    rw [scat_zero (by simp at hn; unfold TG; omega)]; simp, Finset.sum_singleton,
    scat_odd (by omega) (by omega)]
  have e1 : (852 + 24 * t + j - 852) / 24 = t := by omega
  have e2 : (852 + 24 * t + j - 852) % 24 = j := by omega
  rw [e1, e2, if_pos (by omega), add_zero]

theorem tsum_oct (r : ℕ → ZMod M) {o n : ℕ} (ho : o < 759) (hn : n < 64) :
    tsum r (50004 + 64 * o + n) =
      ∑ m ∈ Finset.range 64, ((tb.S[m * 64 + n]! : ℤ) : ZMod M) * r (50004 + 64 * o + m) := by
  unfold tsum
  rw [sum_supp ((Finset.range 64).image (50004 + 64 * o + ·)) _
    (fun p hp => by simp at hp; omega) fun p hp hn' => by
      rw [scat_zero]
      · simp
      · simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hn'
        unfold TG
        intro h
        have := hn' (p - (50004 + 64 * o)) (by omega)
        omega,
    Finset.sum_image (fun a _ b _ h => by simpa using h)]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rw [scat_oct (by omega) (by omega), if_pos (by omega)]
  have e1 : (50004 + 64 * o + m - 50004) % 64 = m := by omega
  have e2 : 50004 + 64 * o + n - (50004 + (50004 + 64 * o + m - 50004) / 64 * 64) = n := by omega
  rw [e1, e2]

theorem tb_w {t : ℕ} (ht : t < 2048) : tb.w[t]! = wordN (2 * t) := by
  unfold tb Native.mkTauTab
  dsimp only
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_ofFn]

theorem tb_pb {t : ℕ} (ht : t < 2048) : tb.pb[t]! = pN (2 * t) := by
  unfold tb Native.mkTauTab
  dsimp only
  rw [getElem!_pos _ t (by simpa using ht), Array.getElem_ofFn]

theorem tb_S {k : ℕ} (hk : k < 4096) :
    tb.S[k]! = octSign (Native.evenTab ())[k / 64]! (Native.evenTab ())[k % 64]! := by
  unfold tb Native.mkTauTab
  dsimp only
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

variable {np : ℕ} {O : POps}

theorem res_of_zero {S x p : ℕ} (h : Zero np S x p) : resPN np S x p = 0 :=
  (resPN_congr (y := 0) fun b hb => by rw [h b hb, Nat.zero_testBit]).trans (resPN_zero np S p)

theorem res_lor_l {S x y p : ℕ} (hp : p < S) (hy : Zero np S y p) :
    resPN np S (Nat.lor x y) p = resPN np S x p := by
  rw [show Nat.lor x y = x ||| y from rfl, res_lor hp (Or.inr hy), res_of_zero hy, add_zero]

theorem res_lor_r {S x y p : ℕ} (hp : p < S) (hx : Zero np S x p) :
    resPN np S (Nat.lor x y) p = resPN np S y p := by
  rw [show Nat.lor x y = x ||| y from rfl, res_lor hp (Or.inl hx), res_of_zero hx, zero_add]

theorem zero_lor {S x y p : ℕ} (hx : Zero np S x p) (hy : Zero np S y p) :
    Zero np S (Nat.lor x y) p := fun b hb => by
  change (x ||| y).testBit _ = false
  rw [Nat.testBit_or, hx b hb, hy b hb]
  rfl

theorem zero_land_l {S x y p : ℕ} (hx : Zero np S x p) : Zero np S (Nat.land x y) p := fun b hb => by
  change (x &&& y).testBit _ = false
  rw [Nat.testBit_and, hx b hb, Bool.false_and]

theorem zero_land_rep (hO : PLaw np O) {S m x p : ℕ} (hm : m < 2 ^ S) (hp : p < S)
    (hb : m.testBit p = false) : Zero np S (Nat.land x (O.rep S m)) p := fun b hb' => by
  change (x &&& O.rep S m).testBit _ = false
  rw [Nat.testBit_and, hO.rep_testBit hm hb' hp, hb, Bool.and_false]

theorem res_land_rep' (hO : PLaw np O) {S m x p : ℕ} (hm : m < 2 ^ S) (hp : p < S) :
    resPN np S (Nat.land x (O.rep S m)) p = if m.testBit p then resPN np S x p else 0 :=
  res_land_rep hO hm hp

theorem rep_Rep (hO : PLaw np O) {S m : ℕ} (hm : m < 2 ^ S) (hS : 0 < S) :
    Benes.Rep S np (O.rep S m) m := fun q => by
  by_cases hq : q < S * np
  · have hb : q / S < np := (Nat.div_lt_iff_lt_mul hS).2 (by rw [Nat.mul_comm]; exact hq)
    have e : q = q / S * S + q % S := (Nat.div_add_mod' q S).symm
    rw [decide_eq_true hq, Bool.true_and]
    conv_lhs => rw [e]
    exact hO.rep_testBit hm hb (Nat.mod_lt _ hS)
  · rw [decide_eq_false hq, Bool.false_and]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hO.rep_lt hm)
      (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm]; omega)))

theorem testBit_dsw_rep (hO : PLaw np O) {S d m : ℕ} (hv : Benes.ValidIn S d m) (hS : 0 < S)
    (y : ℕ) {u r : ℕ} (hu : u < np) (hr : r < S) :
    (dsw d (O.rep S m) y).testBit (S * u + r) = y.testBit (S * u + Benes.swp d m r) := by
  have hR := rep_Rep hO (Benes.lt_of_validIn hv) hS (np := np)
  rw [Benes.testBit_dsw (Benes.rep_disj hR hv), Benes.swp_rep hR hv hu hr]

theorem SX_eq : SX = 2 ^ 17 := rfl

theorem SA_eq : SA = 2 ^ 10 := rfl

theorem recS_succ (g : ℕ → ℕ → ℕ) (n x : ℕ) :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y) (fun k ih y => CFSG.KC.Loop.strictN (g k y) ih)
      (n + 1) x) = Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y)
        (fun k ih y => CFSG.KC.Loop.strictN (g k y) ih) n (g n x) :=
  Benes.strictN_eq _ _

open CFSG.KC.KDense.InitAux in
theorem lo16_bit (p : ℕ) : lo16.testBit p = decide (p < 65536) := testBit_ones' _ _

theorem lt_of_bits {x S : ℕ} (h : ∀ p, x.testBit p = true → p < S) : x < 2 ^ S :=
  Nat.lt_pow_two_of_testBit _ fun p hp => by
    cases e : x.testBit p
    · rfl
    · have := h p e
      omega

theorem lo16_lt : lo16 < 2 ^ SX := lt_of_bits fun p hp => by
  rw [lo16_bit] at hp
  simp at hp
  change p < 131072
  omega

theorem lo16_lt' : lo16 < 2 ^ (SX - 65536) := lt_of_bits fun p hp => by
  rw [lo16_bit] at hp
  simp at hp
  change p < 131072 - 65536
  omega

open CFSG.KC.KDense.InitAux in
theorem regOct_lt : regOct < 2 ^ SX := lt_of_bits fun p hp => by
  rw [testBit_regOct] at hp
  change p < 131072
  omega

open CFSG.KC.KDense.InitAux in
theorem upA_lt : upA < 2 ^ SA := lt_of_bits fun p hp => by
  by_contra hc
  have e : p = 1024 + (p - 1024) := by change ¬ p < 1024 at hc; omega
  rw [e, ← Nat.testBit_shiftRight, upA_shr, Nat.zero_testBit] at hp
  exact Bool.false_ne_true hp

theorem diagA_bits : ∀ x < 1024, diagA.testBit x = decide (x / 32 = x % 32 ∧ x % 32 < 24) := by
  decide +kernel

theorem diagA_lt : diagA < 2 ^ SA := by decide +kernel

open CFSG.KC.KDense.InitAux in
theorem oct_closed {b : ℕ} (hb : b < 6) : ∀ q < SX, regOct.testBit q = true → q.testBit b = false →
    regOct.testBit (q + 2 ^ b) = true := by
  intro q _ h1 h2
  rw [testBit_regOct] at h1 ⊢
  rw [Nat.testBit_eq_decide_div_mod_eq] at h2
  simp only [decide_eq_false_iff_not] at h2
  interval_cases b <;> simp at h2 <;> omega

@[expose] noncomputable def Hn (O : POps) (n x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y)
    (fun b ih y => CFSG.KC.Loop.strictN (O.bfly SX b regOct y) ih) n x

theorem Hn_succ (O : POps) (n x : ℕ) : Hn O (n + 1) x = Hn O n (O.bfly SX n regOct x) :=
  recS_succ (fun b y => O.bfly SX b regOct y) n x

@[expose] def Kz (n q c : ℕ) : ℤ :=
  if c >>> n = q >>> n then (if popcN n (c &&& q) % 2 = 0 then 1 else -1) else 0

theorem Kz_step : ∀ n < 6, ∀ q < 64, ∀ c < 64,
    Kz (n + 1) q c = Kz n q c * (if c.testBit n then -1 else 1) + Kz n q (c ^^^ 2 ^ n) := by
  decide +kernel

theorem Kz_zero : ∀ q < 64, ∀ c < 64, Kz 0 q c = if q = c then 1 else 0 := by decide +kernel

theorem xor_bit : ∀ n < 6, ∀ c < 64, c ^^^ 2 ^ n < 64 ∧
    (c.testBit n = false → c ^^^ 2 ^ n = c + 2 ^ n) ∧
    (c.testBit n = true → 2 ^ n ≤ c ∧ c ^^^ 2 ^ n = c - 2 ^ n) := by
  decide +kernel

theorem Hn_bd (hO : PLaw np O) : ∀ n ≤ 6, ∀ x, Bd np SX x → Bd np SX (Hn O n x)
  | 0, _, _, hx => hx
  | n + 1, hn, x, hx => by
    rw [Hn_succ]
    exact Hn_bd hO n (by omega) _ (hO.bfly_bd (k := 17) (b := n) SX_eq (by omega) regOct_lt hx)

theorem Hn_zero (hO : PLaw np O) {p : ℕ} (hp : p < SX) (hr : regOct.testBit p = false) :
    ∀ n ≤ 6, ∀ x, Bd np SX x → Zero np SX x p → Zero np SX (Hn O n x) p
  | 0, _, _, _, hz => hz
  | n + 1, hn, x, hx, hz => by
    rw [Hn_succ]
    exact Hn_zero hO hp hr n (by omega) _ (hO.bfly_bd (k := 17) (b := n) SX_eq (by omega) regOct_lt hx)
      (hO.bfly_zero (k := 17) (b := n) SX_eq (by omega) regOct_lt (oct_closed (by omega)) hx hp hr hz)

theorem bit_blk {B c : ℕ} (hc : c < 64) {n : ℕ} (hn : n < 6) :
    (64 * B + c).testBit n = c.testBit n := by
  rw [show 64 * B + c = 2 ^ 6 * B + c from rfl, Nat.testBit_two_pow_mul_add B (by simpa using hc),
    if_pos hn]

open CFSG.KC.KDense.InitAux in
theorem bfly_blk (hO : PLaw np O) {n x B c : ℕ} (hn : n < 6) (hx : Bd np SX x) (hB1 : 1024 ≤ B)
    (hB2 : B < 1783) (hc : c < 64) :
    resPN np SX (O.bfly SX n regOct x) (64 * B + c) =
      ((if c.testBit n then -1 else 1 : ℤ) : ZMod (2 ^ np - 1)) * resPN np SX x (64 * B + c) +
        resPN np SX x (64 * B + (c ^^^ 2 ^ n)) := by
  obtain ⟨-, h1, h2⟩ := xor_bit n hn c hc
  have r1 : regOct.testBit (64 * B + c) = true := by rw [testBit_regOct]; omega
  rw [hO.bfly_res (k := 17) SX_eq (by omega) regOct_lt (oct_closed hn) hx (by change _ < 131072; omega),
    r1, bit_blk hc hn]
  rw [if_neg (by simp)]
  cases e : c.testBit n
  · rw [if_pos rfl, h1 e]
    simp only [Bool.false_eq_true, if_false, Int.cast_one, one_mul]
    rw [Nat.add_assoc]
  · obtain ⟨h3, h4⟩ := h2 e
    have h5 : 2 ^ n ≤ 32 := by interval_cases n <;> decide
    have r2 : regOct.testBit (64 * B + c - 2 ^ n) = true := by
      rw [testBit_regOct]
      generalize 2 ^ n = d at h3 h5 ⊢
      omega
    rw [if_neg (by simp), r2, if_pos rfl, h4]
    simp only [if_true, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [show 64 * B + c - 2 ^ n = 64 * B + (c - 2 ^ n) by omega]
    ring

theorem Hn_res (hO : PLaw np O) : ∀ n ≤ 6, ∀ x, Bd np SX x → ∀ B, 1024 ≤ B → B < 1783 →
    ∀ q < 64, resPN np SX (Hn O n x) (64 * B + q) =
      ∑ c ∈ Finset.range 64, ((Kz n q c : ℤ) : ZMod (2 ^ np - 1)) * resPN np SX x (64 * B + c)
  | 0, _, x, _, B, _, _, q, hq => by
    rw [Finset.sum_congr rfl fun c hc => by rw [Kz_zero q hq c (Finset.mem_range.1 hc)]]
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_range, if_pos hq]
    rfl
  | n + 1, hn, x, hx, B, hB1, hB2, q, hq => by
    have hy := hO.bfly_bd (k := 17) (b := n) SX_eq (by omega) regOct_lt hx
    rw [Hn_succ, Hn_res hO n (by omega) _ hy B hB1 hB2 q hq]
    rw [Finset.sum_congr rfl fun c hc => by
      rw [bfly_blk hO (by omega) hx hB1 hB2 (Finset.mem_range.1 hc), mul_add]]
    rw [Finset.sum_add_distrib]
    have hre : ∑ c ∈ Finset.range 64, ((Kz n q c : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX x (64 * B + (c ^^^ 2 ^ n)) = ∑ c ∈ Finset.range 64,
          ((Kz n q (c ^^^ 2 ^ n) : ℤ) : ZMod (2 ^ np - 1)) * resPN np SX x (64 * B + c) := by
      refine Finset.sum_nbij' (fun c => c ^^^ 2 ^ n) (fun c => c ^^^ 2 ^ n)
        (fun c hc => Finset.mem_range.2 (xor_bit n (by omega) c (Finset.mem_range.1 hc)).1)
        (fun c hc => Finset.mem_range.2 (xor_bit n (by omega) c (Finset.mem_range.1 hc)).1)
        (fun c _ => by simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])
        (fun c _ => by simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])
        (fun c _ => by simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])
    rw [hre, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Kz_step n (by omega) q hq c (Finset.mem_range.1 hc)]
    push_cast
    ring

theorem wht6G_eq (O : POps) (x : ℕ) : wht6G O x = Hn O 6 x := rfl

@[expose] def xs (r k : ℕ) : Bool := Nat.rec (motive := fun _ => Bool) false (fun i acc => acc ^^ r.testBit i) k

theorem testBit_xorP : ∀ k ≤ 17, ∀ s < SX,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (idPlane SX i)) k).testBit s =
      xs s k
  | 0, _, s, _ => Nat.zero_testBit s
  | k + 1, hk, s, hs => by
    change (Nat.xor (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (idPlane SX i)) k)
      (idPlane SX k)).testBit s = (xs s k ^^ s.testBit k)
    rw [show Nat.xor _ _ = _ ^^^ _ from rfl, Nat.testBit_xor, testBit_xorP k (by omega) s hs, SX_eq,
      Benes.idPlane_testBit (by omega), decide_eq_true (by rw [← SX_eq]; exact hs), Bool.true_and]

open CFSG.KC.KDense.InitAux in
theorem testBit_idP17 {u r : ℕ} (hu : u < 17) (hr : r < SX) :
    (idP 17).testBit (SX * u + r) = r.testBit u := by
  have e : idP 17 = Nat.rec (motive := fun _ => ℕ) 0 (fun b a => Nat.lor a
      ((fun b => Nat.shiftLeft (idPlane (2 ^ 17) b) (b * 2 ^ 17)) b)) 17 := rfl
  rw [e, Bool.eq_iff_iff, testBit_foldOr]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, testBit_shl]
  change r < 131072 at hr
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    rw [Benes.idPlane_testBit hb] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have h1' : b * 131072 ≤ 131072 * u + r := h1
    have h2' : 131072 * u + r - b * 131072 < 131072 := h2.1
    have hbu : b = u := by omega
    subst hbu
    have e2 : SX * b + r - b * 2 ^ 17 = r := by change 131072 * b + r - b * 131072 = r; omega
    rw [e2] at h2
    exact h2.2
  · intro h
    refine ⟨u, hu, by change u * 131072 ≤ 131072 * u + r; omega, ?_⟩
    have e2 : SX * u + r - u * 2 ^ 17 = r := by change 131072 * u + r - u * 131072 = r; omega
    rw [e2, Benes.idPlane_testBit hu, decide_eq_true (by change r < 131072; omega), Bool.true_and, h]

@[expose] noncomputable def mk6 : ℕ :=
  Nat.land regOct (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.xor acc (idPlane SX i)) 6)

open CFSG.KC.KDense.InitAux in
theorem testBit_mk6 {s : ℕ} (hs : s < SX) :
    mk6.testBit s = (decide (65536 ≤ s ∧ s < 114112) && xs s 6) := by
  unfold mk6
  rw [show Nat.land _ _ = _ &&& _ from rfl, Nat.testBit_and, testBit_xorP 6 (by omega) s hs]
  congr 1
  rw [Bool.eq_iff_iff, testBit_regOct, decide_eq_true_eq]

theorem xs_blk : ∀ c < 64, xs c 6 = xs (c ^^^ 63) 6 ∧ c ^^^ 63 < 64 := by decide +kernel

theorem xs6 (r : ℕ) : xs r 6 = (((((((false ^^ r.testBit 0) ^^ r.testBit 1) ^^ r.testBit 2) ^^
    r.testBit 3) ^^ r.testBit 4) ^^ r.testBit 5)) := rfl

theorem xs_eq_blk {B c : ℕ} (hc : c < 64) : xs (64 * B + c) 6 = xs c 6 := by
  rw [xs6, xs6]
  simp only [bit_blk hc (show 0 < 6 by omega), bit_blk hc (show 1 < 6 by omega),
    bit_blk hc (show 2 < 6 by omega), bit_blk hc (show 3 < 6 by omega),
    bit_blk hc (show 4 < 6 by omega), bit_blk hc (show 5 < 6 by omega)]

theorem xor63_blk {B c : ℕ} (hc : c < 64) : (64 * B + c) ^^^ 63 = 64 * B + (c ^^^ 63) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h63 : c ^^^ 63 < 2 ^ 6 := (xs_blk c hc).2
  rw [Nat.testBit_xor, show 64 * B + c = 2 ^ 6 * B + c from rfl,
    show 64 * B + (c ^^^ 63) = 2 ^ 6 * B + (c ^^^ 63) from rfl,
    Nat.testBit_two_pow_mul_add B (by simpa using hc), Nat.testBit_two_pow_mul_add B h63]
  split_ifs with h
  · rw [Nat.testBit_xor]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 63 < 2 ^ 6 by decide)
      (Nat.pow_le_pow_right (by decide) (by omega))), Bool.xor_false]

@[expose] noncomputable def phi (r : ℕ) : ℕ := if mk6.testBit r then r ^^^ 63 else r

theorem phi_lt {r : ℕ} (hr : r < SX) : phi r < SX := by
  unfold phi
  split_ifs with h
  · rw [testBit_mk6 hr] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have e := Nat.div_add_mod r 64
    have hc : r % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [← e, xor63_blk hc]
    have := (xs_blk _ hc).2
    change _ < 131072
    omega
  · exact hr

theorem mk6_phi {r : ℕ} (hr : r < SX) : mk6.testBit (phi r) = mk6.testBit r := by
  unfold phi
  split_ifs with h
  · have h' := h
    rw [testBit_mk6 hr] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have e := Nat.div_add_mod r 64
    have hc : r % 64 < 64 := Nat.mod_lt _ (by decide)
    have hb := xs_blk _ hc
    rw [h', ← e, xor63_blk hc, testBit_mk6 (by rw [e] at *; have := hb.2; change _ < 131072; omega),
      xs_eq_blk hb.2, ← hb.1, decide_eq_true (by omega), Bool.true_and]
    rw [← xs_eq_blk (B := r / 64) hc, e]
    exact h.2
  · rfl

open CFSG.KC.KDense.InitAux in
theorem pi6_perm {F : Fix} (h6 : pi6OK F = true) {r : ℕ} (hr : r < SX) :
    Benes.benesPerm 17 F.pi6 r = phi r := by
  obtain ⟨hok, heq⟩ := Benes.andB_true h6
  rw [Nat.beq_eq] at heq
  change netP SX 17 17 F.pi6 (Nat.xor (idP 17) (repP SX 6 mk6)) = idP 17 at heq
  have hnet := (Benes.testBit_netP (S := SX) (n := 17) SX_eq hok
    (Nat.xor (idP 17) (repP SX 6 mk6))).1
  rw [heq] at hnet
  have hsv := Benes.stagesValid_of_netOK hok
  set s := Benes.benesPerm 17 F.pi6 r with hs_def
  have hs : s < SX := Benes.benesPerm_lt hsv (by rw [← SX_eq]; exact hr)
  have hmk : ∀ p, mk6.testBit p = true → p < SX := by
    intro p hp
    unfold mk6 at hp
    rw [show Nat.land _ _ = _ &&& _ from rfl, Nat.testBit_and, Bool.and_eq_true,
      testBit_regOct] at hp
    change p < 131072
    omega
  have hR := Benes.rep_repP hmk 6
  have key : ∀ u < 17, r.testBit u = (s.testBit u ^^ (decide (u < 6) && mk6.testBit s)) := by
    intro u hu
    have := hnet u hu r hr
    rw [testBit_idP17 hu hr] at this
    rw [this, show Nat.xor _ _ = _ ^^^ _ from rfl, Nat.testBit_xor, testBit_idP17 hu hs, hR,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
    congr 2
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · intro h
      by_contra hc
      have : SX * 6 ≤ SX * u := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro h
      have : SX * (u + 1) ≤ SX * 6 := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this
      omega
  have hbig : ∀ x, x < SX → ∀ u, 17 ≤ u → x.testBit u = false := fun x hx u hu =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (by rw [SX_eq]; exact Nat.pow_le_pow_right (by decide) hu))
  cases hm : mk6.testBit s
  · have ers : r = s := by
      apply Nat.eq_of_testBit_eq
      intro u
      by_cases hu : u < 17
      · rw [key u hu, hm, Bool.and_false, Bool.xor_false]
      · rw [hbig r hr u (by omega), hbig s hs u (by omega)]
    rw [← ers] at hm
    unfold phi
    rw [hm, if_neg (by simp), ers]
  · have ers : r = s ^^^ 63 := by
      apply Nat.eq_of_testBit_eq
      intro u
      rw [Nat.testBit_xor]
      by_cases hu : u < 17
      · rw [key u hu, hm, Bool.and_true]
        congr 1
        by_cases h6 : u < 6
        · rw [decide_eq_true h6]
          interval_cases u <;> rfl
        · rw [decide_eq_false h6, Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 63 < 2 ^ 6 by decide)
            (Nat.pow_le_pow_right (by decide) (by omega)))]
      · rw [hbig r hr u (by omega), hbig s hs u (by omega), Nat.testBit_lt_two_pow
          (lt_of_lt_of_le (show 63 < 2 ^ 6 by decide) (Nat.pow_le_pow_right (by decide) (by omega)))]
        rfl
    have hphi : phi s = r := by unfold phi; rw [hm, if_pos rfl, ers]
    have hm' : mk6.testBit r = true := by rw [← hphi, mk6_phi hs, hm]
    unfold phi
    rw [hm', if_pos rfl, ers, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

@[expose] noncomputable def POCT : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight
      (Nat.add (popcT (nat_lit 6) q) (parT (nat_lit 6) q)) (nat_lit 1)) (nat_lit 1)) q)) (nat_lit 64)

@[expose] noncomputable def rowF (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun t acc => Nat.lor acc (Nat.shiftLeft (g t) (Nat.mul 32 t))) n

@[expose] noncomputable def gU (t : ℕ) : ℕ := wordT (Nat.shiftLeft t 1)

@[expose] noncomputable def gL (t : ℕ) : ℕ := selB (pT (Nat.shiftLeft t 1)) 16777215

@[expose] noncomputable def gH (t : ℕ) : ℕ :=
  Nat.xor (wordT (Nat.shiftLeft t 1)) (selB (pT (Nat.shiftLeft t 1)) 16777215)

theorem tri_fold : ∀ n,
    Nat.rec (motive := fun _ => Nat × Nat × Nat) (nat_lit 0, nat_lit 0, nat_lit 0)
        (fun t ih => (fun w p => Prod.rec (motive := fun _ => Nat × Nat × Nat) (fun u r => Prod.rec
            (motive := fun _ => Nat × Nat × Nat) (fun lo up =>
              (Nat.lor u (Nat.shiftLeft w (Nat.mul (nat_lit 32) t)),
               Nat.lor lo (Nat.shiftLeft (selB p (nat_lit 16777215)) (Nat.mul (nat_lit 32) t)),
               Nat.lor up (Nat.shiftLeft (Nat.xor w (selB p (nat_lit 16777215)))
                 (Nat.mul (nat_lit 32) t)))) r) ih)
          (wordT (Nat.shiftLeft t (nat_lit 1))) (pT (Nat.shiftLeft t (nat_lit 1)))) n =
      (rowF gU n, rowF gL n, rowF gH n)
  | 0 => rfl
  | n + 1 => by
    change (fun w p => Prod.rec (motive := fun _ => Nat × Nat × Nat) (fun u r => Prod.rec
            (motive := fun _ => Nat × Nat × Nat) (fun lo up =>
              (Nat.lor u (Nat.shiftLeft w (Nat.mul (nat_lit 32) n)),
               Nat.lor lo (Nat.shiftLeft (selB p (nat_lit 16777215)) (Nat.mul (nat_lit 32) n)),
               Nat.lor up (Nat.shiftLeft (Nat.xor w (selB p (nat_lit 16777215)))
                 (Nat.mul (nat_lit 32) n)))) r) _)
          (wordT (Nat.shiftLeft n (nat_lit 1))) (pT (Nat.shiftLeft n (nat_lit 1))) = _
    rw [tri_fold n]
    rfl

theorem masks_spec {F : Fix} (hm : tauMasksOK F = true) :
    F.doct = Nat.shiftLeft (Nat.mul POCT (Nat.div (ones (nat_lit 48576)) (ones (nat_lit 64))))
      (nat_lit 65536) ∧ F.sgOddUp = rowF gU 2048 ∧ F.sgWLo = rowF gL 2048 ∧
      F.sgWUp = rowF gH 2048 := by
  unfold tauMasksOK at hm
  generalize hN : nat_lit 2048 = N at hm
  rw [tri_fold N] at hm
  subst hN
  have hb : ∀ a b : Bool, andB a b = (a && b) := fun a b => by cases a <;> rfl
  dsimp only at hm
  simp only [hb, Bool.and_eq_true, Nat.beq_eq] at hm
  exact ⟨hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩

open CFSG.KC.KDense.InitAux in
theorem testBit_rowF {g : ℕ → ℕ} {n : ℕ} (hg : ∀ t < n, g t < 2 ^ 24) (y : ℕ) :
    (rowF g n).testBit y = (decide (y / 32 < n) && decide (y % 32 < 24) &&
      (g (y / 32)).testBit (y % 32)) := by
  unfold rowF
  rw [Bool.eq_iff_iff, testBit_foldOr (fun t => Nat.shiftLeft (g t) (Nat.mul 32 t))]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, testBit_shl, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    have h3 : y - Nat.mul 32 t < 24 := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hg t ht) (Nat.pow_le_pow_right (by decide)
        (by omega)))] at h2
      exact Bool.false_ne_true h2
    change 32 * t ≤ y at h1
    change y - 32 * t < 24 at h3
    have e1 : y / 32 = t := by omega
    have e2 : y % 32 = y - Nat.mul 32 t := by change _ = y - 32 * t; omega
    rw [e1, e2]
    exact ⟨⟨by omega, by omega⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨y / 32, h1, by change 32 * (y / 32) ≤ y; omega, ?_⟩
    have e2 : y - Nat.mul 32 (y / 32) = y % 32 := by change y - 32 * (y / 32) = _; omega
    rw [e2]
    exact h3

theorem tw_ok : ∀ t < 2048, wordT (Nat.shiftLeft t 1) = wordN (2 * t) ∧ wordN (2 * t) < 2 ^ 24 ∧
    pT (Nat.shiftLeft t 1) = (pN (2 * t)).toNat := by
  decide +kernel

theorem selB_bit (b : Bool) (j : ℕ) :
    (selB b.toNat 16777215).testBit j = (b && decide (j < 24)) := by
  cases b
  · change Nat.testBit (0 * 16777215) j = _
    simp
  · change Nat.testBit (1 * 16777215) j = _
    rw [Nat.one_mul, show (16777215 : ℕ) = 2 ^ 24 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    rfl

theorem selB_lt (b : Bool) : selB b.toNat 16777215 < 2 ^ 24 := by cases b <;> decide

theorem gU_bit {t : ℕ} (ht : t < 2048) (j : ℕ) : (gU t).testBit j = (wordN (2 * t)).testBit j := by
  unfold gU
  rw [(tw_ok t ht).1]

theorem gL_bit {t j : ℕ} (ht : t < 2048) (hj : j < 24) : (gL t).testBit j = pN (2 * t) := by
  unfold gL
  rw [(tw_ok t ht).2.2, selB_bit, decide_eq_true hj, Bool.and_true]

theorem gH_bit {t j : ℕ} (ht : t < 2048) (hj : j < 24) :
    (gH t).testBit j = ((wordN (2 * t)).testBit j ^^ pN (2 * t)) := by
  unfold gH
  rw [(tw_ok t ht).2.2, (tw_ok t ht).1, show Nat.xor _ _ = _ ^^^ _ from rfl, Nat.testBit_xor,
    selB_bit, decide_eq_true hj, Bool.and_true]

theorem gU_lt {t : ℕ} (ht : t < 2048) : gU t < 2 ^ 24 := by
  unfold gU
  rw [(tw_ok t ht).1]
  exact (tw_ok t ht).2.1

theorem gL_lt {t : ℕ} (ht : t < 2048) : gL t < 2 ^ 24 := by
  unfold gL
  rw [(tw_ok t ht).2.2]
  exact selB_lt _

theorem gH_lt {t : ℕ} (ht : t < 2048) : gH t < 2 ^ 24 := by
  unfold gH
  rw [(tw_ok t ht).2.2, (tw_ok t ht).1]
  exact Nat.xor_lt_two_pow (tw_ok t ht).2.1 (selB_lt _)

theorem rowF_lt {g : ℕ → ℕ} (hg : ∀ t < 2048, g t < 2 ^ 24) : rowF g 2048 < 2 ^ SX :=
  lt_of_bits fun p hp => by
    rw [testBit_rowF hg] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    change p < 131072
    omega

theorem rowF_hi {g : ℕ → ℕ} (hg : ∀ t < 2048, g t < 2 ^ 24) {p : ℕ} (hp : 65536 ≤ p) :
    (rowF g 2048).testBit p = false := by
  rw [testBit_rowF hg]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left; left; omega

theorem rowF_lo {g : ℕ → ℕ} (hg : ∀ t < 2048, g t < 2 ^ 24) {t j : ℕ} (ht : t < 2048)
    (hj : j < 24) : (rowF g 2048).testBit (32 * t + j) = (g t).testBit j := by
  rw [testBit_rowF hg, decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and,
    Bool.true_and]
  congr 2 <;> omega

theorem gL_lt' : ∀ t < 2048, gL t < 2 ^ 24 := fun _ ht => gL_lt ht

theorem gU_lt' : ∀ t < 2048, gU t < 2 ^ 24 := fun _ ht => gU_lt ht

theorem gH_lt' : ∀ t < 2048, gH t < 2 ^ 24 := fun _ ht => gH_lt ht

theorem sgL_lt : rowF gL 2048 < 2 ^ SX := rowF_lt (g := gL) gL_lt'

theorem sgU_lt : rowF gU 2048 < 2 ^ SX := rowF_lt (g := gU) gU_lt'

theorem sgH_lt : rowF gH 2048 < 2 ^ SX := rowF_lt (g := gH) gH_lt'

theorem bdL {np S x y : ℕ} (h : Bd np S x) : Bd np S (Nat.land x y) := bd_land h

theorem POCT_lt : POCT < 2 ^ 64 := by decide +kernel

open CFSG.KC.KDense.InitAux in
theorem doct_bit (y : ℕ) :
    (Nat.shiftLeft (Nat.mul POCT (Nat.div (ones (nat_lit 48576)) (ones (nat_lit 64))))
      (nat_lit 65536)).testBit y = (decide (65536 ≤ y ∧ y < 114112) && POCT.testBit (y % 64)) := by
  rw [Bool.eq_iff_iff, testBit_shl, Benes.nmul, Benes.ndiv, Benes.ones_eq, Benes.ones_eq,
    Benes.testBit_mul_div (n := 759) (by decide) (by decide) POCT_lt]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e : (y - 65536) % 64 = y % 64 := by omega
    rw [e] at h3
    exact ⟨⟨h1, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have e : (y - 65536) % 64 = y % 64 := by omega
    rw [e]
    exact ⟨h1, by omega, h3⟩

theorem doct_lt : Nat.shiftLeft (Nat.mul POCT (Nat.div (ones (nat_lit 48576)) (ones (nat_lit 64))))
    (nat_lit 65536) < 2 ^ SX := lt_of_bits fun p hp => by
  rw [doct_bit] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  change p < 131072
  omega

@[expose] def phi6 (q : ℕ) : ℕ := if xs q 6 then q ^^^ 63 else q

theorem phi6_lt {q : ℕ} (hq : q < 64) : phi6 q < 64 := by
  unfold phi6
  split_ifs
  · exact (xs_blk q hq).2
  · exact hq

theorem phi_blk {B q : ℕ} (hB1 : 1024 ≤ B) (hB2 : B < 1783) (hq : q < 64) :
    phi (64 * B + q) = 64 * B + phi6 q := by
  unfold phi phi6
  rw [testBit_mk6 (by change _ < 131072; omega), xs_eq_blk hq, decide_eq_true (by omega),
    Bool.true_and]
  split_ifs
  · exact xor63_blk hq
  · rfl

theorem phi_out {p : ℕ} (hp : p < SX) (h : ¬ (65536 ≤ p ∧ p < 114112)) : phi p = p := by
  unfold phi
  rw [testBit_mk6 hp, decide_eq_false h, Bool.false_and]
  rfl

theorem evenTab_get : ∀ q < 64, (Native.evenTab ())[q]! = 2 * q + (xs q 6).toNat := by
  decide +kernel

theorem oct_matrix : ∀ q < 64, ∀ c < 64,
    (if POCT.testBit q then -Kz 6 (phi6 q) c else Kz 6 (phi6 q) c) =
      octSign (2 * c + (xs c 6).toNat) (2 * q + (xs q 6).toNat) := by
  decide +kernel

@[expose] noncomputable def octZ (O : POps) (F : Fix) (X : ℕ) : ℕ :=
  O.half SX (nat_lit 3) (O.neg SX F.doct (O.net SX (nat_lit 17) F.pi6
    (wht6G O (Nat.land X (O.rep SX regOct)))))

theorem octZ_bd (hO : PLaw np O) {F : Fix} (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {X : ℕ}
    (hX : Bd np SX X) : Bd np SX (octZ O F X) := by
  obtain ⟨hk, -⟩ := Benes.andB_true h6
  have hd := (masks_spec hm).1
  unfold octZ
  rw [hd]
  exact hO.half_bd (by decide) (by decide) (hO.neg_bd doct_lt (hO.net_bd (k := 17) SX_eq hk
    (Hn_bd hO 6 le_rfl _ (bdL hX))))

theorem octZ_zero (hO : PLaw np O) {F : Fix} (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {X : ℕ}
    (hX : Bd np SX X) {p : ℕ} (hp : p < SX) (hr : ¬ (65536 ≤ p ∧ p < 114112)) :
    Zero np SX (octZ O F X) p := by
  obtain ⟨hk, -⟩ := Benes.andB_true h6
  have hd := (masks_spec hm).1
  have hro : regOct.testBit p = false := by
    rw [← Bool.not_eq_true, CFSG.KC.KDense.InitAux.testBit_regOct]
    exact hr
  have hy := Hn_bd hO 6 le_rfl _ (bd_land (y := O.rep SX regOct) hX)
  unfold octZ
  rw [hd]
  refine hO.half_zero (by decide) (by decide) (hO.neg_bd doct_lt (hO.net_bd (k := 17) SX_eq hk hy))
    hp (hO.neg_zero doct_lt (hO.net_bd (k := 17) SX_eq hk hy) hp ?_ (hO.net_zero (k := 17) SX_eq hk
      hy hp ?_))
  · rw [doct_bit, decide_eq_false hr, Bool.false_and]
  · rw [pi6_perm h6 hp, phi_out hp hr]
    exact Hn_zero hO hp hro 6 le_rfl _ (bdL hX) (zero_land_rep hO regOct_lt hp hro)

theorem octZ_res (hO : PLaw np O) {F : Fix} (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {X : ℕ}
    (hX : Bd np SX X) {B q : ℕ} (hB1 : 1024 ≤ B) (hB2 : B < 1783) (hq : q < 64) :
    resPN np SX (octZ O F X) (64 * B + q) = hN np ^ 3 * ∑ c ∈ Finset.range 64,
      ((octSign (2 * c + (xs c 6).toNat) (2 * q + (xs q 6).toNat) : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX X (64 * B + c) := by
  obtain ⟨hk, -⟩ := Benes.andB_true h6
  have hd := (masks_spec hm).1
  have hpS : 64 * B + q < SX := by change _ < 131072; omega
  have hy : Bd np SX (Hn O 6 (Nat.land X (O.rep SX regOct))) :=
    Hn_bd hO 6 le_rfl _ (bd_land (y := O.rep SX regOct) hX)
  unfold octZ
  rw [hd, wht6G_eq, hO.half_res (by decide) (by decide)
    (hO.neg_bd doct_lt (hO.net_bd (k := 17) SX_eq hk hy)) hpS,
    hO.neg_res doct_lt (hO.net_bd (k := 17) SX_eq hk hy) hpS,
    hO.net_res (k := 17) SX_eq hk hy hpS, pi6_perm h6 hpS, phi_blk hB1 hB2 hq,
    Hn_res hO 6 le_rfl (Nat.land X (O.rep SX regOct)) (bdL hX) B hB1 hB2 _ (phi6_lt hq),
    doct_bit,
    decide_eq_true (by omega), Bool.true_and, show (64 * B + q) % 64 = q by omega]
  congr 1
  have hc : ∀ c ∈ Finset.range 64, resPN np SX (Nat.land X (O.rep SX regOct)) (64 * B + c) =
      resPN np SX X (64 * B + c) := by
    intro c hc
    simp only [Finset.mem_range] at hc
    rw [res_land_rep' hO regOct_lt (by change _ < 131072; omega),
      (CFSG.KC.KDense.InitAux.testBit_regOct _).mpr ⟨by omega, by omega⟩]
    rfl
  have hs : ∀ c ∈ Finset.range 64,
      ((octSign (2 * c + (xs c 6).toNat) (2 * q + (xs q 6).toNat) : ℤ) : ZMod (2 ^ np - 1)) =
        ((if POCT.testBit q then -Kz 6 (phi6 q) c else Kz 6 (phi6 q) c : ℤ) : ZMod (2 ^ np - 1)) :=
    fun c hc => by rw [oct_matrix q hq c (Finset.mem_range.1 hc)]
  have hsum : ∑ c ∈ Finset.range 64,
      ((octSign (2 * c + (xs c 6).toNat) (2 * q + (xs q 6).toNat) : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX X (64 * B + c) = ∑ c ∈ Finset.range 64,
      ((if POCT.testBit q then -Kz 6 (phi6 q) c else Kz 6 (phi6 q) c : ℤ) : ZMod (2 ^ np - 1)) *
        resPN np SX (Nat.land X (O.rep SX regOct)) (64 * B + c) :=
    Finset.sum_congr rfl fun c hc' => by rw [hs c hc', hc c hc']
  rw [hsum]
  split_ifs
  · simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  · rfl

@[expose] noncomputable def tdk (k : ℕ) : ℕ :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add k (nat_lit 5))) (Nat.shiftLeft (nat_lit 1) k)

@[expose] noncomputable def tmk (k : ℕ) : ℕ := Nat.land (idPlane SA k) (clr SA (Nat.add k (nat_lit 5)))

@[expose] noncomputable def Tn (O : POps) (n x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun y => y)
    (fun k ih y => CFSG.KC.Loop.strictN (dsw (tdk k) (O.rep SA (tmk k)) y) ih) n x

theorem transpG_eq (O : POps) (x : ℕ) : transpG O x = Tn O 5 x := rfl

theorem Tn_succ (O : POps) (n x : ℕ) : Tn O (n + 1) x = Tn O n (dsw (tdk n) (O.rep SA (tmk n)) x) :=
  recS_succ (fun k y => dsw (tdk k) (O.rep SA (tmk k)) y) n x

theorem tvalid_dec : ∀ k < 5, tmk k &&& (tmk k <<< tdk k) = 0 ∧ tmk k >>> (SA - tdk k) = 0 := by
  decide +kernel

theorem tvalid {k : ℕ} (hk : k < 5) : Benes.ValidIn SA (tdk k) (tmk k) :=
  Benes.validIn_of_dsw (tvalid_dec k hk).1 (tvalid_dec k hk).2

@[expose] noncomputable def sig : ℕ → ℕ → ℕ
  | 0, r => r
  | n + 1, r => Benes.swp (tdk n) (tmk n) (sig n r)

theorem sig_lt : ∀ n ≤ 5, ∀ r < SA, sig n r < SA
  | 0, _, r, hr => hr
  | n + 1, hn, r, hr => Benes.swp_lt (tvalid (by omega)) (sig_lt n (by omega) r hr)

theorem sig5 : ∀ r < 1024, sig 5 r = 32 * (r % 32) + r / 32 := by decide +kernel

theorem Tn_bits (hO : PLaw np O) : ∀ n ≤ 5, ∀ x, ∀ u < np, ∀ r < SA,
    (Tn O n x).testBit (SA * u + r) = x.testBit (SA * u + sig n r)
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, hn, x, u, hu, r, hr => by
    rw [Tn_succ, Tn_bits hO n (by omega) _ u hu r hr,
      testBit_dsw_rep hO (tvalid (by omega)) (by decide) x hu (sig_lt n (by omega) r hr)]
    rfl

theorem Tn_bd (hO : PLaw np O) : ∀ n ≤ 5, ∀ x, Bd np SA x → Bd np SA (Tn O n x)
  | 0, _, _, hx => hx
  | n + 1, hn, x, hx => by
    rw [Tn_succ]
    exact Tn_bd hO n (by omega) _ (bd_dsw_rep hO (tvalid (by omega)) hx)

theorem res_perm {S x y p q : ℕ} (h : ∀ b < np, x.testBit (b * S + p) = y.testBit (b * S + q)) :
    resPN np S x p = resPN np S y q := by
  unfold resPN
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, h b (Finset.mem_range.1 hb)]

theorem transp_res (hO : PLaw np O) {x r : ℕ} (hr : r < 1024) :
    resPN np SA (transpG O x) r = resPN np SA x (32 * (r % 32) + r / 32) := by
  rw [transpG_eq, ← sig5 r hr]
  refine res_perm fun b hb => ?_
  rw [Nat.mul_comm b, Tn_bits hO 5 le_rfl x b hb r hr]

theorem transp_zero (hO : PLaw np O) {x r : ℕ} (hr : r < 1024)
    (hz : Zero np SA x (32 * (r % 32) + r / 32)) : Zero np SA (transpG O x) r := fun b hb => by
  rw [transpG_eq, Nat.mul_comm b, Tn_bits hO 5 le_rfl x b hb r hr, sig5 r hr, Nat.mul_comm]
  exact hz b hb

theorem zero_shl {S o x p : ℕ} (hpo : p < o) (ho : o ≤ S)
    (hs : ∀ b < np, ∀ q < S, S - o ≤ q → x.testBit (b * S + q) = false) :
    Zero np S (Nat.shiftLeft x o) p := fun b hb => by
  change (x <<< o).testBit _ = false
  rw [Nat.testBit_shiftLeft]
  rcases b with _ | b
  · simp only [Nat.zero_mul, Nat.zero_add]
    rw [decide_eq_false (by omega), Bool.false_and]
  · have e : (b + 1) * S + p - o = b * S + (S - o + p) := by rw [Nat.succ_mul]; omega
    rw [e, hs b (by omega) _ (by omega) (by omega), Bool.and_false]

@[expose] noncomputable def dd2 (O : POps) (X : ℕ) : ℕ :=
  O.half SA (nat_lit 1) (O.add SA (O.compact (nat_lit 114688) X)
    (O.neg SA upA (O.compact (nat_lit 115712) X)))

@[expose] noncomputable def UU (O : POps) (X : ℕ) : ℕ :=
  Nat.land (O.half SA (nat_lit 1) (O.add SA (O.compact (nat_lit 114688) X)
    (O.compact (nat_lit 115712) X))) (O.rep SA upA)

@[expose] noncomputable def T1 (O : POps) (F : Fix) (W : ℕ) : ℕ :=
  O.neg SX F.sgWLo (Nat.land W (O.rep SX lo16))

@[expose] noncomputable def T3 (O : POps) (X A : ℕ) : ℕ :=
  O.expand 114688 (Nat.land (O.add SA A (dd2 O X)) (O.rep SA upA))

@[expose] noncomputable def T4 (O : POps) (X A : ℕ) : ℕ :=
  O.expand 115712 (Nat.land (O.add SA (O.neg SA upA A) (dd2 O X)) (O.rep SA upA))

@[expose] noncomputable def P1 (O : POps) (F : Fix) (W : ℕ) : ℕ :=
  O.neg SX F.sgWUp (Nat.land (Nat.shiftRight W (nat_lit 65536)) (O.rep SX lo16))

@[expose] noncomputable def P0 (O : POps) (F : Fix) (X : ℕ) : ℕ :=
  O.neg SX F.sgOddUp (Nat.land X (O.rep SX lo16))

theorem tauG_eq (O : POps) (F : Fix) (X A W : ℕ) : tauG O F X A W =
    (Nat.lor (T1 O F W) (Nat.lor (octZ O F X) (Nat.lor (T3 O X A) (T4 O X A))),
     Nat.lor (Nat.land A (O.rep SA diagA)) (Nat.lor (UU O X) (transpG O (UU O X))),
     Nat.lor (P1 O F W) (Nat.shiftLeft (P0 O F X) (nat_lit 65536))) := rfl

theorem SA_v : SA = 1024 := rfl

theorem SX_v : SX = 131072 := rfl

section Comp

variable (hO : PLaw np O) {X A W : ℕ} (hX : Bd np SX X) (hA : Bd np SA A) (hW : Bd np SX W)
include hO

theorem compact_res' {o q : ℕ} (ho : o + SA ≤ SX) (hq : q < SA) (hX : Bd np SX X) :
    resPN np SA (O.compact o X) q = resPN np SX X (o + q) := hO.compact_res ho hX hq

theorem dd2_bd : Bd np SA (dd2 O X) :=
  hO.half_bd (by decide) (by decide) (hO.add_bd hO.compact_bd (hO.neg_bd upA_lt hO.compact_bd))

include hX in
theorem dd2_res {q : ℕ} (hq : q < SA) : resPN np SA (dd2 O X) q = hN np * (resPN np SX X (114688 + q) +
    if upA.testBit q then -resPN np SX X (115712 + q) else resPN np SX X (115712 + q)) := by
  unfold dd2
  rw [hO.half_res (by decide) (by decide) (hO.add_bd hO.compact_bd (hO.neg_bd upA_lt hO.compact_bd)) hq,
    hO.add_res hO.compact_bd (hO.neg_bd upA_lt hO.compact_bd) hq, hO.neg_res upA_lt hO.compact_bd hq,
    compact_res' hO (by decide) hq hX, compact_res' hO (by decide) hq hX, pow_one]

theorem UU_bd : Bd np SA (UU O X) :=
  bd_land (hO.half_bd (by decide) (by decide) (hO.add_bd hO.compact_bd hO.compact_bd))

include hX in
theorem UU_res {q : ℕ} (hq : q < SA) : resPN np SA (UU O X) q = if upA.testBit q then
    hN np * (resPN np SX X (114688 + q) + resPN np SX X (115712 + q)) else 0 := by
  unfold UU
  rw [res_land_rep' hO upA_lt hq, hO.half_res (by decide) (by decide)
    (hO.add_bd hO.compact_bd hO.compact_bd) hq, hO.add_res hO.compact_bd hO.compact_bd hq,
    compact_res' hO (by decide) hq hX, compact_res' hO (by decide) hq hX, pow_one]

theorem UU_zero {q : ℕ} (hq : q < SA) (hu : upA.testBit q = false) : Zero np SA (UU O X) q :=
  zero_land_rep hO upA_lt hq hu

variable {F : Fix} (hm : tauMasksOK F = true)
include hm

theorem T1_bd (hW : Bd np SX W) : Bd np SX (T1 O F W) := by
  unfold T1
  rw [(masks_spec hm).2.2.1]
  exact hO.neg_bd sgL_lt (bdL hW)

theorem T1_res (hW : Bd np SX W) {p : ℕ} (hp : p < 65536) : resPN np SX (T1 O F W) p =
    if (rowF gL 2048).testBit p then -resPN np SX W p else resPN np SX W p := by
  unfold T1
  rw [(masks_spec hm).2.2.1, hO.neg_res sgL_lt (bdL hW)
    (by rw [SX_v]; omega), res_land_rep' hO lo16_lt (by rw [SX_v]; omega), lo16_bit,
    decide_eq_true hp, if_pos rfl]

theorem T1_zero (hW : Bd np SX W) {p : ℕ} (hp : p < SX) (hp' : 65536 ≤ p) :
    Zero np SX (T1 O F W) p := by
  unfold T1
  rw [(masks_spec hm).2.2.1]
  exact hO.neg_zero sgL_lt (bdL hW) hp
    (rowF_hi (g := gL) gL_lt' hp') (zero_land_rep hO lo16_lt hp (by
      rw [lo16_bit, decide_eq_false (by omega)]))

theorem P0_bd (hX : Bd np SX X) : Bd np SX (P0 O F X) := by
  unfold P0
  rw [(masks_spec hm).2.1]
  exact hO.neg_bd sgU_lt (bdL hX)

theorem P0_res (hX : Bd np SX X) {p : ℕ} (hp : p < 65536) : resPN np SX (P0 O F X) p =
    if (rowF gU 2048).testBit p then -resPN np SX X p else resPN np SX X p := by
  unfold P0
  rw [(masks_spec hm).2.1, hO.neg_res sgU_lt (bdL hX)
    (by rw [SX_v]; omega), res_land_rep' hO lo16_lt (by rw [SX_v]; omega), lo16_bit,
    decide_eq_true hp, if_pos rfl]

theorem P0_zero (hX : Bd np SX X) {p : ℕ} (hp : p < SX) (hp' : 65536 ≤ p) :
    Zero np SX (P0 O F X) p := by
  unfold P0
  rw [(masks_spec hm).2.1]
  exact hO.neg_zero sgU_lt (bdL hX) hp
    (rowF_hi (g := gU) gU_lt' hp') (zero_land_rep hO lo16_lt hp (by
      rw [lo16_bit, decide_eq_false (by omega)]))

theorem shr_bd (hW : Bd np SX W) : Bd np SX (Nat.shiftRight W (nat_lit 65536)) :=
  lt_of_le_of_lt (Nat.shiftRight_le W 65536) hW

theorem P1_bd (hW : Bd np SX W) : Bd np SX (P1 O F W) := by
  unfold P1
  rw [(masks_spec hm).2.2.2]
  exact hO.neg_bd sgH_lt (bdL (shr_bd hO hm hW))

theorem P1_res (hW : Bd np SX W) {p : ℕ} (hp : p < 65536) : resPN np SX (P1 O F W) p =
    if (rowF gH 2048).testBit p then -resPN np SX W (p + 65536) else resPN np SX W (p + 65536) := by
  unfold P1
  rw [(masks_spec hm).2.2.2, hO.neg_res sgH_lt
    (bdL (shr_bd hO hm hW)) (by rw [SX_v]; omega)]
  have e := res_shr_land hO (o := 65536) (m := lo16) (x := W) (S := SX) (by rw [SX_v]; omega)
    lo16_lt' hW (p := p) (by rw [SX_v]; omega)
  rw [lo16_bit, decide_eq_true hp, if_pos rfl] at e
  change resPN np SX ((W >>> 65536) &&& O.rep SX lo16) p = _ at e
  rw [show Nat.land (Nat.shiftRight W (nat_lit 65536)) (O.rep SX lo16) =
    (W >>> 65536) &&& O.rep SX lo16 from rfl, e]

theorem P1_zero (hW : Bd np SX W) {p : ℕ} (hp : p < SX) (hp' : 65536 ≤ p) :
    Zero np SX (P1 O F W) p := by
  unfold P1
  rw [(masks_spec hm).2.2.2]
  exact hO.neg_zero sgH_lt (bdL (shr_bd hO hm hW)) hp
    (rowF_hi (g := gH) gH_lt' hp') (zero_land_rep hO lo16_lt hp (by
      rw [lo16_bit, decide_eq_false (by omega)]))

theorem P0_hs (hX : Bd np SX X) : ∀ b < np, ∀ q < SX, SX - 65536 ≤ q →
    (P0 O F X).testBit (b * SX + q) = false := fun b hb q hq hq' =>
  P0_zero hO hm hX hq (by rw [SX_v] at hq'; omega) b hb

theorem P2_bd (hX : Bd np SX X) : Bd np SX (Nat.shiftLeft (P0 O F X) (nat_lit 65536)) :=
  bd_shl (P0_bd hO hm hX) (P0_hs hO hm hX)

theorem P2_res (hX : Bd np SX X) {p : ℕ} (hp : p < SX) :
    resPN np SX (Nat.shiftLeft (P0 O F X) (nat_lit 65536)) p =
      if 65536 ≤ p then resPN np SX (P0 O F X) (p - 65536) else 0 :=
  res_shl (P0_bd hO hm hX) (P0_hs hO hm hX) hp

theorem P2_zero (hX : Bd np SX X) {p : ℕ} (hp : p < 65536) :
    Zero np SX (Nat.shiftLeft (P0 O F X) (nat_lit 65536)) p :=
  zero_shl (S := SX) (o := 65536) hp (by rw [SX_v]; omega) (P0_hs hO hm hX)

end Comp

section Comp2

variable (hO : PLaw np O) {X A W : ℕ} (hX : Bd np SX X) (hA : Bd np SA A) (hW : Bd np SX W)
include hO hX hA

theorem I3_bd : Bd np SA (Nat.land (O.add SA A (dd2 O X)) (O.rep SA upA)) :=
  bdL (hO.add_bd hA (dd2_bd hO))

theorem I4_bd : Bd np SA (Nat.land (O.add SA (O.neg SA upA A) (dd2 O X)) (O.rep SA upA)) :=
  bdL (hO.add_bd (hO.neg_bd upA_lt hA) (dd2_bd hO))

theorem T3_bd : Bd np SX (T3 O X A) := hO.expand_bd (by decide) (I3_bd hO hX hA)

theorem T4_bd : Bd np SX (T4 O X A) := hO.expand_bd (by decide) (I4_bd hO hX hA)

theorem T3_res {p : ℕ} (h1 : 114688 ≤ p) (h2 : p < 115712) (hu : upA.testBit (p - 114688) = true) :
    resPN np SX (T3 O X A) p = resPN np SA A (p - 114688) + resPN np SA (dd2 O X) (p - 114688) := by
  unfold T3
  rw [hO.expand_res (by decide) (I3_bd hO hX hA) (by rw [SX_v]; omega), if_pos (by rw [SA_v]; omega),
    res_land_rep' hO upA_lt (by rw [SA_v]; omega), hu, if_pos rfl,
    hO.add_res hA (dd2_bd hO) (by rw [SA_v]; omega)]

theorem T4_res {p : ℕ} (h1 : 115712 ≤ p) (h2 : p < 116736) (hu : upA.testBit (p - 115712) = true) :
    resPN np SX (T4 O X A) p = -resPN np SA A (p - 115712) + resPN np SA (dd2 O X) (p - 115712) := by
  unfold T4
  rw [hO.expand_res (by decide) (I4_bd hO hX hA) (by rw [SX_v]; omega), if_pos (by rw [SA_v]; omega),
    res_land_rep' hO upA_lt (by rw [SA_v]; omega), hu, if_pos rfl,
    hO.add_res (hO.neg_bd upA_lt hA) (dd2_bd hO) (by rw [SA_v]; omega),
    hO.neg_res upA_lt hA (by rw [SA_v]; omega), hu, if_pos rfl]

theorem T3_zero {p : ℕ} (hp : p < SX)
    (h : ¬ (114688 ≤ p ∧ p < 115712 ∧ upA.testBit (p - 114688) = true)) :
    Zero np SX (T3 O X A) p := by
  unfold T3
  refine hO.expand_zero (by decide) (I3_bd hO hX hA) hp fun hw => ?_
  rw [SA_v] at hw
  exact zero_land_rep hO upA_lt (by rw [SA_v]; omega) (by
    cases e : upA.testBit (p - 114688)
    · rfl
    · exact absurd ⟨hw.1, by omega, e⟩ h)

theorem T4_zero {p : ℕ} (hp : p < SX)
    (h : ¬ (115712 ≤ p ∧ p < 116736 ∧ upA.testBit (p - 115712) = true)) :
    Zero np SX (T4 O X A) p := by
  unfold T4
  refine hO.expand_zero (by decide) (I4_bd hO hX hA) hp fun hw => ?_
  rw [SA_v] at hw
  exact zero_land_rep hO upA_lt (by rw [SA_v]; omega) (by
    cases e : upA.testBit (p - 115712)
    · rfl
    · exact absurd ⟨hw.1, by omega, e⟩ h)

end Comp2

section New

variable (hO : PLaw np O) {F : Fix} (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {X A W : ℕ}
  (hX : Bd np SX X) (hA : Bd np SA A) (hW : Bd np SX W)
include hO h6 hm hX hA hW

local notation "XN" => Nat.lor (T1 O F W) (Nat.lor (octZ O F X) (Nat.lor (T3 O X A) (T4 O X A)))

theorem XN_bd : Bd np SX XN :=
  bd_lor (T1_bd hO hm hW) (bd_lor (octZ_bd hO h6 hm hX) (bd_lor (T3_bd hO hX hA) (T4_bd hO hX hA)))

theorem XN_lo {p : ℕ} (hp : p < 65536) : resPN np SX XN p = resPN np SX (T1 O F W) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  exact res_lor_l hpS (zero_lor (octZ_zero hO h6 hm hX hpS (by omega))
    (zero_lor (T3_zero hO hX hA hpS (by omega)) (T4_zero hO hX hA hpS (by omega))))

theorem XN_oct {p : ℕ} (h1 : 65536 ≤ p) (h2 : p < 114112) :
    resPN np SX XN p = resPN np SX (octZ O F X) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  rw [res_lor_r hpS (T1_zero hO hm hW hpS h1)]
  exact res_lor_l hpS (zero_lor (T3_zero hO hX hA hpS (by omega)) (T4_zero hO hX hA hpS (by omega)))

theorem XN_3 {p : ℕ} (h1 : 114688 ≤ p) (h2 : p < 115712) :
    resPN np SX XN p = resPN np SX (T3 O X A) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  rw [res_lor_r hpS (T1_zero hO hm hW hpS (by omega)),
    res_lor_r hpS (octZ_zero hO h6 hm hX hpS (by omega))]
  exact res_lor_l hpS (T4_zero hO hX hA hpS (by omega))

theorem XN_4 {p : ℕ} (h1 : 115712 ≤ p) (h2 : p < 116736) :
    resPN np SX XN p = resPN np SX (T4 O X A) p := by
  have hpS : p < SX := by rw [SX_v]; omega
  rw [res_lor_r hpS (T1_zero hO hm hW hpS (by omega)),
    res_lor_r hpS (octZ_zero hO h6 hm hX hpS (by omega))]
  exact res_lor_r hpS (T3_zero hO hX hA hpS (by omega))

theorem XN_zero {p : ℕ} (hp : p < SX) (h0 : 65536 ≤ p) (h1 : ¬ (65536 ≤ p ∧ p < 114112))
    (h3 : ¬ (114688 ≤ p ∧ p < 115712 ∧ upA.testBit (p - 114688) = true))
    (h4 : ¬ (115712 ≤ p ∧ p < 116736 ∧ upA.testBit (p - 115712) = true)) :
    resPN np SX XN p = 0 :=
  res_of_zero (zero_lor (T1_zero hO hm hW hp h0) (zero_lor (octZ_zero hO h6 hm hX hp h1)
    (zero_lor (T3_zero hO hX hA hp h3) (T4_zero hO hX hA hp h4))))

local notation "WN" => Nat.lor (P1 O F W) (Nat.shiftLeft (P0 O F X) (nat_lit 65536))

theorem WN_bd : Bd np SX WN := bd_lor (P1_bd hO hm hW) (P2_bd hO hm hX)

theorem WN_lo {p : ℕ} (hp : p < 65536) : resPN np SX WN p = resPN np SX (P1 O F W) p :=
  res_lor_l (by rw [SX_v]; omega) (P2_zero hO hm hX hp)

theorem WN_hi {p : ℕ} (hp : p < SX) (h : 65536 ≤ p) :
    resPN np SX WN p = resPN np SX (P0 O F X) (p - 65536) := by
  rw [res_lor_r hp (P1_zero hO hm hW hp h), P2_res hO hm hX hp, if_pos h]

end New

@[expose] noncomputable def AN (O : POps) (X A : ℕ) : ℕ :=
  Nat.lor (Nat.land A (O.rep SA diagA)) (Nat.lor (UU O X) (transpG O (UU O X)))

section NewA

variable (hO : PLaw np O) {X A : ℕ} (hX : Bd np SX X) (hA : Bd np SA A)
include hO hX hA

theorem AN_bd : Bd np SA (AN O X A) :=
  bd_lor (bdL hA) (bd_lor (UU_bd hO) (by rw [transpG_eq]; exact Tn_bd hO 5 le_rfl _ (UU_bd hO)))

theorem AN_diag {i : ℕ} (hi : i < 24) : resPN np SA (AN O X A) (32 * i + i) = resPN np SA A (32 * i + i) := by
  have hq : 32 * i + i < SA := by rw [SA_v]; omega
  have hu : upA.testBit (32 * i + i) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ (by omega)]
    simp only [decide_eq_false_iff_not]
    omega
  have e1 : (32 * i + i) / 32 = i := by omega
  have e2 : (32 * i + i) % 32 = i := by omega
  have hd : diagA.testBit (32 * i + i) = true := by
    rw [diagA_bits (32 * i + i) (by omega), e1, e2]
    simp only [decide_eq_true_eq]
    exact ⟨trivial, hi⟩
  unfold AN
  rw [res_lor_l hq (zero_lor (UU_zero hO hq hu) (transp_zero hO (by omega) (by
    rw [e1, e2]
    exact UU_zero hO hq hu))), res_land_rep' hO diagA_lt hq, hd, if_pos rfl]

theorem AN_up {i j : ℕ} (hij : i < j) (hj : j < 24) :
    resPN np SA (AN O X A) (32 * i + j) = resPN np SA (UU O X) (32 * i + j) := by
  have hq : 32 * i + j < SA := by rw [SA_v]; omega
  have hq' : 32 * j + i < SA := by rw [SA_v]; omega
  have e1 : (32 * i + j) / 32 = i := by omega
  have e2 : (32 * i + j) % 32 = j := by omega
  have e3 : (32 * j + i) / 32 = j := by omega
  have e4 : (32 * j + i) % 32 = i := by omega
  have hu : upA.testBit (32 * j + i) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ (by omega), e3, e4]
    simp only [decide_eq_false_iff_not]
    omega
  have hd : diagA.testBit (32 * i + j) = false := by
    rw [diagA_bits (32 * i + j) (by omega), e1, e2]
    simp only [decide_eq_false_iff_not]
    omega
  unfold AN
  rw [res_lor_r hq (zero_land_rep hO diagA_lt hq hd),
    res_lor_l hq (transp_zero hO (by omega) (by rw [e1, e2]; exact UU_zero hO hq' hu))]

theorem AN_low {i j : ℕ} (hij : j < i) (hi : i < 24) :
    resPN np SA (AN O X A) (32 * i + j) = resPN np SA (UU O X) (32 * j + i) := by
  have hq : 32 * i + j < SA := by rw [SA_v]; omega
  have e1 : (32 * i + j) / 32 = i := by omega
  have e2 : (32 * i + j) % 32 = j := by omega
  have hu : upA.testBit (32 * i + j) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ (by omega), e1, e2]
    simp only [decide_eq_false_iff_not]
    omega
  have hd : diagA.testBit (32 * i + j) = false := by
    rw [diagA_bits (32 * i + j) (by omega), e1, e2]
    simp only [decide_eq_false_iff_not]
    omega
  unfold AN
  rw [res_lor_r hq (zero_land_rep hO diagA_lt hq hd),
    res_lor_r hq (UU_zero hO hq hu), transp_res hO (by omega), e1, e2]

theorem AN_zero {p : ℕ} (hp : p < SA) (h : 24 ≤ p % 32 ∨ 24 ≤ p / 32) :
    resPN np SA (AN O X A) p = 0 := by
  have hpS := hp
  rw [SA_v] at hp
  have d1 : diagA.testBit p = false := by
    rw [diagA_bits _ hp]
    simp only [decide_eq_false_iff_not]
    omega
  have u1 : upA.testBit p = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ hp]
    simp only [decide_eq_false_iff_not]
    omega
  have e3 : (32 * (p % 32) + p / 32) / 32 = p % 32 := by omega
  have e4 : (32 * (p % 32) + p / 32) % 32 = p / 32 := by omega
  have hp'' : 32 * (p % 32) + p / 32 < 1024 := by omega
  have hp' : 32 * (p % 32) + p / 32 < SA := hp''
  have u2 : upA.testBit (32 * (p % 32) + p / 32) = false := by
    rw [CFSG.KC.KDense.InitAux.upA_bits _ hp'', e3, e4]
    simp only [decide_eq_false_iff_not]
    omega
  unfold AN
  exact res_of_zero (zero_lor (zero_land_rep hO diagA_lt hpS d1)
    (zero_lor (UU_zero hO hpS u1) (transp_zero hO hp (UU_zero hO hp' u2))))

end NewA

open CFSG.KC.KDense.InitAux

theorem xposK_even {tp : ℕ} (htp : tp < 276) :
    xposK (2 * tp) = 114688 + 32 * (Native.pairTab ())[tp]!.1 + (Native.pairTab ())[tp]!.2 := by
  unfold xposK
  rw [if_pos (by omega), if_pos (by omega), show 2 * tp / 2 = tp by omega]

theorem xposK_odd' {tp : ℕ} (htp : tp < 276) :
    xposK (2 * tp + 1) = 115712 + 32 * (Native.pairTab ())[tp]!.1 + (Native.pairTab ())[tp]!.2 := by
  unfold xposK
  rw [if_pos (by omega), if_neg (by omega), show (2 * tp + 1) / 2 = tp by omega]

theorem xposK_oddc {t i : ℕ} (ht : t < 2048) (hi : i < 24) : xposK (552 + 24 * t + i) = 32 * t + i := by
  unfold xposK
  rw [if_neg (by omega), if_pos (by omega), show (552 + 24 * t + i - 552) / 24 = t by omega,
    show (552 + 24 * t + i - 552) % 24 = i by omega]

theorem xposK_oct {o n : ℕ} (ho : o < 759) (hn : n < 64) :
    xposK (49704 + 64 * o + n) = 64 * (1024 + o) + n := by
  unfold xposK
  rw [if_neg (by omega), if_neg (by omega)]
  omega

theorem aIdx_pair {i j : ℕ} (h : i < j) : Native.aIdx i j = 24 + Native.pairIdx i j := by
  unfold Native.aIdx
  rw [if_neg (by omega), min_eq_left h.le, max_eq_right h.le]

theorem not_xpos {p : ℕ} (h : validX.testBit p = false) : ∀ q < 98280, xposK q ≠ p :=
  fun q hq e => by
    have := xposK_mem hq
    rw [e, h] at this
    exact Bool.false_ne_true this

theorem sgn_cast {M : ℕ} (b : Bool) : ((sgnI b : ℤ) : ZMod M) = if b then -1 else 1 := by
  cases b <;> simp [sgnI]

theorem h2_of {np : ℕ} (hnp : 1 ≤ np) : (2 : ZMod (2 ^ np - 1)) * hN np = 1 := by
  unfold hN
  rw [← pow_succ', Nat.sub_add_cancel hnp]
  have h1 := Nat.one_le_two_pow (n := np)
  have : ((2 ^ np : ℕ) : ZMod (2 ^ np - 1)) = 1 := by
    rw [show 2 ^ np = (2 ^ np - 1) + 1 by omega, Nat.cast_add, ZMod.natCast_self, zero_add,
      Nat.cast_one]
  exact_mod_cast this

end TauAux

theorem tau_sound {np : ℕ} {O : POps} (hO : PLaw np O) (hnp : 2 ≤ np) {F : Fix}
    (h6 : pi6OK F = true) (hm : tauMasksOK F = true) {v : Native.DVec} {t : St}
    (ht : RepN np v t) (f : Bool) :
    RepN np (Native.applyGen (Native.mkCtx ()) .tau v) (f, tauG O F t.2.1 t.2.2.1 t.2.2.2) := by
  open TauAux CFSG.KC.KDense.InitAux in
  obtain ⟨f0, X, A, W⟩ := t
  obtain ⟨hX1, hX2, hXb, hA1, hA2, hAb, hW1, hW2, hWb⟩ := ht
  dsimp only at hX1 hX2 hXb hA1 hA2 hAb hW1 hW2 hWb
  change Bd np SX X at hXb
  change Bd np SA A at hAb
  change Bd np SX W at hWb
  have h2 := h2_of (np := np) (by omega)
  have c8 : hN np ^ 3 * 8 = 1 := by linear_combination (4 * hN np ^ 2 + 2 * hN np + 1) * h2
  have c4 : hN np ^ 3 * 4 = hN np := by linear_combination (2 * hN np ^ 2 + hN np) * h2
  have hnat : ∀ k < 196884, resN np (Native.applyGen (Native.mkCtx ()) .tau v) k =
      hN np ^ 3 * tsum (resN np v) k := fun k hk => applyTau_res h2 _ v hk
  have e : tauG O F X A W =
      (Nat.lor (T1 O F W) (Nat.lor (octZ O F X) (Nat.lor (T3 O X A) (T4 O X A))), AN O X A,
       Nat.lor (P1 O F W) (Nat.shiftLeft (P0 O F X) (nat_lit 65536))) := rfl
  dsimp only
  rw [e]
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, XN_bd hO h6 hm hXb hAb hWb, fun i hi j hj => ?_,
    fun p hp hq => AN_zero hO hXb hAb hp hq, AN_bd hO hXb hAb, fun r hr j hj => ?_, fun p hp hq => ?_,
    WN_bd hO h6 hm hXb hAb hWb⟩
  ·
    rw [hnat _ (by omega)]
    rcases Nat.lt_or_ge q 552 with h1 | h1
    · obtain ⟨tp, htp, rfl | rfl⟩ : ∃ tp, tp < 276 ∧ (q = 2 * tp ∨ q = 2 * tp + 1) :=
        ⟨q / 2, by omega, by omega⟩
      all_goals
        obtain ⟨o1, o2⟩ := pairTab_ok tp htp
        have hpi := pairTab_idx2 tp htp
        have ex := xposK_even htp
        have ex1 := xposK_odd' htp
        generalize (Native.pairTab ())[tp]! = ij at o1 o2 hpi ex ex1
        obtain ⟨i, j⟩ := ij
        dsimp only at o1 o2 hpi ex ex1
        have e1 : (32 * i + j) / 32 = i := by omega
        have e2 : (32 * i + j) % 32 = j := by omega
        have hua : upA.testBit (32 * i + j) = true := by
          rw [upA_bits _ (by omega), e1, e2]
          simp only [decide_eq_true_eq]
          omega
        have hxa : resPN np SX X (114688 + (32 * i + j)) = resN np v (300 + 2 * tp) := by
          rw [← Nat.add_assoc, ← ex]
          exact hX1 _ (by omega)
        have hxb : resPN np SX X (115712 + (32 * i + j)) = resN np v (300 + 2 * tp + 1) := by
          rw [← Nat.add_assoc, ← ex1, hX1 _ (by omega)]
          rfl
        have haa : resPN np SA A (32 * i + j) = resN np v (24 + tp) := by
          rw [hA1 i (by omega) j o2, aIdx_pair o1, hpi]
        have hd := dd2_res hO hXb (q := 32 * i + j) (by rw [SA_v]; omega)
        rw [hua, if_pos rfl, hxa, hxb] at hd
        have s3 : 114688 + 32 * i + j - 114688 = 32 * i + j := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]
        have s4 : 115712 + 32 * i + j - 115712 = 32 * i + j := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]
        have hua3 : upA.testBit (114688 + 32 * i + j - 114688) = true := by rw [s3]; exact hua
        have hua4 : upA.testBit (115712 + 32 * i + j - 115712) = true := by rw [s4]; exact hua
      · rw [ex, XN_3 hO h6 hm hXb hAb hWb (by omega) (by omega),
          T3_res hO hXb hAb (by omega) (by omega) hua3, s3, haa, hd, tsum_pairX _ htp]
        linear_combination (-(resN np v (24 + tp))) * c8 -
          (resN np v (300 + 2 * tp) - resN np v (300 + 2 * tp + 1)) * c4
      · rw [ex1, XN_4 hO h6 hm hXb hAb hWb (by omega) (by omega),
          T4_res hO hXb hAb (by omega) (by omega) hua4, s4,
          haa, hd, show 300 + (2 * tp + 1) = 300 + 2 * tp + 1 by omega, tsum_pairX1 _ htp]
        linear_combination (resN np v (24 + tp)) * c8 -
          (resN np v (300 + 2 * tp) - resN np v (300 + 2 * tp + 1)) * c4
    rcases Nat.lt_or_ge q 49704 with h2' | h2'
    · obtain ⟨t, i, ht, hi, rfl⟩ : ∃ t i, t < 2048 ∧ i < 24 ∧ q = 552 + 24 * t + i :=
        ⟨(q - 552) / 24, (q - 552) % 24, by omega, by omega, by omega⟩
      rw [xposK_oddc ht hi, XN_lo hO h6 hm hXb hAb hWb (by omega), T1_res hO hm hWb (by omega),
        rowF_lo (g := gL) gL_lt' ht hi, gL_bit ht hi, hW1 t (by omega) i hi,
        show 300 + (552 + 24 * t + i) = 852 + 24 * t + i by omega, tsum_odd _ ht hi, tb_pb ht]
      push_cast [sgn_cast]
      cases pN (2 * t)
      · simp only [Bool.false_eq_true, if_false]
        linear_combination (-(resN np v (98580 + 24 * t + i))) * c8
      · simp only [if_true]
        linear_combination (resN np v (98580 + 24 * t + i)) * c8
    · obtain ⟨o, n, ho, hn, rfl⟩ : ∃ o n, o < 759 ∧ n < 64 ∧ q = 49704 + 64 * o + n :=
        ⟨(q - 49704) / 64, (q - 49704) % 64, by omega, by omega, by omega⟩
      rw [xposK_oct ho hn, XN_oct hO h6 hm hXb hAb hWb (by omega) (by omega),
        octZ_res hO h6 hm hXb (by omega) (by omega) hn,
        show 300 + (49704 + 64 * o + n) = 50004 + 64 * o + n by omega, tsum_oct _ ho hn]
      refine congrArg (hN np ^ 3 * ·) ?_
      refine Finset.sum_congr rfl fun c hc => ?_
      simp only [Finset.mem_range] at hc
      have hx := hX1 (49704 + 64 * o + c) (by omega)
      rw [xposK_oct ho hc, show 300 + (49704 + 64 * o + c) = 50004 + 64 * o + c by omega] at hx
      rw [hx, tb_S (by omega), show (c * 64 + n) / 64 = c by omega, show (c * 64 + n) % 64 = n by omega,
        evenTab_get c hc, evenTab_get n hn]
  ·
    have hv : validX.testBit p = false := by
      cases h : validX.testBit p
      · rfl
      · obtain ⟨q, hq', e⟩ := xposK_of_mem h
        exact absurd e (hq q hq')
    have hvx := testBit_validX p
    rw [hv] at hvx
    simp only [Bool.false_eq_true, false_iff] at hvx
    rcases Nat.lt_or_ge p 65536 with h1 | h1
    · rw [XN_lo hO h6 hm hXb hAb hWb h1, T1_res hO hm hWb h1, hW2 p hp (by omega)]
      split_ifs <;> simp
    · refine XN_zero hO h6 hm hXb hAb hWb hp h1 (fun h => hvx (Or.inr (Or.inl h))) ?_ ?_
      · rintro ⟨a, b, c⟩
        rw [upA_bits _ (by omega)] at c
        simp only [decide_eq_true_eq] at c
        exact hvx (Or.inr (Or.inr (Or.inl ⟨a, by omega, c.1, c.2⟩)))
      · rintro ⟨a, b, c⟩
        rw [upA_bits _ (by omega)] at c
        simp only [decide_eq_true_eq] at c
        exact hvx (Or.inr (Or.inr (Or.inr ⟨a, by omega, c.1, c.2⟩)))
  ·
    rw [hnat _ (by have := aIdx_lt i hi j hj; omega)]
    rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨htp, hpt⟩ := pairTab_idx i hi j hj hij
      have ex := xposK_even htp
      have ex1 := xposK_odd' htp
      rw [hpt] at ex ex1
      dsimp only at ex ex1
      have e1 : (32 * i + j) / 32 = i := by omega
      have e2 : (32 * i + j) % 32 = j := by omega
      have hua : upA.testBit (32 * i + j) = true := by
        rw [upA_bits _ (by omega), e1, e2]
        simp only [decide_eq_true_eq]
        omega
      rw [AN_up hO hXb hAb hij hj, UU_res hO hXb (by rw [SA_v]; omega), hua, if_pos rfl,
        ← Nat.add_assoc, ← Nat.add_assoc, ← ex, ← ex1, hX1 _ (by omega), hX1 _ (by omega),
        aIdx_pair hij, tsum_pairA _ htp, show 300 + (2 * Native.pairIdx i j + 1) =
          300 + 2 * Native.pairIdx i j + 1 by omega]
      linear_combination (-(resN np v (300 + 2 * Native.pairIdx i j) +
        resN np v (300 + 2 * Native.pairIdx i j + 1))) * c4
    · rw [AN_diag hO hXb hAb hi, hA1 i hi i hi, show Native.aIdx i i = i by simp [Native.aIdx],
        tsum_diag _ hi]
      linear_combination (-(resN np v i)) * c8
    · obtain ⟨htp, hpt⟩ := pairTab_idx j hj i hi hij
      have ex := xposK_even htp
      have ex1 := xposK_odd' htp
      rw [hpt] at ex ex1
      dsimp only at ex ex1
      have e1 : (32 * j + i) / 32 = j := by omega
      have e2 : (32 * j + i) % 32 = i := by omega
      have hua : upA.testBit (32 * j + i) = true := by
        rw [upA_bits _ (by omega), e1, e2]
        simp only [decide_eq_true_eq]
        omega
      rw [AN_low hO hXb hAb hij hi, UU_res hO hXb (by rw [SA_v]; omega), hua, if_pos rfl,
        ← Nat.add_assoc, ← Nat.add_assoc, ← ex, ← ex1, hX1 _ (by omega), hX1 _ (by omega),
        CFSG.KC.KDenseP.ListAux.aIdx_comm i hi j hj, aIdx_pair hij, tsum_pairA _ htp, show 300 + (2 * Native.pairIdx j i + 1) =
          300 + 2 * Native.pairIdx j i + 1 by omega]
      linear_combination (-(resN np v (300 + 2 * Native.pairIdx j i) +
        resN np v (300 + 2 * Native.pairIdx j i + 1))) * c4
  ·
    rw [hnat _ (by omega)]
    rcases Nat.lt_or_ge r 2048 with hr' | hr'
    · rw [WN_lo hO h6 hm hXb hAb hWb (by omega), P1_res hO hm hWb (by omega),
        rowF_lo (g := gH) gH_lt' hr' hj, gH_bit hr' hj,
        show 32 * r + j + 65536 = 32 * (2048 + r) + j by omega, hW1 (2048 + r) (by omega) j hj,
        tsum_Wlo _ hr' hj, tb_w hr', tb_pb hr']
      push_cast [sgn_cast]
      cases (wordN (2 * r)).testBit j <;> cases pN (2 * r)
      · simp only [Bool.false_eq_true, if_false, Bool.xor_false]
        linear_combination (-(resN np v (98580 + 24 * (2048 + r) + j))) * c8
      · simp only [Bool.false_eq_true, if_false, if_true, Bool.false_xor]
        linear_combination (resN np v (98580 + 24 * (2048 + r) + j)) * c8
      · simp only [Bool.false_eq_true, if_false, if_true, Bool.xor_false]
        linear_combination (resN np v (98580 + 24 * (2048 + r) + j)) * c8
      · simp only [if_true, Bool.xor_self, Bool.false_eq_true, if_false]
        linear_combination (-(resN np v (98580 + 24 * (2048 + r) + j))) * c8
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 2048 ∧ r = 2048 + t := ⟨r - 2048, by omega, by omega⟩
      have hx := hX1 (552 + 24 * t + j) (by omega)
      rw [xposK_oddc ht hj, show 300 + (552 + 24 * t + j) = 852 + 24 * t + j by omega] at hx
      rw [WN_hi hO h6 hm hXb hAb hWb (by rw [SX_v]; omega) (by omega),
        show 32 * (2048 + t) + j - 65536 = 32 * t + j by omega, P0_res hO hm hXb (by omega),
        rowF_lo (g := gU) gU_lt' ht hj, gU_bit ht j, hx, tsum_Whi _ ht hj, tb_w ht]
      push_cast [sgn_cast]
      cases (wordN (2 * t)).testBit j
      · simp only [Bool.false_eq_true, if_false]
        linear_combination (-(resN np v (852 + 24 * t + j))) * c8
      · simp only [if_true]
        linear_combination (resN np v (852 + 24 * t + j)) * c8
  ·
    rcases Nat.lt_or_ge p 65536 with h1 | h1
    · rw [WN_lo hO h6 hm hXb hAb hWb h1, P1_res hO hm hWb h1,
        hW2 (p + 65536) (by rw [SX_v]; omega) (by omega)]
      split_ifs <;> simp
    · have hv : validX.testBit (p - 65536) = false := by
        cases h : validX.testBit (p - 65536)
        · rfl
        · rw [testBit_validX] at h
          rw [SX_v] at hp
          omega
      rw [WN_hi hO h6 hm hXb hAb hWb hp h1, P0_res hO hm hXb (by rw [SX_v] at hp; omega),
        hX2 (p - 65536) (by rw [SX_v] at hp ⊢; omega) (not_xpos hv)]
      split_ifs <;> simp

end CFSG.KC.KStep

end
