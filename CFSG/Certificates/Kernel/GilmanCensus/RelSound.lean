module

public import CFSG.Certificates.Kernel.GilmanCensus.SmallSound
import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.RankSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def idxI (v : List Int) : List (List Int) → Nat → Option Nat
  | [], _ => none
  | r :: rs, k => if r == v then some k else idxI v rs (k + 1)

structure Rel (dt : Data) (dk : DK) : Prop where
  mode : dt.mode = dk.mode
  N : dt.N = dk.N
  Nlt : dk.N < 128
  d : dt.d = dk.d
  R : LLI dt.R = toI dk.R
  Rlen : ∀ r ∈ dk.R, r.length = dt.n
  RN : dk.R.length = dk.N
  ix : ∀ v : IVec, dt.ix[v]? = idxI v.toList (LLI dt.R) 0
  AR : LLI dt.AR = toI dk.AR
  ARlen : ∀ r ∈ dk.AR, r.length = dt.n
  ARlt : dk.AR.length < 128
  aix : ∀ v : IVec, dt.aix[v]? = idxI v.toList (LLI dt.AR) 0
  absidx : LL dt.absidx = dk.absidx
  rho : dt.rho.toList = dk.rho
  F : LL dt.F = dk.F
  Fsz : ∀ r ∈ dt.F.toList, r.size = dt.d
  FN : dk.F.length = dk.N
  H : LL dt.H = dk.H
  Hsz : ∀ r ∈ dt.H.toList, r.size = dt.d
  HN : dk.H.length = dk.N
  G : ∀ i j, i < dk.N → j < dk.N → dt.G[i]![j]! = gI dk i j
  adj : dt.adj.toList = dk.adj
  aadj : dt.aadj.toList = dk.aadj
  refl : ∀ i < dk.N, ∀ j < 128, (dk.reflP.getD i 0 >>> (7 * j)) % 128 = dt.refl[i]![j]!
  lines : LL dt.lines = dk.lines
  full : dt.full = dk.full

theorem bitsA_lt : ∀ (f i m b k : Nat), m < 2 ^ b → k ∈ bitsA f i m → k < i + b
  | 0, _, _, _, _, _, h => by simp [bitsA] at h
  | f + 1, i, m, b, k, hm, h => by
    simp only [bitsA] at h
    split at h
    · simp at h
    · rename_i h0
      have hb : b ≠ 0 := by
        rintro rfl
        simp at hm
        simp [hm] at h0
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hm2 : m / 2 < 2 ^ b := by rw [Nat.pow_succ] at hm; omega
      split at h
      · rcases List.mem_cons.mp h with h | h
        · omega
        · have := bitsA_lt f (i + 1) (m / 2) b k hm2 h
          omega
      · have := bitsA_lt f (i + 1) (m / 2) b k hm2 h
        omega

theorem bitsK_lt (m b k : Nat) (hm : m < 2 ^ b) (h : k ∈ bitsK m) : k < b := by
  have := bitsA_lt 128 0 m b k hm h
  omega

theorem pow_mono_128 (m b : Nat) (hm : m < 2 ^ b) (hb : b ≤ 128) : m < 2 ^ 128 :=
  Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hb)

@[expose] def zerosL (dk : DK) (v : List Nat) : Nat :=
  (List.range' 0 dk.N).foldl (fun m i => if (dot3K v (fK dk i) == 0) = true then m ||| bitK i else m) 0

theorem fK_eq {dt : Data} {dk : DK} (h : Rel dt dk) (i : Nat) : (dt.F[i]!).toList = fK dk i := by
  rw [getRow, h.F, fK]

theorem zerosOf_eq {dt : Data} {dk : DK} (h : Rel dt dk) (v : Array Nat) :
    zerosOf dt v = zerosL dk v.toList := by
  unfold zerosOf zerosL
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, h.N]
  rw [forIn_ifs (fun i _ => dot3 v dt.F[i]! == 0) (fun i m => m ||| bit i)]
  refine (bind_pure _).trans ?_
  congr 1
  funext m i
  rw [dot3_eq, fK_eq h]
  rfl

theorem toI_getD (R : List (List Nat)) (i : Nat) : (toI R).getD i [] = (R.getD i []).map Int.ofNat := by
  rw [toI, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases R[i]? <;> rfl

theorem idxI_toI (x : List Nat) : ∀ (R : List (List Nat)) (k : Nat),
    idxI (x.map Int.ofNat) (toI R) k = idxOfL x R k
  | [], _ => rfl
  | r :: rs, k => by
    have e : (r.map Int.ofNat == x.map Int.ofNat) = (r == x) := by
      have hi : ∀ a b : List Nat, a.map Int.ofNat = b.map Int.ofNat → a = b := by
        intro a b hab
        have := congrArg (List.map Int.toNat) hab
        have e2 : Int.toNat ∘ Int.ofNat = id := funext fun _ => rfl
        rw [List.map_map, List.map_map, e2, List.map_id, List.map_id] at this
        exact this
      by_cases hrx : r = x
      · subst hrx
        rw [beq_self_eq_true, beq_self_eq_true]
      · have : r.map Int.ofNat ≠ x.map Int.ofNat := fun hh => hrx (hi _ _ hh)
        rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr hrx]
    simp only [toI, List.map_cons, idxI, idxOfL] at *
    rw [e]
    split
    · rfl
    · exact idxI_toI x rs (k + 1)

theorem getD_nonneg : ∀ (r : List Nat) (t : Nat), 0 ≤ (r.map Int.ofNat).getD t 0
  | [], _ => by simp
  | a :: r, 0 => by simp
  | a :: r, t + 1 => by
    rw [List.map_cons, List.getD_cons_succ]
    exact getD_nonneg r t

theorem idxI_neg (v : List Int) (t : Nat) (ht : v.getD t 0 < 0) : ∀ (R : List (List Nat)) (k : Nat),
    idxI v (toI R) k = none
  | [], _ => rfl
  | r :: rs, k => by
    have hne : (r.map Int.ofNat == v) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      have := getD_nonneg r t
      omega
    simp only [toI, List.map_cons, idxI] at *
    rw [hne]
    exact idxI_neg v t ht rs (k + 1)

theorem zipWith_sub_nat : ∀ (a b : List Nat), leAll b a = true →
    List.zipWith (fun x y : Int => x - y) (a.map Int.ofNat) (b.map Int.ofNat) =
      (List.zipWith (· - ·) a b).map Int.ofNat
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | x :: xs, y :: ys, h => by
    simp only [leAll, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.zipWith_cons_cons, List.cons.injEq]
    refine ⟨?_, zipWith_sub_nat xs ys h.2⟩
    simp only [Int.ofNat_eq_natCast]
    omega

theorem zipWith_sub_neg : ∀ (a b : List Nat), a.length = b.length → leAll b a = false →
    ∃ t, (List.zipWith (fun x y : Int => x - y) (a.map Int.ofNat) (b.map Int.ofNat)).getD t 0 < 0
  | [], [], _, h => by simp [leAll] at h
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | x :: xs, y :: ys, hl, h => by
    simp only [leAll, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at h
    rcases h with h | h
    · exact ⟨0, by simp; omega⟩
    · obtain ⟨t, ht⟩ := zipWith_sub_neg xs ys (by simpa using hl) h
      exact ⟨t + 1, by simpa using ht⟩

theorem vsub_toList (r s : IVec) (hs : s.size = r.size) :
    (vsub r s).toList = List.zipWith (fun x y : Int => x - y) r.toList s.toList := by
  unfold vsub
  apply List.ext_getElem
  · simp [hs]
  · intro t h1 h2
    simp only [Array.toList_ofFn, List.getElem_ofFn, List.getElem_zipWith, Array.getElem_toList]
    rw [getElem!_pos r t (by simpa using h1), getElem!_pos s t (by simp at h1; omega)]

theorem row_toList {dt : Data} {dk : DK} (h : Rel dt dk) (i : Nat) (hi : i < dk.N) :
    (dt.R[i]!).toList = (dk.R.getD i []).map Int.ofNat := by
  rw [getRowI, h.R, toI_getD]

theorem row_size {dt : Data} {dk : DK} (h : Rel dt dk) (i : Nat) (hi : i < dk.N) :
    (dt.R[i]!).size = dt.n := by
  rw [← Array.length_toList, row_toList h i hi, List.length_map]
  apply h.Rlen
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [h.RN]; exact hi)]
  exact List.getElem_mem _

theorem ix_sub {dt : Data} {dk : DK} (h : Rel dt dk) (i j : Nat) (hi : i < dk.N) (hj : j < dk.N) :
    dt.ix[vsub dt.R[i]! dt.R[j]!]? = subIdx dk.R (dk.R.getD i []) (dk.R.getD j []) := by
  rw [h.ix, vsub_toList _ _ (by rw [row_size h i hi, row_size h j hj]), row_toList h i hi,
    row_toList h j hj, h.R, subIdx]
  split
  · rename_i hle
    rw [zipWith_sub_nat _ _ hle, idxI_toI]
  · rename_i hle
    have hl : (dk.R.getD i []).length = (dk.R.getD j []).length := by
      have s1 := row_size h i hi
      have s2 := row_size h j hj
      rw [← Array.length_toList, row_toList h i hi, List.length_map] at s1
      rw [← Array.length_toList, row_toList h j hj, List.length_map] at s2
      omega
    obtain ⟨t, ht⟩ := zipWith_sub_neg _ _ hl (by simpa using hle)
    exact idxI_neg _ t ht _ 0

theorem arr_filter {α : Type} (l : List α) (p : α → Bool) : l.toArray.filter p = (l.filter p).toArray := by
  simp

theorem arr_any {α : Type} (l : List α) (p : α → Bool) : l.toArray.any p = l.any p := by
  simp

theorem any_congr' {α : Type} (p q : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.any p = l.any q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      any_congr' p q l (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem simpOf_eq {dt : Data} {dk : DK} (h : Rel dt dk) (mask : Nat) (hm : mask < 2 ^ dk.N) :
    simpOf dt mask = (simpOfK dk mask).toArray := by
  have h128 := pow_mono_128 mask dk.N hm (Nat.le_of_lt h.Nlt)
  unfold simpOf simpOfK
  rw [bitsOf_eq mask h128, arr_filter]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [arr_any]
  congr 1
  apply any_congr'
  intro j hj
  rw [ix_sub h i j (bitsK_lt mask dk.N i hm hi) (bitsK_lt mask dk.N j hm hj)]
  rfl

theorem rootsOfMask_eq {dt : Data} {dk : DK} (h : Rel dt dk) (mask : Nat) (hm : mask < 2 ^ dk.N) :
    LLI (rootsOfMask dt.R mask) = toI (rootsOfMaskK dk.R mask) := by
  have h128 := pow_mono_128 mask dk.N hm (Nat.le_of_lt h.Nlt)
  unfold rootsOfMask rootsOfMaskK
  rw [bitsOf_eq mask h128, LLI, toI]
  simp only [List.map_toArray, List.toList_toArray, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact row_toList h i (bitsK_lt mask dk.N i hm hi)

theorem kindOf_eq {dt : Data} {dk : DK} (h : Rel dt dk) (mask : Nat) (hm : mask < 2 ^ dk.N) :
    kindOf dt mask = kindOfK dk mask := by
  have h128 := pow_mono_128 mask dk.N hm (Nat.le_of_lt h.Nlt)
  unfold kindOf kindOfK
  rw [typeName_eq, popc_eq mask h128, rankQ_eq, rootsOfMask_eq h mask hm]
  have hsz : ∀ r ∈ (rootsOfMask dt.R mask).toList, r.size = dt.n := by
    intro r hr
    unfold rootsOfMask at hr
    rw [bitsOf_eq mask h128] at hr
    simp only [List.map_toArray, List.toList_toArray, List.mem_map] at hr
    obtain ⟨i, hi, rfl⟩ := hr
    exact row_size h i (bitsK_lt mask dk.N i hm hi)
  intro r hr
  rw [hsz r hr]
  have hne : 0 < (rootsOfMask dt.R mask).size := by
    have := List.length_pos_of_mem hr
    simpa using this
  rw [getElem!_pos _ 0 hne]
  exact (hsz _ (Array.getElem_mem_toList _)).symm

end Certificates.GilmanCensusK

end
