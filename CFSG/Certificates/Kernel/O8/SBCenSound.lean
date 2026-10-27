module

public import Certificates.Data.Kernel.O8.SBCen
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillC
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchExt

public section

namespace CFSG.KC.SBCen

open CFSG.KC.Enum CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem cen_strictN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem cen_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem cen_beq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem cen_blt (a b : ℕ) : Nat.blt a b = decide (a < b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.blt_eq, decide_eq_true_iff])

theorem cen_shl (x k : ℕ) : Nat.shiftLeft x k = x * 2 ^ k := Nat.shiftLeft_eq x k

theorem cen_nIf (b : Bool) (x y : ℕ) :
    Bool.rec (motive := fun _ => ℕ) y x b = if b = true then x else y := by
  cases b <;> rfl

theorem extMulF_eq (N : ℕ) (mul : ℕ → ℕ → ℕ) (F : ℕ → ℕ) (z c d : ℕ) :
    extMulF N mul F z c d = extMul N mul F z c d := by
  unfold extMulF extMul
  simp only [cen_nIf, cen_blt, decide_eq_true_eq]
  rfl

@[expose] def packF (ps : List (ℕ → Bool)) (c : ℕ) : ℕ :=
  ps.foldr (fun p acc => (if p c = true then 1 else 0) + 2 ^ 20 * acc) 0

theorem packF_cons (p : ℕ → Bool) (ps : List (ℕ → Bool)) (c : ℕ) :
    packF (p :: ps) c = (if p c = true then 1 else 0) + 2 ^ 20 * packF ps c := rfl

theorem packF_append (A B : List (ℕ → Bool)) (c : ℕ) :
    packF (A ++ B) c = packF A c + 2 ^ (20 * A.length) * packF B c := by
  induction A with
  | nil => simp [packF]
  | cons p A ih =>
    rw [List.cons_append, packF_cons, packF_cons, ih, List.length_cons, Nat.mul_succ, pow_add]
    ring

theorem packF_and (g : ℕ → Bool) (h : ℕ → ℕ → Bool) (L : List ℕ) (c : ℕ) :
    packF (L.map fun q x => g x && h q x) c =
      if g c = true then packF (L.map fun q x => h q x) c else 0 := by
  induction L with
  | nil => simp [packF]
  | cons q L ih =>
    rw [List.map_cons, List.map_cons, packF_cons, packF_cons, ih]
    cases g c <;> simp

theorem cmL_eq (mul : ℕ → ℕ → ℕ) (c : ℕ) (L : List ℕ) :
    cmL mul c L = packF (L.map fun q x => mul x q == mul q x) c := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    have e : cmL mul c (q :: L) = Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1
        (Nat.beq (mul c q) (mul q c))) (Nat.shiftLeft (cmL mul c L) 20) := rfl
    rw [e, List.map_cons, packF_cons, ih, cen_shl, cen_nIf, cen_beq]
    simp only [beq_iff_eq, decide_eq_true_eq, Nat.add_eq]
    ring

@[expose] def cenPreds (mul : ℕ → ℕ → ℕ) (Q U : List ℕ) : List (ℕ → Bool) :=
  (fun c => mul c c == 0 && c != 0) ::
    ((Q.map fun q c => (mul c c == 0 && c != 0) && (mul c q == mul q c)) ++
      U.map fun u c => isOrd4 mul c && (mul c u == mul u c))

theorem cen_eq (mul : ℕ → ℕ → ℕ) (Q U : List ℕ) (c : ℕ) :
    cen mul Q U Q.length c = packF (cenPreds mul Q U) c := by
  unfold cen
  rw [cen_strictN, cenPreds, packF_cons, packF_append, packF_and, packF_and, List.length_map]
  simp only [cen_nIf, cen_beq, decide_eq_true_eq, cmL_eq, cen_shl, Nat.add_eq, Nat.mul_eq,
    isOrd4]
  by_cases h0 : mul c c = 0
  · by_cases hc : c = 0
    · subst hc
      simp [h0]
    · simp [h0, hc]
      ring
  · by_cases h4 : mul (mul c c) (mul c c) = 0
    · simp [h0, h4, pow_succ, pow_mul]
      ring
    · simp [h0, h4]

theorem sum_ind (p : ℕ → Bool) (g : ℕ → ℕ) (L : List ℕ) :
    (L.map fun c => (if p c = true then 1 else 0) + 2 ^ 20 * g c).sum =
      (L.filter p).length + 2 ^ 20 * (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons, List.map_cons, List.sum_cons]
    cases p a <;> simp <;> ring

theorem div_pow_succ (x i : ℕ) : x / 2 ^ (20 * (i + 1)) = x / 2 ^ 20 / 2 ^ (20 * i) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  ring

section Lanes

variable {L : List ℕ} (hL : L.length < 2 ^ 20)
include hL

theorem lane_zero (p : ℕ → Bool) (ps : List (ℕ → Bool)) :
    (L.map (packF (p :: ps))).sum % 2 ^ 20 = (L.filter p).length := by
  have hX : (L.filter p).length < 2 ^ 20 := lt_of_le_of_lt (List.length_filter_le _ _) hL
  rw [show (L.map (packF (p :: ps))).sum = (L.filter p).length + 2 ^ 20 * (L.map (packF ps)).sum
    from sum_ind p (packF ps) L, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

theorem lane_succ (p : ℕ → Bool) (ps : List (ℕ → Bool)) :
    (L.map (packF (p :: ps))).sum / 2 ^ 20 = (L.map (packF ps)).sum := by
  have hX : (L.filter p).length < 2 ^ 20 := lt_of_le_of_lt (List.length_filter_le _ _) hL
  rw [show (L.map (packF (p :: ps))).sum = (L.filter p).length + 2 ^ 20 * (L.map (packF ps)).sum
    from sum_ind p (packF ps) L, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hX,
    Nat.zero_add]

theorem lane_append (A B : List (ℕ → Bool)) :
    (L.map (packF (A ++ B))).sum / 2 ^ (20 * A.length) = (L.map (packF B)).sum := by
  induction A with
  | nil => simp
  | cons p A ih => rw [List.length_cons, div_pow_succ, List.cons_append, lane_succ hL, ih]

theorem lane_map (g : ℕ → ℕ → Bool) (B : List (ℕ → Bool)) :
    ∀ (Q : List ℕ), ∀ i < Q.length,
      (L.map (packF (Q.map g ++ B))).sum / 2 ^ (20 * i) % 2 ^ 20 = (L.filter (g (Q.getD i 0))).length
  | [], i, hi => by simp at hi
  | q :: Q, 0, _ => by
    rw [Nat.mul_zero, pow_zero, Nat.div_one, List.map_cons, List.cons_append, lane_zero hL]
    rfl
  | q :: Q, i + 1, hi => by
    rw [div_pow_succ, List.map_cons, List.cons_append, lane_succ hL,
      lane_map g B Q i (by simpa using hi), List.getD_cons_succ]

end Lanes

theorem cenLane_eq (T j : ℕ) : cenLane T j = T / 2 ^ (20 * j) % 2 ^ 20 := by
  unfold cenLane
  change (T >>> (20 * j)) &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem census_counts {mul : ℕ → ℕ → ℕ} {Q U : List ℕ} {N T : ℕ} (hN : N < 2 ^ 20)
    (hT : ((List.range N).map (cen mul Q U Q.length)).sum = T) :
    (kInv mul N).length = cenLane T 0 ∧
      (∀ i < Q.length, kCount mul (kInv mul N) (Q.getD i 0) = cenLane T (1 + i)) ∧
      ∀ i < U.length, kCount mul (kOrd4 mul N) (U.getD i 0) = cenLane T (1 + Q.length + i) := by
  have hL : (List.range N).length < 2 ^ 20 := by rw [List.length_range]; exact hN
  have hT' : ((List.range N).map (packF (cenPreds mul Q U))).sum = T := by
    rw [← hT]
    congr 1
    exact List.map_congr_left fun c _ => (cen_eq mul Q U c).symm
  rw [← hT']
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [cenLane_eq, Nat.mul_zero, pow_zero, Nat.div_one, cenPreds, lane_zero hL]
    rfl
  · rw [cenLane_eq, Nat.add_comm 1 i, div_pow_succ, cenPreds, lane_succ hL, lane_map hL _ _ Q i hi,
      kCount, kInv, List.filter_filter]
    congr 2
    funext c
    first | rfl | exact Bool.and_comm _ _
  · rw [cenLane_eq, Nat.add_assoc, Nat.add_comm 1, div_pow_succ, cenPreds, lane_succ hL,
      Nat.mul_add, pow_add, ← Nat.div_div_eq_div_mul,
      show 20 * Q.length = 20 * (Q.map fun q c => (mul c c == 0 && c != 0) && (mul c q == mul q c)).length
        by rw [List.length_map], lane_append hL, ← List.append_nil (U.map _), lane_map hL _ _ U i hi,
      kCount_kOrd4_eq]

theorem natRec_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = ((List.range k).map F).sum
  | 0 => rfl
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_sum F k, List.range_succ, List.map_append, List.sum_append]
    simp [Nat.add_comm]

theorem sumBelow_g (m : ℕ) (f : ℕ → ℕ) : ∀ hi, CFSG.KC.Loop.sumBelow m hi f =
    ((List.range (64 * hi)).map fun i => if i < m then f i else 0).sum
  | 0 => rfl
  | hi + 1 => by
    have e : CFSG.KC.Loop.sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0
        (fun l ih2 => Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (CFSG.KC.Loop.sumBelow m hi f) := rfl
    rw [e, natRec_sum, sumBelow_g m f hi, Nat.mul_succ, List.range_add, List.map_append,
      List.sum_append, Nat.add_eq, Nat.add_comm, List.map_map]
    congr 2
    refine List.map_congr_left fun l _ => ?_
    simp only [Function.comp_apply, cen_nIf, cen_blt, decide_eq_true_eq, cen_shl, Nat.add_eq]
    rw [show hi * 2 ^ 6 = 64 * hi by ring]

theorem sumBelow_list {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi f = ((List.range m).map f).sum := by
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [sumBelow_g, hd, List.range_add, List.map_append, List.sum_append, List.map_map]
  have h2 : ((List.range d).map ((fun i => if i < m then f i else 0) ∘ fun x => m + x)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    simp
  rw [h2, Nat.add_zero]
  congr 1
  exact List.map_congr_left fun i hi => by rw [if_pos (List.mem_range.1 hi)]

theorem sum_blocks (f : ℕ → ℕ) (n : ℕ) : ∀ k, ((List.range (n * k)).map f).sum =
    ((List.range k).map fun s => ((List.range n).map fun i => f (n * s + i)).sum).sum
  | 0 => by simp
  | k + 1 => by
    rw [Nat.mul_succ, List.range_add, List.map_append, List.sum_append, sum_blocks f n k,
      List.range_succ, List.map_append, List.sum_append, List.map_map]
    simp [Function.comp_def]

theorem sum_cenBlk {mul : ℕ → ℕ → ℕ} {Q U : List ℕ} {B : List ℕ}
    (h : ∀ s < 16, cenBlk mul Q U Q.length (8192 * s) = B.getD s 0) :
    ((List.range 131072).map (cen mul Q U Q.length)).sum = ((List.range 16).map fun s => B.getD s 0).sum := by
  rw [show (131072 : ℕ) = 8192 * 16 from rfl, sum_blocks _ 8192 16]
  refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
  rw [← h s (List.mem_range.1 hs), cenBlk, sumBelow_list _ (by norm_num)]
  simp only [Nat.add_eq]

theorem killAtCF_eq_killG (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (N : ℕ) (I R : List ℕ)
    (cO : ℕ → ℕ) (m : ℕ) (χ : Array Bool) (n5 : Bool) (t : ℕ) (ti : ℕ × ℕ) :
    killAtCF mul inv gens N I R cO m χ n5 t ti =
      killG mul inv gens N (kCount mul I) R cO m (fun r => χ[r]!) n5 t ti := rfl

theorem killG_congr (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (N : ℕ) (cI cI' : ℕ → ℕ)
    (R : List ℕ) (cO cO' : ℕ → ℕ) (m : ℕ) (χ : ℕ → Bool) (n5 : Bool) (t : ℕ) (ti : ℕ × ℕ)
    (U : List ℕ) (ht : t ∈ R) (hI : ∀ r ∈ R, cI r = cI' r)
    (hq : queriedG mul inv gens cI' R m χ n5 t ti U = true) (hU : ∀ u ∈ U, cO u = cO' u) :
    killG mul inv gens N cI R cO m χ n5 t ti = killG mul inv gens N cI' R cO' m χ n5 t ti := by
  unfold queriedG at hq
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hq
  unfold killG
  rw [hU t hq.1, hI t ht]
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun r hr => ?_
  rw [hI r hr]
  rcases hq.2 r hr with (h | h) | h
  · simp [h]
  · simp [h]
  · rw [hU r h]

end CFSG.KC.SBCen

end
