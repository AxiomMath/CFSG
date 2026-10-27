module

public import CFSG.Certificates.Kernel.M3BFib.Fib13Sound
public import Certificates.Data.Kernel.M3BFib.Fib0
public import Certificates.Data.Kernel.M3BFib.Fib0Root

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.M3BF

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
open CFSG.Monster.Generated
open Timmesfeld.M3B (B0 fT fLam fpt unpack nPts fRootV repD nfD eOf)

@[expose] def GoodMat (A : List ℕ) : Prop := A.length = 12 ∧ ∀ r ∈ A, GoodRow r

@[expose] noncomputable def vecK (A : List ℕ) (w : Fin 12 → ZMod 3) : Fin 12 → ZMod 3 :=
  fun i => ∑ j : Fin 12, w j * vz (A.getD j 0) i

theorem goodMat_of_goodM {A : List ℕ} (h : goodM A = true) : GoodMat A := by
  unfold goodM at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, fun r hr => h.2 r hr⟩

theorem vz_zero : vz 0 = 0 := by
  funext k
  revert k
  decide +kernel

theorem goodRow_zero : GoodRow 0 := by
  unfold GoodRow
  decide +kernel

theorem goodMat_idRows : GoodMat idRows := by
  unfold GoodMat
  decide +kernel

theorem vz_mvK {A : List ℕ} (hA : GoodMat A) (y : ℕ) : vz (mvK y A) = vecK A (vz y) := by
  have e : mvK y A = applyK (A, 0) y := by simp only [applyK, mvK, Nat.add_eq, Nat.add_zero]
  rw [e, vz_applyK (M := (A, 0)) ⟨hA.1, hA.2, goodRow_zero⟩]
  funext i
  simp only [affV, vecK, vz_zero, Pi.zero_apply, zero_add]

theorem mmK_length (A B : List ℕ) : (mmK A B).length = A.length := List.length_map _

theorem goodMat_mmK {A B : List ℕ} (hA : A.length = 12) : GoodMat (mmK A B) := by
  refine ⟨by rw [mmK_length, hA], fun r hr => ?_⟩
  unfold mmK at hr
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 hr
  exact goodRow_red _

theorem vecK_mmK {A B : List ℕ} (hA : A.length = 12) (hB : GoodMat B) (w : Fin 12 → ZMod 3) :
    vecK (mmK A B) w = vecK B (vecK A w) := by
  funext i
  have hr : ∀ j : Fin 12, vz ((mmK A B).getD j 0) i =
      ∑ k : Fin 12, vz (A.getD j 0) k * vz (B.getD k 0) i := by
    intro j
    have e : (mmK A B).getD j 0 = mvK (A.getD j 0) B :=
      getD_map_lt (f := fun r => mvK r B) (d := 0) (by rw [hA]; exact j.isLt)
    rw [e, vz_mvK hB]
    rfl
  simp only [vecK, hr, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem coordChk_spec {ms : List AffK} {sM sI : List ℕ} {K : List (List ℕ)}
    (h : coordChk ms sM sI K = true) :
    (∀ M ∈ ms, M.2 = 0 ∧ GoodMat M.1) ∧ GoodMat sM ∧ GoodMat sI ∧ mmK sI sM = idRows ∧
      ∀ m < 4, K.getD m [] = mmK (mmK sM (ms.getD m ([], 0)).1) sI := by
  unfold coordChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, -⟩, h8⟩ := h
  exact ⟨fun M hM => ⟨(h2 M hM).1, goodMat_of_goodM (h2 M hM).2⟩, goodMat_of_goodM h3,
    goodMat_of_goodM h4, h5, h8⟩

theorem normChk_spec {K D : List (List ℕ)} {hw nw : List ℕ} (h : normChk K hw nw D = true) :
    D.length = 26 ∧ (∀ A ∈ D, blkDiag A = true) ∧ D.getD 0 [] = idRows ∧
      (∀ e < 12, D.getD (e + 1) [] = mmK (D.getD e []) (prodK K hw)) ∧
      ∀ e < 13, D.getD (e + 13) [] = mmK (prodK K nw) (D.getD e []) := by
  unfold normChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem f0S_lane_lt {y : ℕ} (hy : GoodRow y) (k : ℕ) : lane y k < 3 := by
  by_cases hk : k < 12
  · rw [f13S_lane_eq hy hk]
    exact getD_mem_lt (dig3_lt y) (by norm_num) _
  · rw [f13S_lane_big hy (by omega)]
    norm_num

theorem f0S_vz_lane {y : ℕ} (hy : GoodRow y) (k : Fin 12) : vz y k = (lane y k : ZMod 3) := by
  rw [f13S_lane_eq hy k.isLt]
  rfl

theorem f0S_blkK (y m : ℕ) :
    blkK y m = lane y (3 * m) + 3 * lane y (3 * m + 1) + 9 * lane y (3 * m + 2) := by
  change Nat.add (lane y (Nat.mul 3 m)) (Nat.mul 3 (Nat.add (lane y (Nat.mul 3 m + 1))
    (Nat.mul 3 (Nat.add (lane y (Nat.mul 3 m + 2)) (Nat.mul 3 0))))) = _
  simp only [Nat.add_eq, Nat.mul_eq]
  ring

theorem f0S_lane_blk0 {y m : ℕ} (h : blkK y m = 0) {k : ℕ} (hk : k / 3 = m) : lane y k = 0 := by
  rw [f0S_blkK] at h
  have e : k = 3 * m ∨ k = 3 * m + 1 ∨ k = 3 * m + 2 := by omega
  rcases e with rfl | rfl | rfl <;> omega

theorem f0S_lane_out {r m : ℕ} (h1 : r % 64 ^ (3 * m) = 0) (h2 : r < 64 ^ (3 * m + 3)) {k : ℕ}
    (hk : k / 3 ≠ m) : lane r k = 0 := by
  change r / 64 ^ k % 64 = 0
  rcases Nat.lt_or_ge k (3 * m) with hk' | hk'
  · obtain ⟨s, rfl⟩ := Nat.dvd_of_mod_eq_zero h1
    obtain ⟨t, ht⟩ : ∃ t, 3 * m = k + (t + 1) := ⟨3 * m - k - 1, by omega⟩
    have e : 64 ^ (3 * m) * s = 64 ^ k * (64 * (64 ^ t * s)) := by
      rw [ht, pow_add, pow_succ]
      ring
    rw [e, Nat.mul_div_cancel_left _ (by positivity), Nat.mul_mod_right]
  · have : r < 64 ^ k := lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt this]

theorem f0S_qIdx {y : ℕ} (hy : GoodRow y) : ∀ fr : List ℕ, fr.Nodup → (∀ f ∈ fr, f < 12) →
    qIdx fr y < 3 ^ fr.length ∧
      ptQ fr (qIdx fr y) = ∑ k : Fin 12, (if (k : ℕ) ∈ fr then lane y k else 0) * 64 ^ (k : ℕ)
  | [], _, _ => ⟨by norm_num [qIdx], by simp [ptQ]⟩
  | f :: fr, hn, h12 => by
    rw [List.nodup_cons] at hn
    have hf : f < 12 := h12 f List.mem_cons_self
    obtain ⟨hi', e⟩ := f0S_qIdx hy fr hn.2 fun g hg => h12 g (List.mem_cons_of_mem _ hg)
    have hv : lane y f < 3 := f0S_lane_lt hy f
    have hq : qIdx (f :: fr) y = lane y f + 3 * qIdx fr y := rfl
    refine ⟨?_, ?_⟩
    · rw [hq, List.length_cons, pow_succ]
      omega
    · change (qIdx (f :: fr) y) % 3 * 64 ^ f + ptQ fr ((qIdx (f :: fr) y) / 3) = _
      have e1 : (lane y f + 3 * qIdx fr y) % 3 = lane y f := by omega
      have e2 : (lane y f + 3 * qIdx fr y) / 3 = qIdx fr y := by omega
      rw [hq, e1, e2, e]
      have hk : ∀ k : Fin 12, (if (k : ℕ) ∈ f :: fr then lane y k else 0) * 64 ^ (k : ℕ) =
          (if k = ⟨f, hf⟩ then lane y f * 64 ^ f else 0) +
            (if (k : ℕ) ∈ fr then lane y k else 0) * 64 ^ (k : ℕ) := by
        intro k
        by_cases hkf : k = ⟨f, hf⟩
        · subst hkf
          simp [hn.1]
        · have hne : (k : ℕ) ≠ f := fun e' => hkf (Fin.ext e')
          simp [hne, hkf]
      rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp

theorem f0S_pow_sum {p : ℕ} (hp : p < 12) :
    64 ^ p = ∑ k : Fin 12, (if (k : ℕ) = p then 1 else 0) * 64 ^ (k : ℕ) := by
  rw [Finset.sum_eq_single ⟨p, hp⟩ (fun b _ hb => by
    rw [if_neg fun h => hb (Fin.ext h), zero_mul]) (by simp)]
  simp

theorem f0S_blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem f0S_blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
  exact h

theorem f0S_repK_def (n : ℕ) : repK n =
    bif Nat.blt n 758 then
      (bif Nat.blt n 29 then
        (bif Nat.blt n 2 then
          (bif Nat.blt n 1 then 0 else Nat.add (Nat.pow 64 9) (ptQ (frL 3) (Nat.sub n 1)))
        else Nat.add (Nat.pow 64 6) (ptQ (frL 2) (Nat.sub n 2)))
      else Nat.add (Nat.pow 64 3) (ptQ (frL 1) (Nat.sub n 29)))
    else Nat.add (Nat.pow 64 0) (ptQ (frL 0) (Nat.sub n 758)) := rfl

theorem f0S_repK_off {i q : ℕ} (hi : i < 4) (hq : q < 3 ^ (9 - 3 * i)) :
    repK (offK i + q) = 64 ^ (3 * i) + ptQ (frL i) q := by
  interval_cases i
  · change repK (758 + q) = 64 ^ 0 + ptQ (frL 0) q
    rw [f0S_repK_def, f0S_blt_f (a := 758 + q) (b := 758) (by omega), cond_false]
    change 64 ^ 0 + ptQ (frL 0) (758 + q - 758) = _
    rw [Nat.add_sub_cancel_left]
  · have hq' : q < 729 := by simpa using hq
    change repK (29 + q) = 64 ^ 3 + ptQ (frL 1) q
    rw [f0S_repK_def, f0S_blt_t (a := 29 + q) (b := 758) (by omega),
      f0S_blt_f (a := 29 + q) (b := 29) (by omega), cond_true, cond_false]
    change 64 ^ 3 + ptQ (frL 1) (29 + q - 29) = _
    rw [Nat.add_sub_cancel_left]
  · have hq' : q < 27 := by simpa using hq
    change repK (2 + q) = 64 ^ 6 + ptQ (frL 2) q
    rw [f0S_repK_def, f0S_blt_t (a := 2 + q) (b := 758) (by omega),
      f0S_blt_t (a := 2 + q) (b := 29) (by omega), f0S_blt_f (a := 2 + q) (b := 2) (by omega),
      cond_true, cond_true, cond_false]
    change 64 ^ 6 + ptQ (frL 2) (2 + q - 2) = _
    rw [Nat.add_sub_cancel_left]
  · have hq' : q < 1 := by simpa using hq
    change repK (1 + q) = 64 ^ 9 + ptQ (frL 3) q
    rw [f0S_repK_def, f0S_blt_t (a := 1 + q) (b := 758) (by omega),
      f0S_blt_t (a := 1 + q) (b := 29) (by omega), f0S_blt_t (a := 1 + q) (b := 2) (by omega),
      f0S_blt_f (a := 1 + q) (b := 1) (by omega), cond_true, cond_true, cond_true, cond_false]
    change 64 ^ 9 + ptQ (frL 3) (1 + q - 1) = _
    rw [Nat.add_sub_cancel_left]

@[expose] noncomputable def f0S_br (D : List (List ℕ)) (tb : List ℕ) (y i : ℕ) : ℕ :=
  Nat.add (offK i) (qIdx (frL i) (mvK y (D.getD (tb.getD (Nat.add (Nat.mul 27 i) (blkK y i)) 0) [])))

theorem f0S_nidxK_def (D : List (List ℕ)) (tb : List ℕ) (y : ℕ) : nidxK D tb y =
    bif blkK y 0 == 0 then
      (bif blkK y 1 == 0 then
        (bif blkK y 2 == 0 then (bif blkK y 3 == 0 then 0 else f0S_br D tb y 3)
        else f0S_br D tb y 2)
      else f0S_br D tb y 1)
    else f0S_br D tb y 0 := rfl

theorem f0S_frL_mem {i : ℕ} (hi : i < 4) (k : ℕ) (hk : k < 12) : k ∈ frL i ↔ 3 * i + 3 ≤ k := by
  unfold frL
  rw [List.mem_range'_1]
  simp only [Nat.mul_eq, Nat.sub_eq]
  omega

theorem f0S_blkL_mem (i k : ℕ) : k ∈ blkL i ↔ k / 3 = i := by
  unfold blkL
  simp only [List.mem_cons, List.not_mem_nil, or_false, Nat.mul_eq]
  omega

theorem f0S_branch {D : List (List ℕ)} {tb : List ℕ}
    (hD : ∀ e < 26, GoodMat (D.getD e []) ∧ blkDiag (D.getD e []) = true)
    (ht : tabChk D tb = true) {z : ℕ} (hz : GoodRow z) {i : ℕ} (hi : i < 4)
    (hpre : ∀ j < i, blkK z j = 0) (hb : blkK z i ≠ 0) :
    f0S_br D tb z i < nRep ∧ ∃ e < 26, vz (mvK z (D.getD e [])) = vz (repK (f0S_br D tb z i)) := by
  unfold f0S_br
  simp only [Nat.add_eq, Nat.mul_eq]
  have hb27 : blkK z i < 27 := by
    rw [f0S_blkK]
    have := f0S_lane_lt hz (3 * i)
    have := f0S_lane_lt hz (3 * i + 1)
    have := f0S_lane_lt hz (3 * i + 2)
    omega
  unfold tabChk at ht
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, List.mem_range'_1,
    Nat.blt_eq, Nat.add_eq, Nat.mul_eq] at ht
  obtain ⟨he, hy1⟩ := ht.2 i hi (blkK z i) ⟨by omega, by omega⟩
  generalize tb.getD (27 * i + blkK z i) 0 = e at he hy1 ⊢
  obtain ⟨hDg, hDb⟩ := hD e he
  have hrow : ∀ j < 12, (D.getD e []).getD j 0 % 64 ^ (3 * (j / 3)) = 0 ∧
      (D.getD e []).getD j 0 < 64 ^ (3 * (j / 3) + 3) := by
    intro j hj
    unfold blkDiag at hDb
    rw [List.all_eq_true] at hDb
    have h := hDb j (List.mem_range.2 hj)
    unfold blkRow at h
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
    exact h
  have hDz : ∀ j k : Fin 12, (j : ℕ) / 3 ≠ (k : ℕ) / 3 → vz ((D.getD e []).getD j 0) k = 0 := by
    intro j k hjk
    have hg : GoodRow ((D.getD e []).getD j 0) :=
      hDg.2 _ (getD_mem (by rw [hDg.1]; exact j.isLt))
    rw [f0S_vz_lane hg, f0S_lane_out (hrow j j.isLt).1 (hrow j j.isLt).2 (Ne.symm hjk),
      Nat.cast_zero]
  have hz0 : ∀ j : Fin 12, (j : ℕ) / 3 < i → vz z j = 0 := by
    intro j hj
    rw [f0S_vz_lane hz, f0S_lane_blk0 (hpre _ hj) rfl, Nat.cast_zero]
  have hbn : (blkL i).Nodup := by
    unfold blkL
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true, not_false_eq_true, Nat.mul_eq]
    omega
  have hb12 : ∀ f ∈ blkL i, f < 12 := fun f hf => by
    rw [f0S_blkL_mem] at hf
    omega
  obtain ⟨-, hyE⟩ := f0S_qIdx hz (blkL i) hbn hb12
  have hyv : ∀ j : Fin 12, vz (ptQ (blkL i) (blkK z i)) j = if (j : ℕ) / 3 = i then vz z j else 0 := by
    intro j
    change vz (ptQ (blkL i) (qIdx (blkL i) z)) j = _
    rw [hyE, f13S_vz_sum (fun k => by split_ifs <;> [exact lt_trans (f0S_lane_lt hz k) (by norm_num);
      norm_num]) j]
    by_cases h : (j : ℕ) / 3 = i
    · rw [if_pos ((f0S_blkL_mem i j).2 h), if_pos h, f0S_vz_lane hz]
    · rw [if_neg (mt (f0S_blkL_mem i j).1 h), if_neg h, Nat.cast_zero]
  have hw : GoodRow (mvK (ptQ (blkL i) (blkK z i)) (D.getD e [])) := goodRow_red _
  rw [f0S_blkK] at hy1
  have hw0 := f0S_lane_lt hw (3 * i)
  have hw1 := f0S_lane_lt hw (3 * i + 1)
  have hw2 := f0S_lane_lt hw (3 * i + 2)
  have hx : GoodRow (mvK z (D.getD e [])) := goodRow_red _
  have hfn : (frL i).Nodup := List.nodup_range'
  have hf12 : ∀ f ∈ frL i, f < 12 := fun f hf => by
    unfold frL at hf
    rw [List.mem_range'_1] at hf
    simp only [Nat.mul_eq, Nat.sub_eq] at hf
    omega
  obtain ⟨hq, hxE⟩ := f0S_qIdx hx (frL i) hfn hf12
  have hfl : (frL i).length = 9 - 3 * i := by
    unfold frL
    rw [List.length_range']
    rfl
  rw [hfl] at hq
  refine ⟨?_, e, he, ?_⟩
  · unfold nRep
    interval_cases i <;> simp only [offK] at hq ⊢ <;> norm_num at hq ⊢ <;> omega
  rw [f0S_repK_off hi hq, hxE, f0S_pow_sum (by omega : 3 * i < 12), ← Finset.sum_add_distrib]
  simp only [← add_mul]
  funext k
  rw [f13S_vz_sum (fun k => by
    have := f0S_lane_lt hx k
    split_ifs <;> omega) k]
  have hmv : ∀ y, vz (mvK y (D.getD e [])) k = ∑ j : Fin 12, vz y j * vz ((D.getD e []).getD j 0) k :=
    fun y => by rw [vz_mvK hDg]; rfl
  have hk12 := k.isLt
  rcases Nat.lt_trichotomy ((k : ℕ) / 3) i with hk | hk | hk
  ·
    have n1 : ¬ (k : ℕ) = 3 * i := by omega
    have n2 : (k : ℕ) ∉ frL i := by
      rw [f0S_frL_mem hi k hk12]
      omega
    rw [if_neg n1, if_neg n2, hmv]
    refine Eq.trans (Finset.sum_eq_zero fun j _ => ?_) (by norm_num)
    by_cases hj : (j : ℕ) / 3 = (k : ℕ) / 3
    · rw [hz0 j (by omega), zero_mul]
    · rw [hDz j k hj, mul_zero]
  ·
    have n2 : (k : ℕ) ∉ frL i := by
      rw [f0S_frL_mem hi k hk12]
      omega
    rw [if_neg n2, add_zero]
    have e1 : vz (mvK z (D.getD e [])) k = vz (mvK (ptQ (blkL i) (blkK z i)) (D.getD e [])) k := by
      rw [hmv, hmv]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (j : ℕ) / 3 = i
      · rw [hyv j, if_pos hj]
      · rw [hDz j k (by omega), mul_zero, mul_zero]
    rw [e1, f0S_vz_lane hw]
    have e2 : (k : ℕ) = 3 * i ∨ (k : ℕ) = 3 * i + 1 ∨ (k : ℕ) = 3 * i + 2 := by omega
    rcases e2 with e2 | e2 | e2 <;> rw [e2]
    · rw [if_pos rfl]
      have : lane (mvK (ptQ (blkL i) (blkK z i)) (D.getD e [])) (3 * i) = 1 := by omega
      rw [this]
    · rw [if_neg (by omega)]
      have : lane (mvK (ptQ (blkL i) (blkK z i)) (D.getD e [])) (3 * i + 1) = 0 := by omega
      rw [this]
    · rw [if_neg (by omega)]
      have : lane (mvK (ptQ (blkL i) (blkK z i)) (D.getD e [])) (3 * i + 2) = 0 := by omega
      rw [this]
  ·
    have n1 : ¬ (k : ℕ) = 3 * i := by omega
    have p2 : (k : ℕ) ∈ frL i := by
      rw [f0S_frL_mem hi k hk12]
      omega
    rw [if_neg n1, if_pos p2, zero_add, f0S_vz_lane hx]

theorem f0S_beq_t {a : ℕ} (h : a = 0) : (a == 0) = true := beq_iff_eq.2 h

theorem f0S_beq_f {a : ℕ} (h : a ≠ 0) : (a == 0) = false := by simpa using h

theorem nidxK_spec {D : List (List ℕ)} {tb : List ℕ}
    (hD : ∀ e < 26, GoodMat (D.getD e []) ∧ blkDiag (D.getD e []) = true)
    (ht : tabChk D tb = true) (z : ℕ) (hz : GoodRow z) :
    nidxK D tb z < nRep ∧ ∃ e < 26, vz (mvK z (D.getD e [])) = vz (repK (nidxK D tb z)) := by
  rw [f0S_nidxK_def]
  by_cases h0 : blkK z 0 = 0
  · rw [f0S_beq_t h0, cond_true]
    by_cases h1 : blkK z 1 = 0
    · rw [f0S_beq_t h1, cond_true]
      by_cases h2 : blkK z 2 = 0
      · rw [f0S_beq_t h2, cond_true]
        by_cases h3 : blkK z 3 = 0
        · rw [f0S_beq_t h3, cond_true]
          refine ⟨by unfold nRep; norm_num, 0, by norm_num, ?_⟩
          have hz0 : vz z = 0 := by
            funext k
            rw [f0S_vz_lane hz, Pi.zero_apply]
            have hk : (k : ℕ) / 3 = 0 ∨ (k : ℕ) / 3 = 1 ∨ (k : ℕ) / 3 = 2 ∨ (k : ℕ) / 3 = 3 := by
              have := k.isLt
              omega
            rcases hk with hk | hk | hk | hk
            · rw [f0S_lane_blk0 h0 hk, Nat.cast_zero]
            · rw [f0S_lane_blk0 h1 hk, Nat.cast_zero]
            · rw [f0S_lane_blk0 h2 hk, Nat.cast_zero]
            · rw [f0S_lane_blk0 h3 hk, Nat.cast_zero]
          have hr0 : repK 0 = 0 := rfl
          rw [vz_mvK (hD 0 (by norm_num)).1, hz0, hr0, vz_zero]
          funext k
          simp [vecK]
        · rw [f0S_beq_f h3, cond_false]
          exact f0S_branch hD ht hz (by norm_num) (fun j hj => by
            interval_cases j
            · exact h0
            · exact h1
            · exact h2) h3
      · rw [f0S_beq_f h2, cond_false]
        exact f0S_branch hD ht hz (by norm_num) (fun j hj => by
          interval_cases j
          · exact h0
          · exact h1) h2
    · rw [f0S_beq_f h1, cond_false]
      exact f0S_branch hD ht hz (by norm_num) (fun j hj => by
        interval_cases j
        exact h0) h1
  · rw [f0S_beq_f h0, cond_false]
    exact f0S_branch hD ht hz (by norm_num) (fun j hj => absurd hj (Nat.not_lt_zero _)) h0

theorem bit_iff (m i : ℕ) : bit m i = true ↔ m.testBit i = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  unfold bit
  rw [beq_iff_eq]
  rfl

theorem bit_lor_pow {m p i : ℕ} (h : bit (Nat.lor m (Nat.pow 2 p)) i = true) :
    bit m i = true ∨ i = p := by
  rw [bit_iff] at h ⊢
  have e : Nat.lor m (Nat.pow 2 p) = m ||| 2 ^ p := rfl
  rw [e, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h.symm

theorem bit_pow_sub_one {n i : ℕ} (h : i < n) : bit (Nat.sub (Nat.pow 2 n) 1) i = true := by
  rw [bit_iff]
  have e : Nat.sub (Nat.pow 2 n) 1 = 2 ^ n - 1 := rfl
  rw [e, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
  exact h

theorem bit_rootMask0 : ∀ (rs : List (ℕ × ℕ × ℕ)) (i : ℕ), bit (rootMask0 rs) i = true →
    ∃ r ∈ rs, r.2.1 = i
  | [], i, h => by
    rw [bit_iff] at h
    change Nat.testBit 0 i = true at h
    simp at h
  | r :: rs, i, h => by
    change bit (Nat.lor (rootMask0 rs) (Nat.pow 2 r.2.1)) i = true at h
    rcases bit_lor_pow h with h | rfl
    · obtain ⟨r', hr', e⟩ := bit_rootMask0 rs i h
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩
    · exact ⟨r, List.mem_cons_self, rfl⟩

theorem rowsK0_spec {K D : List (List ℕ)} {tb : List ℕ} (P : ℕ → Prop)
    (hs : ∀ p q k, p < nRep → k < 4 → nidxK D tb (mvK (repK p) (K.getD k [])) = q → P q → P p) :
    ∀ (rows : List (ℕ × ℕ × ℕ)) (m m' : ℕ), rowsK0 K D tb rows m = some m' →
      (∀ i, bit m i = true → P i) → ∀ i, bit m' i = true → P i
  | [], m, m', h, hm => by
    change some m = some m' at h
    cases h
    exact hm
  | r :: rows, m, m', h, hm => by
    change (bif Nat.blt r.1 nRep && bit m r.2.1 && Nat.blt r.2.2 4 &&
        nidxK D tb (mvK (repK r.1) (K.getD r.2.2 [])) == r.2.1
      then rowsK0 K D tb rows (Nat.lor m (Nat.pow 2 r.1)) else none) = some m' at h
    cases hc : (Nat.blt r.1 nRep && bit m r.2.1 && Nat.blt r.2.2 4 &&
        nidxK D tb (mvK (repK r.1) (K.getD r.2.2 [])) == r.2.1) with
    | false =>
      rw [hc, cond_false] at h
      cases h
    | true =>
      rw [hc, cond_true] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      refine rowsK0_spec P hs rows _ m' h fun i hi => ?_
      rcases bit_lor_pow hi with hi | rfl
      · exact hm i hi
      · exact hs _ _ _ h1 h3 h4 (hm _ h2)

theorem chain_spec {K D : List (List ℕ)} {tb : List ℕ} {os : List (List (ℕ × ℕ × ℕ))}
    {mk : List ℕ} (P : ℕ → Prop)
    (hs : ∀ p q k, p < nRep → k < 4 → nidxK D tb (mvK (repK p) (K.getD k [])) = q → P q → P p) :
    ∀ n, (∀ j < n, (rowsK0 K D tb (os.getD j []) (mk.getD j 0) == some (mk.getD (j + 1) 0)) = true) →
      (∀ i, bit (mk.getD 0 0) i = true → P i) → ∀ i, bit (mk.getD n 0) i = true → P i
  | 0, _, h0 => h0
  | n + 1, hc, h0 =>
    rowsK0_spec P hs _ _ _ (beq_iff_eq.1 (hc n (by omega)))
      (chain_spec P hs n (fun j hj => hc j (by omega)) h0)

theorem headD_eq_getD (l : List ℕ) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

theorem getLastD_eq_getD {l : List ℕ} {n : ℕ} (h : l.length = n + 1) : l.getLastD 0 = l.getD n 0 := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, h,
    Nat.add_sub_cancel]

section Fibre


theorem vecK_idRows (w : Fin 12 → ZMod 3) : vecK idRows w = w := by
  funext i
  unfold vecK
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [vz_idRows, if_neg hj, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h), vz_idRows, if_pos rfl, mul_one]

@[expose] def Moves (S X : List ℕ) : Prop :=
  GoodMat X ∧ ∀ u, Reach oneK (vecK S u) (vecK S (vecK X u))

theorem moves_id (S : List ℕ) : Moves S idRows :=
  ⟨goodMat_idRows, fun u => by
    rw [vecK_idRows]
    exact Reach.refl _ _⟩

theorem moves_mm {S X Y : List ℕ} (hX : Moves S X) (hY : Moves S Y) : Moves S (mmK X Y) :=
  ⟨goodMat_mmK hX.1.1, fun u => by
    rw [vecK_mmK hX.1.1 hY.1]
    exact (hX.2 u).trans (hY.2 _)⟩

theorem moves_prodK {S : List ℕ} {K : List (List ℕ)} (hK : ∀ m < 4, Moves S (K.getD m [])) :
    ∀ w : List ℕ, (∀ m ∈ w, m < 4) → Moves S (prodK K w)
  | [], _ => moves_id S
  | m :: w, h => moves_mm (hK m (h m List.mem_cons_self))
      (moves_prodK hK w fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))

@[expose] def ToRoot (S : List ℕ) (rs : List (ℕ × ℕ × ℕ)) (n : ℕ) : Prop :=
  ∀ y, FibAct oneK y (vecK S (vz (repK n))) →
    ∃ h ∈ tbL, ∃ r ∈ rs, FibAct oneK (h⁻¹ * y * h) (vz r.1)

theorem fibre0_roots_of_checks (hinv : letterInvCheck () = true)
    {gs : List GenK} {lk : List PD} {sM sI : List ℕ} {K D : List (List ℕ)} {hw nw tb : List ℕ}
    {rs : List (ℕ × ℕ × ℕ)} {os : List (List (ℕ × ℕ × ℕ))} {mk : List ℕ} {n : ℕ}
    (hlk : LK = lk) (hwd : wordChk LpM lk gs = true) (hg : genChk LpM oneK gs = true)
    (hl : lamChk gs = true) (hco : coordChk (mapsOf gs) sM sI K = true)
    (hno : normChk K hw nw D = true)
    (hhn : (hw.all (Nat.blt · 4) && nw.all (Nat.blt · 4)) = true) (htb : tabChk D tb = true)
    (hrt : rootChk sM D rs = true) (hrv : rootVChk0 rs = true)
    (hmk : (maskChk rs mk && mk.length == n + 1) = true)
    (hch : ∀ j < n,
      (rowsK0 K D tb (os.getD j []) (mk.getD j 0) == some (mk.getD (j + 1) 0)) = true) :
    ∀ p < nPts, ∀ x : Gmat, IsAct tbSys x (toD (fpt (fT 0) (fLam 0) (unpack p))) →
      ∃ g ∈ tbL, ∃ v ∈ fRootV 0, IsAct tbSys (g⁻¹ * x * g) (toD (repD 0 v)) := by
  have hT : GoodPD oneK := one_sound.1
  have hmv := maps_move hinv hT (genOK_of_checks hlk hwd hg hl)
  obtain ⟨hms, hSg, hIg, hIS, hK⟩ := coordChk_spec hco
  have hA : ∀ m < 4, GoodMat ((mapsOf gs).getD m ([], 0)).1 ∧
      ∀ w, Reach oneK w (vecK ((mapsOf gs).getD m ([], 0)).1 w) := by
    intro m hm
    have hl4 : (mapsOf gs).length = 4 := by
      unfold coordChk at hco
      simp only [Bool.and_eq_true, beq_iff_eq] at hco
      exact hco.1.1.1.1.1.1.1
    have hmem : (mapsOf gs).getD m ([], 0) ∈ mapsOf gs := getD_mem (by omega)
    obtain ⟨h0, hgM⟩ := hms _ hmem
    obtain ⟨-, x, hx, hxm⟩ := hmv _ hmem
    refine ⟨hgM, fun w y hy => ⟨x, hx, ?_⟩⟩
    have e : affV ((mapsOf gs).getD m ([], 0)) w = vecK ((mapsOf gs).getD m ([], 0)).1 w := by
      funext i
      simp only [affV, vecK, h0, vz_zero, Pi.zero_apply, zero_add]
    rw [← e]
    exact hxm y w hy
  have hSI : ∀ z, vecK sM (vecK sI z) = z := by
    intro z
    rw [← vecK_mmK hIg.1 hSg, hIS, vecK_idRows]
  have hKm : ∀ m < 4, Moves sM (K.getD m []) := by
    intro m hm
    obtain ⟨hgA, hR⟩ := hA m hm
    have hl1 : (mmK sM ((mapsOf gs).getD m ([], 0)).1).length = 12 := by rw [mmK_length, hSg.1]
    rw [hK m hm]
    refine ⟨goodMat_mmK hl1, fun u => ?_⟩
    rw [vecK_mmK hl1 hIg, vecK_mmK hSg.1 hgA, hSI]
    exact hR _
  obtain ⟨hDl, hDb, hD0, hDs, hDn⟩ := normChk_spec hno
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hhn
  have hKh := moves_prodK hKm hw hhn.1
  have hKn := moves_prodK hKm nw hhn.2
  have hlow : ∀ e ≤ 12, Moves sM (D.getD e []) := by
    intro e he
    induction e with
    | zero =>
      rw [hD0]
      exact moves_id _
    | succ e ih =>
      rw [hDs e (by omega)]
      exact moves_mm (ih (by omega)) hKh
  have hDm : ∀ e < 26, Moves sM (D.getD e []) := by
    intro e he
    by_cases h : e ≤ 12
    · exact hlow e h
    · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 13 := ⟨e - 13, by omega⟩
      rw [hDn e' (by omega)]
      exact moves_mm hKn (hlow e' (by omega))
  have hnf : ∀ z, GoodRow z → nidxK D tb z < nRep ∧
      Reach oneK (vecK sM (vz z)) (vecK sM (vz (repK (nidxK D tb z)))) := by
    intro z hz
    obtain ⟨hlt, e, he, hv⟩ := nidxK_spec (fun e he => ⟨(hDm e he).1,
      hDb _ (getD_mem (by omega))⟩) htb z hz
    refine ⟨hlt, ?_⟩
    rw [← hv, vz_mvK (hDm e he).1]
    exact (hDm e he).2 _
  unfold rootChk at hrt
  simp only [List.all_eq_true, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at hrt
  have hroot : ∀ r ∈ rs, ToRoot sM rs r.2.1 := by
    intro r hr y hy
    obtain ⟨⟨-, h2⟩, h3⟩ := hrt r hr
    obtain ⟨h, hh, hyh⟩ := (hDm _ h2).2 _ y hy
    refine ⟨h, hh, r, hr, ?_⟩
    rw [← h3, vz_mvK hSg, vz_mvK (hDm _ h2).1]
    exact hyh
  have hstep : ∀ p q k, p < nRep → k < 4 → nidxK D tb (mvK (repK p) (K.getD k [])) = q →
      ToRoot sM rs q → ToRoot sM rs p := by
    intro p q k _ hk he hq y hy
    obtain ⟨h1, hh1, hy1⟩ := (hKm k hk).2 _ y hy
    rw [← vz_mvK (hKm k hk).1] at hy1
    obtain ⟨-, hR⟩ := hnf (mvK (repK p) (K.getD k [])) (goodRow_red _)
    rw [he] at hR
    obtain ⟨h2, hh2, hy2⟩ := hR _ hy1
    obtain ⟨h3, hh3, r, hr, hy3⟩ := hq _ hy2
    refine ⟨h1 * h2 * h3, tbL.mul_mem (tbL.mul_mem hh1 hh2) hh3, r, hr, ?_⟩
    have e : (h1 * h2 * h3)⁻¹ * y * (h1 * h2 * h3) =
        h3⁻¹ * (h2⁻¹ * (h1⁻¹ * y * h1) * h2) * h3 := by group
    rw [e]
    exact hy3
  simp only [maskChk, Bool.and_eq_true, beq_iff_eq] at hmk
  obtain ⟨⟨hm0, hmL⟩, hlen⟩ := hmk
  have hP0 : ∀ i, bit (mk.getD 0 0) i = true → ToRoot sM rs i := by
    intro i hi
    rw [← headD_eq_getD, hm0] at hi
    obtain ⟨r, hr, rfl⟩ := bit_rootMask0 rs i hi
    exact hroot r hr
  have hall : ∀ i < nRep, ToRoot sM rs i := by
    intro i hi
    refine chain_spec (ToRoot sM rs) hstep n hch hP0 i ?_
    rw [← getLastD_eq_getD hlen, hmL]
    exact bit_pow_sub_one hi
  intro p _ x hx
  have hrow : toMat (fT 0) = fun i => ((dK oneK).1 i).1 := by
    have e : fT 0 = Timmesfeld.M3B.mone := rfl
    funext i j
    rw [e]
    revert i j
    decide +kernel
  have hlam : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.toZ (fLam 0) =
      (dK oneK).2 := by
    have e : fLam 0 = 1 := rfl
    rw [e]
    decide
  have hfib : FibAct oneK x (vfun (unpack p)) := by
    unfold FibAct
    rw [toD_fpt, hrow, hlam] at hx
    exact hx
  obtain ⟨hcg, hcv⟩ := encW_spec (vecK sI (vfun (unpack p)))
  obtain ⟨hlt, hR⟩ := hnf _ hcg
  rw [hcv, hSI] at hR
  obtain ⟨h1, hh1, hy1⟩ := hR x hfib
  obtain ⟨h2, hh2, r, hr, hy2⟩ := hall _ hlt _ hy1
  unfold rootVChk0 at hrv
  obtain ⟨v, hv, hvr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hrv r hr)
  obtain ⟨-, hNd⟩ := pdOf_spec (nfD (B0 ()) (eOf v 0))
  rw [eq_of_pdEq hvr] at hNd
  have hrep : repD 0 v = nfD (B0 ()) (eOf v 0) := by
    unfold repD
    exact if_pos rfl
  refine ⟨h1 * h2, tbL.mul_mem hh1 hh2, v, hv, ?_⟩
  have e2 : (h1 * h2)⁻¹ * x * (h1 * h2) = h2⁻¹ * (h1⁻¹ * x * h1) * h2 := by group
  rw [e2, hrep, ← hNd]
  exact hy2

end Fibre

end CFSG.KC.M3BF

end
