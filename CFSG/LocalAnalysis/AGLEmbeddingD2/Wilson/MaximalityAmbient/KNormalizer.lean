module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Defs
public import Certificates.Certificate12632
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc CFSG.AGLEmbeddingD2.Wilson.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Mats

variable
  (hM : MatFacts)
include hM

theorem Mx_eta_gE {n : ℕ} (hn : n ≤ 12) (c : ℕ) :
    Mx (eta gE n c) = rowsMatrix ((List.range n).foldl
      (fun acc j => if c.testBit j then mulT acc qT[j]! else acc) idRows) := by
  induction n with
  | zero => simp [eta, rowsMatrix_idRows]
  | succ n ih =>
    rw [eta_succ, map_mul, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih' := ih (by omega)
    by_cases h : c.testBit n
    · simp only [h, ite_true]
      rw [rowsMatrix_mulT_qT _ (by omega), ih', Mx_q hM (by omega)]
    · simp only [h, Bool.false_eq_true, ite_false]
      rw [ih', map_one, mul_one]

theorem z0_comm_eta {n : ℕ} (hn : n ≤ 12) (c : ℕ) : z0 * eta gE n c = eta gE n c * z0 := by
  induction n with
  | zero => simp [eta]
  | succ n ih =>
    rw [eta_succ]
    have ih' := ih (by omega)
    by_cases h : c.testBit n
    · simp only [h, ite_true]
      rw [← mul_assoc, ih', mul_assoc, Qgens_comm_z0 hM (by omega : n < 12), mul_assoc]
    · have h1 : (if c.testBit n then gE n else 1) = 1 := by simp [h]
      rw [h1, mul_one]
      exact ih'

theorem Mx_qNF (e : Bool) (c : ℕ) : Mx (qNF e c) = rowsMatrix (qProd c e) := by
  have hm := Mx_eta_gE hM (le_refl 12) c
  cases e
  · simp only [qNF, qProd, Bool.false_eq_true, ite_false, one_mul]
    exact hm
  · simp only [qNF, qProd, ite_true]
    rw [map_mul, rowsMatrix_mulT_zT, ← hm, rowsMatrix_zM hM, ← map_mul, ← map_mul,
      z0_comm_eta hM (le_refl 12) c]

theorem Mx_kElt (f : Bool × ℕ × ℕ) : Mx (kElt f) = rowsMatrix (kRows f) := by
  unfold kElt kRows
  obtain ⟨e, c, i⟩ := f
  simp only
  induction i with
  | zero => simp [Mx_qNF hM]
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ,
      ← mul_assoc, map_mul, ih, cTab, rowsMatrix_mulT_frTable, Mx_cE hM]

omit hM in
theorem decodeF_codeF (e : Bool) {c i : ℕ} (hc : c < 4096) (hi : i < 3) :
    decodeF (codeF (e, c, i)) = (e, c, i) := by
  cases e <;> simp only [decodeF, codeF] <;> ext <;> simp <;> omega

omit hM in
theorem codeF_lt (e : Bool) {c i : ℕ} (hc : c < 4096) (hi : i < 3) :
    codeF (e, c, i) < 24576 := by
  cases e <;> simp only [codeF] <;> simp <;> omega

omit hM in
theorem getElem!_map_toArray_range {α : Type*} [Inhabited α] (f : ℕ → α) (m n : ℕ) (hn : n < m) :
    (((List.range m).map f).toArray)[n]! = f n := by
  rw [getElem!_pos _ n (by simp [hn])]
  simp

omit hM in
theorem kTab_getElem {n : ℕ} (hn : n < 24576) : kTab[n]! = kRows (decodeF n) :=
  getElem!_map_toArray_range (fun n => kRows (decodeF n)) 24576 n hn

@[expose] def Sform : Set J := {y | ∃ n < 24576, y = kElt (decodeF n)}

theorem hasForm_sound {X : Array V2} {c i : ℕ} (h : hasForm X c i = true) :
    ∃ n < 24576, rowsMatrix X = Mx (kElt (decodeF n)) := by
  unfold hasForm at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, hi⟩, h | h⟩ := h
  · refine ⟨codeF (false, c, i), codeF_lt false hc hi, ?_⟩
    rw [Mx_kElt hM, ← kTab_getElem (codeF_lt false hc hi), eqRows_iff.1 h]
  · refine ⟨codeF (true, c, i), codeF_lt true hc hi, ?_⟩
    rw [Mx_kElt hM, ← kTab_getElem (codeF_lt true hc hi), eqRows_iff.1 h]

theorem mul_mem_Sform {g : J} {G : Array V2} (hG : Mx g = rowsMatrix G) {n : ℕ} {c i : ℕ}
    (h : hasForm (mulT G (frTable kTab[n]!)) c i = true) (hn : n < 24576) :
    g * kElt (decodeF n) ∈ Sform := by
  obtain ⟨m, hm, e⟩ := hasForm_sound hM h
  refine ⟨m, hm, Mx_injective ?_⟩
  rw [map_mul, hG, Mx_kElt hM, ← e, rowsMatrix_mulT_frTable, kTab_getElem hn]

omit hM in
theorem chkClosure_true : chkClosure = true := by
  have h := Certificates.certificate12632
  unfold kCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

omit hM in
theorem chkNorm_true : chkNorm = true := by
  have h := Certificates.certificate12632
  unfold kCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

omit hM in
theorem chkM_true : chkM = true := by
  have h := Certificates.certificate12632
  unfold kCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.2

omit hM in
theorem kTab_wfR {n : ℕ} (hn : n < 24576) :
    wfR kTab[n]! = true := by
  have h := chkClosure_true
  unfold chkClosure at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hw⟩, -⟩ := h
  rw [Array.all_eq_true] at hw
  have hs' : kTab.size = 24576 := by simpa using hs
  have := hw n (by omega)
  rw [getElem!_pos kTab n (by omega)]
  exact this

omit hM in
theorem chkClosure_parts {n : ℕ} (hn : n < 24576) :
    (∀ j < 12, hasForm (mulT qM[j]! (frTable kTab[n]!)) ((decodeF n).2.1 ^^^ 2 ^ j)
        (decodeF n).2.2 = true ∧
      hasForm (mulT qI[j]! (frTable kTab[n]!)) ((decodeF n).2.1 ^^^ 2 ^ j)
        (decodeF n).2.2 = true) ∧
    hasForm (mulT cMat (frTable kTab[n]!)) (cMask (decodeF n).2.1)
      (((decodeF n).2.2 + 1) % 3) = true ∧
    hasForm (mulT cMat2 (frTable kTab[n]!)) (cMask (cMask (decodeF n).2.1))
      (((decodeF n).2.2 + 2) % 3) = true := by
  have h := chkClosure_true
  unfold chkClosure at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨-, h⟩ := h
  have h1 := h n hn
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

omit hM in
theorem eq_of_rowsMatrix_eq' {X Y : Array V2} (hX : wfR X = true) (hY : wfR Y = true)
    (h : rowsMatrix X = rowsMatrix Y) : X = Y := by
  obtain ⟨hXs, hXw⟩ := wfR_spec hX
  obtain ⟨hYs, hYw⟩ := wfR_spec hY
  refine Array.ext (hXs.trans hYs.symm) fun i h1 h2 => ?_
  have hi : i < 112 := by omega
  have e := congrFun (congrFun h ⟨i, hi⟩)
  have hXi := hXw _ (Array.getElem_mem h1)
  have hYi := hYw _ (Array.getElem_mem h2)
  refine (V2.toVec_inj hXi hYi).1 ?_
  funext j
  have := e j
  simp only [rowsMatrix_apply, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

theorem one_mem_Sform : (1 : J) ∈ Sform := by
  refine ⟨0, by norm_num, ?_⟩
  have : decodeF 0 = (false, 0, 0) := by simp [decodeF]
  rw [this]
  simp [kElt, qNF, eta_zero]

omit hM in
theorem Kgrp_eq_closure :
    Kgrp = Subgroup.closure ({x | ∃ k < 12, x = gE k} ∪ {cE} : Set J) := by
  rw [Kgrp, Qgrp, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]

theorem cE_inv_eq : cE⁻¹ = cE ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact cE_pow_three hM)

theorem Mx_cE_inv : Mx cE⁻¹ = rowsMatrix cMat2 := by
  rw [cE_inv_eq hM, map_pow, pow_two, Mx_cE hM, cMat2, cTab, rowsMatrix_mulT_frTable]

theorem Kgrp_le_Sform : ∀ y ∈ Kgrp, y ∈ Sform := by
  intro y hy
  rw [Kgrp_eq_closure] at hy
  induction hy using Subgroup.closure_induction_left with
  | one => exact one_mem_Sform hM
  | mul_left x hx y _ ih =>
    obtain ⟨n, hn, rfl⟩ := ih
    rcases hx with ⟨k, hk, rfl⟩ | hx
    · exact mul_mem_Sform hM (Mx_q hM hk) ((chkClosure_parts hn).1 k hk).1 hn
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mul_mem_Sform hM (Mx_cE hM) (chkClosure_parts hn).2.1 hn
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨n, hn, rfl⟩ := ih
    rcases hx with ⟨k, hk, rfl⟩ | hx
    · exact mul_mem_Sform hM (Mx_inv_q hM hk) ((chkClosure_parts hn).1 k hk).2 hn
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mul_mem_Sform hM (Mx_cE_inv hM) (chkClosure_parts hn).2.2 hn

omit hM in
theorem k3F_bounds : ∀ f ∈ k3F, f.2.1 < 4096 ∧ f.2.2 < 3 := by decide

theorem kTab_codeF {e : Bool} {c i : ℕ} (hc : c < 4096) (hi : i < 3) :
    Mx (kElt (e, c, i)) = rowsMatrix kTab[codeF (e, c, i)]! := by
  rw [kTab_getElem (codeF_lt e hc hi), decodeF_codeF e hc hi, Mx_kElt hM]

theorem conj_mem_of_normK3 {g : J} {M Mi : Array V2} (hg : Mx g = rowsMatrix M)
    (hgi : Mx g⁻¹ = rowsMatrix Mi) (h : normK3 M Mi = true) :
    ∀ x ∈ K3set, g * x * g⁻¹ ∈ K3set := by
  rintro x ⟨⟨e', c', i'⟩, hf', rfl⟩
  have b := k3F_bounds _ hf'
  unfold normK3 at h
  dsimp only at h
  rw [List.all_eq_true] at h
  have h1 := h (frTable kTab[codeF (e', c', i')]!) (by
    unfold k3Tabs k3Mats
    exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨_, hf', rfl⟩, rfl⟩)
  unfold inK3 at h1
  rw [List.any_eq_true] at h1
  obtain ⟨Y, hY, hYe⟩ := h1
  unfold k3Mats at hY
  obtain ⟨⟨e'', c'', i''⟩, hf'', rfl⟩ := List.mem_map.1 hY
  have b'' := k3F_bounds _ hf''
  refine ⟨_, hf'', Mx_injective ?_⟩
  have h3 := congrArg rowsMatrix (eqRows_iff.1 hYe)
  rw [rowsMatrix_mulT_frTable, rowsMatrix_mulT_frTable, ← hg, ← hgi,
    ← kTab_codeF hM b.1 b.2] at h3
  rw [map_mul, map_mul, h3, kTab_codeF hM b''.1 b''.2]

theorem normK3_of_conj_mem {g : J} {M Mi : Array V2}
    (hg : Mx g = rowsMatrix M) (hgi : Mx g⁻¹ = rowsMatrix Mi) (hwf : wfR M = true)
    (hwfi : wfR Mi = true) (h : ∀ x ∈ K3set, g * x * g⁻¹ ∈ K3set) : normK3 M Mi = true := by
  unfold normK3
  dsimp only
  rw [List.all_eq_true]
  intro TX hTX
  unfold k3Tabs k3Mats at hTX
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hTX
  obtain ⟨⟨e', c', i'⟩, hf', rfl⟩ := List.mem_map.1 hX
  have b := k3F_bounds _ hf'
  obtain ⟨⟨e'', c'', i''⟩, hf'', hconj⟩ := h (kElt (e', c', i')) ⟨_, hf', rfl⟩
  have b'' := k3F_bounds _ hf''
  unfold inK3
  rw [List.any_eq_true]
  refine ⟨kTab[codeF (e'', c'', i'')]!, List.mem_map.2 ⟨_, hf'', rfl⟩, ?_⟩
  apply eqRows_iff.2
  have hw1 : wfR kTab[codeF (e', c', i')]! = true := kTab_wfR (codeF_lt e' b.1 b.2)
  have hw2 : wfR kTab[codeF (e'', c'', i'')]! = true := kTab_wfR (codeF_lt e'' b''.1 b''.2)
  apply eq_of_rowsMatrix_eq' _ hw2
  · rw [rowsMatrix_mulT_frTable, rowsMatrix_mulT_frTable, ← hg, ← hgi,
      ← kTab_codeF hM b.1 b.2, ← map_mul, ← map_mul, hconj, kTab_codeF hM b''.1 b''.2]
  · exact wfR_mulRows (wfR_mulRows hwf hw1) hwfi

theorem K3set_normalizer :
    ∀ k ∈ Kgrp, (∀ x ∈ K3set, k * x * k⁻¹ ∈ K3set) → k ∈ K3set := by
  intro k hk hnorm
  obtain ⟨n, hn, rfl⟩ := Kgrp_le_Sform hM k hk
  have h := chkNorm_true
  unfold chkNorm at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at h
  have h1 := h n hn
  obtain ⟨⟨hwfi, hinv⟩, hor⟩ := h1
  have hg : Mx (kElt (decodeF n)) = rowsMatrix kTab[n]! := by
    rw [Mx_kElt hM, kTab_getElem hn]
  have hgi := rowsMatrix_inv_of_mul hg hinv
  have hN : normK3 kTab[n]! (invRows kTab[n]!) = true :=
    normK3_of_conj_mem hM hg hgi (kTab_wfR hn) hwfi hnorm
  rcases hor with h2 | h2
  · rw [hN] at h2
    exact absurd h2 (by simp)
  · exact ⟨decodeF n, h2, rfl⟩

theorem Mx_mElt : Mx mElt = rowsMatrix mRows := by
  have g : ∀ n < 32, Mx (gE n) = rowsMatrix gmats[n]! := fun n hn => Mx_gE hM hn
  simp only [mElt, mRows, List.foldl_cons, List.foldl_nil, map_mul]
  rw [rowsMatrix_mulT_gtabs _ (by norm_num : 11 < 32), rowsMatrix_mulT_gtabs _ (by norm_num : 9 < 32),
    rowsMatrix_mulT_gtabs _ (by norm_num : 7 < 32), rowsMatrix_mulT_gtabs _ (by norm_num : 1 < 32),
    rowsMatrix_mulT_gtabs _ (by norm_num : 29 < 32), rowsMatrix_mulT_gtabs _ (by norm_num : 15 < 32),
    rowsMatrix_idRows, one_mul, g 15 (by norm_num), g 29 (by norm_num), g 1 (by norm_num),
    g 7 (by norm_num), g 9 (by norm_num), g 11 (by norm_num)]

omit hM in
theorem chkM_parts :
    wfR mRows = true ∧ wfR (invRows mRows) = true ∧
      eqRows (mulT mRows (frTable (invRows mRows))) idRows = true ∧
      normK3 mRows (invRows mRows) = true ∧ normK3 (invRows mRows) mRows = true := by
  have h := chkM_true
  unfold chkM at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem mElt_conj_K3set :
    ∀ x ∈ K3set, mElt * x * mElt⁻¹ ∈ K3set := by
  obtain ⟨-, -, h3, h4, -⟩ := chkM_parts
  exact conj_mem_of_normK3 hM (Mx_mElt hM) (rowsMatrix_inv_of_mul (Mx_mElt hM) h3) h4

end Mats

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck
