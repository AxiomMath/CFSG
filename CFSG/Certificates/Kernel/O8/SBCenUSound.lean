module

public import Certificates.Data.Kernel.O8.SBCenU
public import CFSG.Certificates.Kernel.O8.SBCenLSound

public section

namespace CFSG.KC.SBCenU

open CFSG.KC.Enum CFSG.KC.SB CFSG.KC.SBCen CFSG.KC.SBCenL CFSG.KC.AxisPlane
  CFSG.EvenSmallLie.OmegaEight.SpBranch

section Grp

variable (AR MR : ℕ → ℕ) {mul : ℕ → ℕ → ℕ} (F : ℕ → ℕ) (z : ℕ)
  (hmul : ∀ c d, c < 65536 → d < 65536 → mul c d = sMulG AR MR c d)
  (hF : ∀ a < 65536, F a < 65536) (hz : z < 65536)

include hmul in
theorem mul_lt {c d : ℕ} (hc : c < 65536) (hd : d < 65536) : mul c d < 65536 := by
  obtain ⟨hcs, hce, hcg⟩ := code_split hc
  obtain ⟨hds, hde, hdg⟩ := code_split hd
  rw [hmul c d hc hd, hcs, hds, sMulG_eq AR MR hce hcg hde hdg]
  have h1 := xor_lt hce (ln_lt (AR (c >>> 7)) (7 * (d &&& 127)))
  have h2 := mt_lt MR (c >>> 7) (d >>> 7)
  omega

theorem ext_uu (e g : ℕ) :
    extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)) =
      mul (mul (e + 128 * g) (F (e + 128 * g))) z := by
  have h1 : ¬ e + 128 * (g + 512) < 65536 := by omega
  have h2 : e + 128 * (g + 512) - 65536 = e + 128 * g := by omega
  rw [extMulF_eq]
  unfold extMul
  rw [if_neg h1, if_neg h1, h2]

theorem ext_ul {e g q : ℕ} (hq : q < 65536) :
    extMulF 65536 mul F z (e + 128 * (g + 512)) q = mul (e + 128 * g) (F q) + 65536 := by
  have h1 : ¬ e + 128 * (g + 512) < 65536 := by omega
  have h2 : e + 128 * (g + 512) - 65536 = e + 128 * g := by omega
  rw [extMulF_eq]
  unfold extMul
  rw [if_neg h1, if_pos hq, h2]

theorem ext_lu {e g q : ℕ} (hq : q < 65536) :
    extMulF 65536 mul F z q (e + 128 * (g + 512)) = mul q (e + 128 * g) + 65536 := by
  have h1 : ¬ e + 128 * (g + 512) < 65536 := by omega
  have h2 : e + 128 * (g + 512) - 65536 = e + 128 * g := by omega
  rw [extMulF_eq]
  unfold extMul
  rw [if_pos hq, if_neg h1, h2]

include hmul hF in
theorem lowCntV_eq {g q : ℕ} (hg : g < 512) (hq : q < 65536) (p : ℕ → Bool) :
    lowCntV AR MR (AR g) (MR g) g (flg p) q (F q) =
      ∑ e ∈ Finset.range 128, if (p e && decide (extMulF 65536 mul F z (e + 128 * (g + 512)) q =
        extMulF 65536 mul F z q (e + 128 * (g + 512)))) = true then 1 else 0 := by
  have hv := hF q hq
  obtain ⟨hqs, he', hh⟩ := code_split hq
  obtain ⟨hvs, hve, hvg⟩ := code_split hv
  have hc : ∀ e, (extMulF 65536 mul F z (e + 128 * (g + 512)) q =
      extMulF 65536 mul F z q (e + 128 * (g + 512))) ↔ mul (e + 128 * g) (F q) = mul q (e + 128 * g) := by
    intro e
    rw [ext_ul F z hq, ext_lu F z hq]
    omega
  simp only [hc]
  unfold lowCntV
  simp only [cen_strictN, cen_nIf, cen_beq, decide_eq_true_eq, nl_and, nl_shr, nl_xor, Nat.mul_eq]
  generalize F q = v at hvs hve hvg ⊢
  generalize q &&& 127 = e' at hqs he' ⊢
  generalize q >>> 7 = h at hqs hh ⊢
  generalize v &&& 127 = ve at hvs hve ⊢
  generalize v >>> 7 = vg at hvs hvg ⊢
  subst hqs hvs
  by_cases hm : (MR g >>> (9 * vg)) &&& 511 = (MR h >>> (9 * g)) &&& 511
  · rw [if_pos hm, zl_eq, flg_and, pop_eq]
    refine Finset.sum_congr rfl fun e he => ?_
    have he := Finset.mem_range.1 he
    simp only [ln_xor]
    rw [ln_IDX he, ln_RU (xor_lt he' (ln_lt _ _)) he, mul_code AR MR hmul he hg hve hvg,
      mul_code AR MR hmul he' hh he hg, hm, xor4]
    simp only [code_eq (xor_lt he (ln_lt _ _)) (xor_lt he' (ln_lt _ _))]
    by_cases hx : e ^^^ ((AR g >>> (7 * ve)) &&& 127) = e' ^^^ ((AR h >>> (7 * e)) &&& 127) <;>
      simp [hx, xor_eq_zero]
  · rw [if_neg hm]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have he := Finset.mem_range.1 he
    rw [mul_code AR MR hmul he hg hve hvg, mul_code AR MR hmul he' hh he hg]
    simp only [code_eq (xor_lt he (ln_lt _ _)) (xor_lt he' (ln_lt _ _))]
    simp [hm]

include hmul hF in
theorem qWalkU_eq {g : ℕ} (hg : g < 512) (p : ℕ → Bool) : ∀ Q : List ℕ,
    qWalkU AR MR F (AR g) (MR g) g (flg p) Q +
        ∑ e ∈ Finset.range 128,
          (if p e = true then cmU (extMulF 65536 mul F z) (e + 128 * (g + 512)) Q else 0) =
      ∑ e ∈ Finset.range 128,
        (if p e = true then cmL (extMulF 65536 mul F z) (e + 128 * (g + 512)) Q else 0)
  | [] => by
    have e1 : ∀ c, cmU (extMulF 65536 mul F z) c [] = 0 := fun _ => rfl
    have e2 : ∀ c, cmL (extMulF 65536 mul F z) c [] = 0 := fun _ => rfl
    change (0 : ℕ) + _ = _
    simp [e1, e2]
  | q :: Q => by
    have ih := qWalkU_eq hg p Q
    have e1 : qWalkU AR MR F (AR g) (MR g) g (flg p) (q :: Q) =
        Nat.add (Bool.rec (motive := fun _ => ℕ) 0 (lowCntV AR MR (AR g) (MR g) g (flg p) q (F q))
          (Nat.blt q 65536)) (Nat.shiftLeft (qWalkU AR MR F (AR g) (MR g) g (flg p) Q) 20) := rfl
    have e2 : ∀ c, cmU (extMulF 65536 mul F z) c (q :: Q) = Nat.add (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) 0 1
          (Nat.beq (extMulF 65536 mul F z c q) (extMulF 65536 mul F z q c))) 0 (Nat.blt q 65536))
        (Nat.shiftLeft (cmU (extMulF 65536 mul F z) c Q) 20) := fun _ => rfl
    have e3 : ∀ c, cmL (extMulF 65536 mul F z) c (q :: Q) = Nat.add
        (Bool.rec (motive := fun _ => ℕ) 0 1
          (Nat.beq (extMulF 65536 mul F z c q) (extMulF 65536 mul F z q c)))
        (Nat.shiftLeft (cmL (extMulF 65536 mul F z) c Q) 20) := fun _ => rfl
    rw [e1]
    simp only [e2, e3, cen_nIf, cen_blt, cen_beq, cen_shl, Nat.add_eq, decide_eq_true_eq]
    rw [sum_ite_add, sum_ite_add, ← ih]
    by_cases hq : q < 65536
    · simp only [hq, ↓reduceIte]
      rw [lowCntV_eq AR MR F z hmul hF hg hq p]
      have h0 : ∑ e ∈ Finset.range 128, (if p e = true then (0 : ℕ) else 0) = 0 := by simp
      rw [h0]
      have h1 : ∑ e ∈ Finset.range 128,
          (if (p e && decide (extMulF 65536 mul F z (e + 128 * (g + 512)) q =
            extMulF 65536 mul F z q (e + 128 * (g + 512)))) = true then 1 else 0) =
          ∑ e ∈ Finset.range 128, (if p e = true then
            (if extMulF 65536 mul F z (e + 128 * (g + 512)) q =
              extMulF 65536 mul F z q (e + 128 * (g + 512)) then 1 else 0) else 0) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [ite_and_one]
        simp
      rw [h1]
      ring
    · simp only [hq, ↓reduceIte]
      ring

include hmul hF in
theorem uWalkU_eq {g : ℕ} (hg : g < 512) (p : ℕ → Bool) : ∀ U : List ℕ, (∀ u ∈ U, u < 65536) →
    uWalkU AR MR F (AR g) (MR g) g (flg p) U =
      ∑ e ∈ Finset.range 128,
        (if p e = true then cmL (extMulF 65536 mul F z) (e + 128 * (g + 512)) U else 0)
  | [], _ => by
    have e2 : ∀ c, cmL (extMulF 65536 mul F z) c [] = 0 := fun _ => rfl
    change (0 : ℕ) = _
    simp [e2]
  | u :: U, hU => by
    have ih := uWalkU_eq hg p U fun v hv => hU v (List.mem_cons_of_mem u hv)
    have e1 : uWalkU AR MR F (AR g) (MR g) g (flg p) (u :: U) =
        Nat.add (lowCntV AR MR (AR g) (MR g) g (flg p) u (F u))
          (Nat.shiftLeft (uWalkU AR MR F (AR g) (MR g) g (flg p) U) 20) := rfl
    have e3 : ∀ c, cmL (extMulF 65536 mul F z) c (u :: U) = Nat.add
        (Bool.rec (motive := fun _ => ℕ) 0 1
          (Nat.beq (extMulF 65536 mul F z c u) (extMulF 65536 mul F z u c)))
        (Nat.shiftLeft (cmL (extMulF 65536 mul F z) c U) 20) := fun _ => rfl
    rw [e1, lowCntV_eq AR MR F z hmul hF hg (hU u (List.mem_cons_self ..)) p, ih]
    simp only [e3, cen_nIf, cen_beq, cen_shl, Nat.add_eq, decide_eq_true_eq]
    rw [sum_ite_add]
    have h1 : (∑ e ∈ Finset.range 128,
        if (p e && decide (extMulF 65536 mul F z (e + 128 * (g + 512)) u =
          extMulF 65536 mul F z u (e + 128 * (g + 512)))) = true then 1 else 0) =
        ∑ e ∈ Finset.range 128, (if p e = true then
          (if extMulF 65536 mul F z (e + 128 * (g + 512)) u =
            extMulF 65536 mul F z u (e + 128 * (g + 512)) then 1 else 0) else 0) :=
      Finset.sum_congr rfl fun e _ => by
        rw [ite_and_one]
        simp
    rw [h1]

include hmul hF hz in
theorem zIU_eq (g : ℕ) (hg : g < 512) :
    lanesK (fun e => strictN (Nat.add e (Nat.mul 128 g)) fun a => strictN (F a) fun u =>
      strictN (mul (mul a u) z) fun s => nIf(Nat.beq s 0, 64, 0)) 128 =
    flg fun e => decide (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)) = 0 ∧
      e + 128 * (g + 512) ≠ 0) := by
  rw [lanesK_eq]
  unfold flg
  refine congrArg (fun f => lanes 7 f 128) (funext fun e => ?_)
  simp only [cen_strictN, cen_nIf, cen_beq, Nat.add_eq, Nat.mul_eq, ext_uu (mul := mul) F z e g]
  have : e + 128 * (g + 512) ≠ 0 := by omega
  simp [this]

include hmul hF hz in
theorem zOU_eq (g : ℕ) (hg : g < 512) :
    lanesK (fun e => strictN (Nat.add e (Nat.mul 128 g)) fun a => strictN (F a) fun u =>
      strictN (mul (mul a u) z) fun s => nIf(Nat.beq s 0, 0, nIf(Nat.beq (mul s s) 0, 64, 0))) 128 =
    flg fun e => decide (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)) ≠ 0 ∧
      extMulF 65536 mul F z (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)))
        (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512))) = 0) := by
  rw [lanesK_eq]
  have e1 : (fun e => strictN (Nat.add e (Nat.mul 128 g)) fun a => strictN (F a) fun u =>
      strictN (mul (mul a u) z) fun s => nIf(Nat.beq s 0, 0, nIf(Nat.beq (mul s s) 0, 64, 0))) =
      fun e => if decide (mul (mul (e + 128 * g) (F (e + 128 * g))) z ≠ 0 ∧
        mul (mul (mul (e + 128 * g) (F (e + 128 * g))) z) (mul (mul (e + 128 * g) (F (e + 128 * g))) z) = 0)
          = true then 64 else 0 := by
    funext e
    simp only [cen_strictN, cen_nIf, cen_beq, Nat.add_eq, Nat.mul_eq]
    by_cases h0 : mul (mul (e + 128 * g) (F (e + 128 * g))) z = 0 <;> simp [h0]
  rw [e1]
  change flg _ = flg _
  apply flg_congr
  intro e he
  rw [ext_uu (mul := mul) F z e g]
  have ha : e + 128 * g < 65536 := by omega
  have hs := mul_lt AR MR hmul (mul_lt AR MR hmul ha (hF _ ha)) hz
  have hss : extMulF 65536 mul F z (mul (mul (e + 128 * g) (F (e + 128 * g))) z)
      (mul (mul (e + 128 * g) (F (e + 128 * g))) z) =
      mul (mul (mul (e + 128 * g) (F (e + 128 * g))) z) (mul (mul (e + 128 * g) (F (e + 128 * g))) z) := by
    rw [extMulF_eq]
    unfold extMul
    rw [if_pos hs, if_pos hs]
  rw [hss]

include hmul hF hz in
theorem grpU_eq {g : ℕ} (hg : g < 512) {Q U : List ℕ} (hU : ∀ u ∈ U, u < 65536) (nQ : ℕ) :
    grpU mul AR MR F z Q U nQ g =
      ∑ e ∈ Finset.range 128, cen (extMulF 65536 mul F z) Q U nQ (e + 128 * (g + 512)) := by
  unfold grpU
  rw [zIU_eq AR MR F z hmul hF hz g hg, zOU_eq AR MR F z hmul hF hz g hg]
  simp only [cen_strictN]
  simp only [Nat.add_eq, cen_shl, Nat.mul_eq, Nat.succ_eq_add_one]
  have hq := qWalkU_eq AR MR F z hmul hF hg (fun e => decide
    (extMulF 65536 mul F z (e + 128 * (g + 512)) (e + 128 * (g + 512)) = 0 ∧ e + 128 * (g + 512) ≠ 0)) Q
  rw [pop_eq, cuSum_eq, uWalkU_eq AR MR F z hmul hF hg _ U hU]
  simp only [cen_split, Finset.sum_add_distrib]
  set M := extMulF 65536 mul F z
  have hA : ∑ e ∈ Finset.range 128, (if M (e + 128 * (g + 512)) (e + 128 * (g + 512)) = 0 ∧
        e + 128 * (g + 512) ≠ 0 then 1 + cmL M (e + 128 * (g + 512)) Q * 2 ^ 20 else 0) =
      ∑ e ∈ Finset.range 128, (if decide (M (e + 128 * (g + 512)) (e + 128 * (g + 512)) = 0 ∧
        e + 128 * (g + 512) ≠ 0) = true then 1 else 0) +
      (∑ e ∈ Finset.range 128, (if decide (M (e + 128 * (g + 512)) (e + 128 * (g + 512)) = 0 ∧
        e + 128 * (g + 512) ≠ 0) = true then cmL M (e + 128 * (g + 512)) Q else 0)) * 2 ^ 20 := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [decide_eq_true_eq]
    split_ifs <;> ring
  have hB : ∑ e ∈ Finset.range 128, (if M (e + 128 * (g + 512)) (e + 128 * (g + 512)) ≠ 0 ∧
        M (M (e + 128 * (g + 512)) (e + 128 * (g + 512))) (M (e + 128 * (g + 512)) (e + 128 * (g + 512))) = 0
        then cmL M (e + 128 * (g + 512)) U * 2 ^ (20 * (nQ + 1)) else 0) =
      (∑ e ∈ Finset.range 128, (if decide (M (e + 128 * (g + 512)) (e + 128 * (g + 512)) ≠ 0 ∧
        M (M (e + 128 * (g + 512)) (e + 128 * (g + 512))) (M (e + 128 * (g + 512)) (e + 128 * (g + 512))) = 0)
        = true then cmL M (e + 128 * (g + 512)) U else 0)) * 2 ^ (20 * (nQ + 1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [decide_eq_true_eq]
    split_ifs <;> ring
  rw [hA, hB, ← hq]
  ring

end Grp

theorem blkU_eq {AR MR : ℕ → ℕ} {mul : ℕ → ℕ → ℕ} {F : ℕ → ℕ} {z : ℕ}
    (hmul : ∀ c d, c < 65536 → d < 65536 → mul c d = sMulG AR MR c d)
    (hF : ∀ a < 65536, F a < 65536) (hz : z < 65536)
    {Q U : List ℕ} (hU : ∀ u ∈ U, u < 65536) (nQ : ℕ) {t : ℕ} (ht : t < 8) :
    blkU mul AR MR F z Q U nQ t = cenBlk (extMulF 65536 mul F z) Q U nQ (8192 * (t + 8)) := by
  unfold blkU
  rw [natRec_sum, cenBlk, sumBelow_list _ (by norm_num : 8192 ≤ 64 * 128),
    show (8192 : ℕ) = 128 * 64 from rfl, sum_blocks _ 128 64]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj := List.mem_range.1 hj
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [grpU_eq AR MR F z hmul hF hz (by omega) hU, lsum_eq]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  ring

theorem conjB_sound {mul : ℕ → ℕ → ℕ} {F : ℕ → ℕ} {z a n : ℕ} (h : conjB mul F z a n = true) :
    ∀ i < n, mul z (a + i) = mul (F (F (a + i))) z := by
  intro i hi
  have := @recAnd (fun i => strictB (Nat.add a i) fun y => strictB (F y) fun u => strictB (F u) fun v =>
    Nat.beq (mul z y) (mul v z)) n h i hi
  simp only [cen_strictB, Nat.add_eq] at this
  exact Nat.eq_of_beq_eq_true this

end CFSG.KC.SBCenU

end
