module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth21Root
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.InvolutionsN1
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.OddSquareCert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open MulOpposite Subgroup CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.GSide CFSG.Monster.B.CTIB
open CFSG.Monster.B.CTIB.Native (qmul gArr autApply autComp autPow id23 qinv wordAut genInvImgs)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem pow_succ_pow_eq_one {G : Type*} [Group G] {g : G} {m : ℕ} (hm : Odd m)
    (h : g ^ (2 * m) = 1) : (g ^ (m + 1)) ^ m = 1 := by
  obtain ⟨k, rfl⟩ := hm
  have e : (g ^ (2 * k + 1 + 1)) ^ (2 * k + 1) = (g ^ (2 * (2 * k + 1))) ^ (k + 1) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [e, h, one_pow]

@[expose] def HasImgs
    (g : Sbp) (A : Array ℕ) : Prop :=
  g.unop ∈ Jbar ∧ A.size = 22 ∧ ∀ i < 22, g⁻¹ * es i * g = qS (A.getD i 0)

theorem HasImgs.conj
    {g : Sbp} {A : Array ℕ} (h : HasImgs g A) (n : ℕ) :
    g⁻¹ * qS n * g = qS (autApply gArr A n) :=
  conj_qS h.1 h.2.2 n

theorem HasImgs.mul
    {g h : Sbp} {A B : Array ℕ} (hg : HasImgs g A) (hh : HasImgs h B) :
    HasImgs (g * h) (autComp gArr A B) := by
  refine ⟨?_, by rw [autComp_size, hg.2.1], fun i hi => ?_⟩
  · rw [unop_mul]
    exact Jbar.mul_mem hh.1 hg.1
  · rw [autComp_getD (by rw [hg.2.1]; exact hi), ← hh.conj, ← hg.2.2 i hi]
    group

theorem HasImgs.pow
    {g : Sbp} {A : Array ℕ} (hg : HasImgs g A) (m : ℕ) :
    HasImgs (g ^ m) (autPow gArr A m) := by
  obtain ⟨h1, h2⟩ := conj_pow hg.1 hg.2.1 hg.2.2 m
  refine ⟨?_, h2, h1⟩
  rw [unop_pow]
  exact Jbar.pow_mem hg.1 m

theorem hasImgs_wordS'
    {w : List ℤ} (hw : ∀ l ∈ w, IsLetter2 l) :
    HasImgs (wordS' w) (wordAut (genInvImgs ()) w) := by
  obtain ⟨h1, h2, h3⟩ := conj_wordS' hw
  exact ⟨h3, h2, h1⟩

theorem eq_one_or_xs_of_hasImgs
    {c : Sbp} (h : HasImgs c id23) : c = 1 ∨ c = xs := by
  have hc : ∀ i < 22, c⁻¹ * es i * c = es i := fun i hi => by
    rw [h.2.2 i hi, id23_getD hi, qS_two_pow hi]
  have hle : Subgroup.closure (es '' {m | m < 22}) ≤ Subgroup.centralizer {c} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc es m * c = c * (c⁻¹ * es m * c) := by group
      _ = c * es m := by rw [hc m hm]
  have hz : c.unop ∈ Subgroup.zpowers xbar := by
    rw [← centralizer_Ebar]
    refine ⟨h.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : op y ∈ Subgroup.centralizer {c} := hle (by rw [closure_es]; exact hy)
    have e := congrArg unop (Subgroup.mem_centralizer_singleton_iff.1 hy')
    rw [unop_mul, unop_mul, unop_op] at e
    exact e.symm
  rcases (Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_xbar).1 hz with h1 | h1
  · exact .inl (unop_injective h1)
  · exact .inr (unop_injective h1)

theorem innerImgs_size (d : ℕ) : (innerImgs d).size = 22 := by simp [innerImgs]

theorem innerImgs_getD (d : ℕ) {i : ℕ} (hi : i < 22) :
    (innerImgs d).getD i 0 = qmul gArr (qmul gArr (qinv d) (2 ^ i)) d := by
  rw [innerImgs, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem hasImgs_qS
    (d : ℕ) : HasImgs (qS d) (innerImgs d) := by
  refine ⟨Ebar_le_Jbar (qS_mem d), innerImgs_size d, fun i hi => ?_⟩
  rw [innerImgs_getD d hi, ← qS_mul, ← qS_mul, qS_qinv, qS_two_pow hi]

theorem eq_or_eq_mul_xs_of_hasImgs
    {g : Sbp} {d : ℕ} (h : HasImgs g (innerImgs d)) :
    g = qS d ∨ g = qS d * xs := by
  have ht : HasImgs (g * (qS d)⁻¹) id23 := by
    refine ⟨?_, by simp [id23], fun i hi => ?_⟩
    · rw [unop_mul, unop_inv]
      exact Jbar.mul_mem (Jbar.inv_mem (Ebar_le_Jbar (qS_mem d))) h.1
    · have h1 := h.2.2 i hi
      have h2 := (hasImgs_qS d).2.2 i hi
      rw [id23_getD hi, qS_two_pow hi]
      calc (g * (qS d)⁻¹)⁻¹ * es i * (g * (qS d)⁻¹) = qS d * (g⁻¹ * es i * g) * (qS d)⁻¹ := by
            group
        _ = qS d * ((qS d)⁻¹ * es i * qS d) * (qS d)⁻¹ := by rw [h1, ← h2]
        _ = es i := by group
  rcases eq_one_or_xs_of_hasImgs ht with h1 | h1
  · exact .inl (mul_inv_eq_one.1 h1)
  · refine .inr ?_
    rw [mul_inv_eq_iff_eq_mul] at h1
    rw [h1, xs_comm (qS_mem d)]

theorem pow_eq_one_of_hasImgs
    {g : Sbp} {A : Array ℕ} (hg : HasImgs g A) {m : ℕ} (hm : Odd m)
    (hA : autPow gArr A m = id23) : (g ^ (m + 1)) ^ m = 1 := by
  have h := hg.pow m
  rw [hA] at h
  have h2 : g ^ (2 * m) = 1 := by
    rcases eq_one_or_xs_of_hasImgs h with h1 | h1
    · rw [mul_comm, pow_mul, h1, one_pow]
    · rw [mul_comm, pow_mul, h1, sq, xs_mul_self]
  exact pow_succ_pow_eq_one hm h2

@[expose] def OddAt
    (c y : Sbp) : Prop :=
  ∃ h₁ h₂ : Sbp, h₁ * c = c * h₁ ∧ h₂ * c = c * h₂ ∧ h₁ * y = y * h₁ ∧ h₂ * y = y * h₂ ∧
    Odd (orderOf h₁) ∧ Odd (orderOf h₂) ∧ h₁ * h₂ * (h₁ * h₂) = y

theorem conj_inv_comm {M : Type*} [Group M] {a b : M} (g : M) (h : a * b = b * a) :
    g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * b * g * (g⁻¹ * a * g) := by
  calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
    _ = g⁻¹ * (b * a) * g := by rw [h]
    _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group

theorem orderOf_inv_mul_mul_eq {M : Type*} [Group M] (g a : M) :
    orderOf (g⁻¹ * a * g) = orderOf a := by
  rw [show g⁻¹ * a * g = MulAut.conj g⁻¹ a by simp, MulEquiv.orderOf_eq]

theorem orderOf_mul_mul_inv_eq {M : Type*} [Group M] (g a : M) :
    orderOf (g * a * g⁻¹) = orderOf a := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem OddAt.of_conj
    {c y c₀ y₀ g : Sbp} (h : OddAt c₀ y₀) (hc : g * c * g⁻¹ = c₀)
    (hy : g * y * g⁻¹ = y₀) : OddAt c y := by
  obtain ⟨h₁, h₂, h1c, h2c, h1y, h2y, o1, o2, hs⟩ := h
  obtain rfl : c = g⁻¹ * c₀ * g := by rw [← hc]; group
  obtain rfl : y = g⁻¹ * y₀ * g := by rw [← hy]; group
  refine ⟨g⁻¹ * h₁ * g, g⁻¹ * h₂ * g, conj_inv_comm g h1c, conj_inv_comm g h2c,
    conj_inv_comm g h1y, conj_inv_comm g h2y, by rwa [orderOf_inv_mul_mul_eq],
    by rwa [orderOf_inv_mul_mul_eq], ?_⟩
  rw [← hs]
  group

theorem isLetter2_of_isLetterB {l : ℤ} (h : isLetterB l = true) : IsLetter2 l := by
  simpa [isLetterB, IsLetter2, or_assoc] using h

theorem HasImgs.commute
    {g : Sbp} {A : Array ℕ} (hg : HasImgs g A) {c : ℕ}
    (h : autApply gArr A c = c) : Commute g (qS c) := by
  have e := hg.conj c
  rw [h] at e
  show g * qS c = qS c * g
  calc g * qS c = g * (g⁻¹ * qS c * g) := by rw [e]
    _ = qS c * g := by group

theorem HasImgs.commute_xs
    {g : Sbp} {A : Array ℕ} (hg : HasImgs g A) : Commute g xs := by
  have e := conj_xs hg.1
  show g * xs = xs * g
  calc g * xs = g * (g⁻¹ * xs * g) := by rw [e]
    _ = xs * g := by group

theorem oddAt_of_oddWitOK
    {c y : ℕ} {wa wb : List ℤ} {ea ma eb mb n e : ℕ}
    (h : oddWitOK c y wa ea ma wb eb mb n e = true) : OddAt (qS c) (qS y) := by
  simp only [oddWitOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwa, hwb⟩, hma⟩, hmb⟩, hAm⟩, hBm⟩, hAc⟩, hAy⟩, hBc⟩, hBy⟩, hnc⟩, hny⟩,
    hS⟩, hec⟩, hey⟩ := h
  have hma' : Odd ma := Nat.odd_iff.2 hma
  have hmb' : Odd mb := Nat.odd_iff.2 hmb
  have hWa := hasImgs_wordS' fun l hl => isLetter2_of_isLetterB (hwa l hl)
  have hWb := hasImgs_wordS' fun l hl => isLetter2_of_isLetterB (hwb l hl)
  set ga := wordS' wa ^ ea with hga
  set gb := wordS' wb ^ eb with hgb
  have hGa := hWa.pow ea
  have hGb := hWb.pow eb
  set a := ga ^ (ma + 1) with ha
  set b := gb ^ (mb + 1) with hb
  have hA := hGa.pow (ma + 1)
  have hB := hGb.pow (mb + 1)
  have ha1 : a ^ ma = 1 := pow_eq_one_of_hasImgs hGa hma' hAm
  have hb1 : b ^ mb = 1 := pow_eq_one_of_hasImgs hGb hmb' hBm
  have hao : Odd (orderOf a) := Odd.of_dvd_nat hma' (orderOf_dvd_of_pow_eq_one ha1)
  have hbo : Odd (orderOf b) := Odd.of_dvd_nat hmb' (orderOf_dvd_of_pow_eq_one hb1)
  have hai : a⁻¹ = a ^ (ma - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hma'.pos, ha1]
  have hAi : HasImgs a⁻¹ (autPow gArr (autPow gArr (autPow gArr
      (wordAut (genInvImgs ()) wa) ea) (ma + 1)) (ma - 1)) := by
    rw [hai]; exact hA.pow (ma - 1)
  have caC : Commute a (qS c) := ((hWa.commute hAc).pow_left ea).pow_left (ma + 1)
  have caY : Commute a (qS y) := ((hWa.commute hAy).pow_left ea).pow_left (ma + 1)
  have cbC : Commute b (qS c) := ((hWb.commute hBc).pow_left eb).pow_left (mb + 1)
  have cbY : Commute b (qS y) := ((hWb.commute hBy).pow_left eb).pow_left (mb + 1)
  have cnC : Commute (qS n) (qS c) := qS_comm_of_code hnc
  have cnY : Commute (qS n) (qS y) := qS_comm_of_code hny
  set h₁ := a * b * a⁻¹ with hh₁
  set h₂ := qS n * a * (qS n)⁻¹ with hh₂
  have c1C : Commute h₁ (qS c) := (caC.mul_left cbC).mul_left caC.inv_left
  have c1Y : Commute h₁ (qS y) := (caY.mul_left cbY).mul_left caY.inv_left
  have c2C : Commute h₂ (qS c) := (cnC.mul_left caC).mul_left cnC.inv_left
  have c2Y : Commute h₂ (qS y) := (cnY.mul_left caY).mul_left cnY.inv_left
  have o1 : Odd (orderOf h₁) := by rw [hh₁, orderOf_mul_mul_inv_eq]; exact hbo
  have o2 : Odd (orderOf h₂) := by rw [hh₂, orderOf_mul_mul_inv_eq]; exact hao
  have hs : HasImgs (h₁ * h₂ * (h₁ * h₂)) (innerImgs y) := by
    have e : h₁ * h₂ = a * b * a⁻¹ * qS n * a * qS (qinv n) := by
      rw [hh₁, hh₂, qS_qinv]; group
    rw [e, ← hS]
    exact ((((((hA.mul hB).mul hAi).mul (hasImgs_qS n)).mul hA).mul (hasImgs_qS (qinv n)))).mul
      (((((hA.mul hB).mul hAi).mul (hasImgs_qS n)).mul hA).mul (hasImgs_qS (qinv n)))
  rcases eq_or_eq_mul_xs_of_hasImgs hs with hsq | hsq
  · exact ⟨h₁, h₂, c1C.eq, c2C.eq, c1Y.eq, c2Y.eq, o1, o2, hsq⟩
  ·
    have hxs1 : Commute h₁ xs := by
      rw [hh₁]
      exact (hA.commute_xs.mul_left hB.commute_xs).mul_left hA.commute_xs.inv_left
    have hxs2 : Commute h₂ xs := by
      rw [hh₂]
      exact ((hasImgs_qS n).commute_xs.mul_left hA.commute_xs).mul_left
        (hasImgs_qS n).commute_xs.inv_left
    have h0 : OddAt (qS c) (qS y * xs) :=
      ⟨h₁, h₂, c1C.eq, c2C.eq, (c1Y.mul_right hxs1).eq, (c2Y.mul_right hxs2).eq, o1, o2, hsq⟩
    refine h0.of_conj (g := (qS e)⁻¹) ?_ ?_
    · rw [inv_inv, mul_assoc, ← qS_comm_of_code hec, ← mul_assoc, inv_mul_cancel, one_mul]
    · rw [inv_inv, ← qS_qinv, qS_mul, qS_mul, hey, ← qS_mul, qS_two_pow_22]

theorem oddAt_q1_q6
    : OddAt (qS 1) (qS 6) := oddAt_of_oddWitOK oddWitOK_Y2

theorem oddAt_q1_q7
    : OddAt (qS 1) (qS 7) := oddAt_of_oddWitOK oddWitOK_CY2

theorem oddAt_q32_q7
    : OddAt (qS 32) (qS 7) := oddAt_of_oddWitOK oddWitOK_Y3

theorem frameCodes_parts :
    qmul gArr 1 6 = 7 ∧ qmul gArr 6 1 = 7 ∧ qmul gArr 1 7 = 6 ∧ qmul gArr 7 1 = 6 := by
  have h := frameCodesOK_eq_true
  simp only [frameCodesOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem innerTy_six : innerTy innerTab 6 = 2 := by
  have h := innerRepsOK_eq_true
  simp only [innerRepsOK, Bool.and_eq_true, List.all_cons, List.all_nil, beq_iff_eq,
    Bool.and_true] at h
  exact h.1.1.1.1.2.1.1

theorem qS_six_mul_self
    : qS 6 * qS 6 = 1 :=
  (rank_of_innerTy (k := 2) (by norm_num) innerTy_six (by decide)).1

theorem rank_qS_six
    : ((βr (qS 6)) - 1).rank = 2048 :=
  (rank_of_innerTy (k := 2) (by norm_num) innerTy_six (by decide)).2

theorem qS_one_mul_qS_six
    : qS 1 * qS 6 = qS 7 := by rw [qS_mul, frameCodes_parts.1]

theorem qS_six_mul_qS_one
    : qS 6 * qS 1 = qS 7 := by rw [qS_mul, frameCodes_parts.2.1]

theorem qS_one_mul_qS_seven
    : qS 1 * qS 7 = qS 6 := by rw [qS_mul, frameCodes_parts.2.2.1]

theorem qS_seven_mul_qS_one
    : qS 7 * qS 1 = qS 6 := by rw [qS_mul, frameCodes_parts.2.2.2]

theorem oddAt_of_Y2
    {s : Sbp} (hs2 : s * s = 1) (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2048) (hr' : ((βr (labelS * s)) - 1).rank = 2168) :
    OddAt labelS s := by
  rcases frame_two_B (IsConj.refl labelS) hs2 hr hsc with ⟨h1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hr'] at h1
    exact absurd h1 (by decide)
  · have hcy : qS 6 * qS 1 = qS 1 * qS 6 := by rw [qS_six_mul_qS_one, qS_one_mul_qS_six]
    rcases frame_two_B isConj_qS_one_labelS qS_six_mul_self rank_qS_six hcy with
      ⟨h1, -⟩ | ⟨g', hgc', hgw'⟩
    · rw [qS_one_mul_qS_six, rank_qS_seven] at h1
      exact absurd h1 (by decide)
    · exact oddAt_q1_q6.of_conj (conj_comp hgc hgc') (conj_comp hgw hgw')

theorem oddAt_of_cY2
    {s : Sbp} (hs2 : s * s = 1) (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2168) (hr' : ((βr (labelS * s)) - 1).rank = 2048) :
    OddAt labelS s := by
  have hw2 : labelS * s * (labelS * s) = 1 := mul_self_mul_of_comm labelS_mul_self hs2 hsc
  have hwc : labelS * s * labelS = labelS * (labelS * s) := by rw [mul_assoc, hsc]
  have hls : labelS * (labelS * s) = s := by rw [← mul_assoc, labelS_mul_self, one_mul]
  rcases frame_two_B (IsConj.refl labelS) hw2 hr' hwc with ⟨h1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hls, hr] at h1
    exact absurd h1 (by decide)
  · have hw2' : qS 1 * qS 7 * (qS 1 * qS 7) = 1 := by rw [qS_one_mul_qS_seven, qS_six_mul_self]
    have hwr' : ((βr (qS 1 * qS 7)) - 1).rank = 2048 := by rw [qS_one_mul_qS_seven, rank_qS_six]
    have hcw : qS 1 * qS 7 * qS 1 = qS 1 * (qS 1 * qS 7) := by
      rw [mul_assoc, qS_seven_mul_qS_one, qS_one_mul_qS_seven]
    have hy : qS 1 * (qS 1 * qS 7) = qS 7 := by rw [← mul_assoc, qS_one_mul_self, one_mul]
    rcases frame_two_B isConj_qS_one_labelS hw2' hwr' hcw with ⟨h1, -⟩ | ⟨g', hgc', hgw'⟩
    · rw [hy, rank_qS_seven] at h1
      exact absurd h1 (by decide)
    · have ec := conj_comp hgc hgc'
      have ew := conj_comp hgw hgw'
      refine oddAt_q1_q7.of_conj ec ?_
      have e := conj_mul_of ec ew
      rwa [hls, hy] at e

theorem oddAt_of_mem_aSet
    {c : Sbp} (hc : c ∈ aSet) : OddAt c (qS 7) := by
  obtain ⟨k, hk, rfl⟩ := exists_conj_of_mem_aSet hc
  have hk7 : k * qS 7 = qS 7 * k := (Subgroup.mem_centralizer_singleton_iff.1 hk.1)
  refine oddAt_q32_q7.of_conj (g := k⁻¹) (by group) ?_
  rw [inv_inv, mul_assoc, ← hk7, ← mul_assoc, inv_mul_cancel, one_mul]

theorem oddAt_of_Y3
    {s : Sbp} (hsQ : s ∈ Qs) (hs2 : s * s = 1) (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2168) (hr' : ((βr (labelS * s)) - 1).rank = 2168) :
    OddAt labelS s := by
  obtain ⟨g, hg, hgy⟩ := mem_jClass_seven_of_rank hsQ hs2 hr
  have e7 : g * s * g⁻¹ = qS 7 := by rw [hgy]; group
  have hc' : g * labelS * g⁻¹ ∈ aSet := by
    refine ⟨?_, conj_mem_jClass hg labelS_mem_jClass, ?_, ?_⟩
    · have h := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) labelS_mem
      rwa [inv_inv] at h
    · rw [← e7, conj_mul_conj', conj_mul_conj', hsc]
    · rw [← e7, conj_mul_conj', rank_conj_inv, hr']
  exact (oddAt_of_mem_aSet hc').of_conj rfl e7

theorem isConj_cV0_mul_lamW0H_of_RB
    {s : Sbp} (hs2 : s * s = 1) (hsc : s * labelS = labelS * s)
    (hr : ((βr s) - 1).rank = 2048) (hr' : ((βr (labelS * s)) - 1).rank = 1860) :
    IsConj (cV0 * lamW0H) ⟨sEquiv s, sEquiv_mem_vStab hsc⟩ := by
  have hxc : xs * labelS = labelS * xs := xs_comm labelS_mem_Qs
  rcases frame_two_B (IsConj.refl labelS) hs2 hr hsc with ⟨-, g, hgc, hgw⟩ | ⟨g, hgc, hgw⟩
  · rcases frame_two_B (IsConj.refl labelS) xs_mul_self rank_xs hxc with
      ⟨-, g', hgc', hgw'⟩ | ⟨g', hgc', hgw'⟩
    · have ec := conj_comp hgc hgc'
      have ew := conj_comp hgw hgw'
      have hkc : g'⁻¹ * g * labelS = labelS * (g'⁻¹ * g) := by
        calc g'⁻¹ * g * labelS = g'⁻¹ * g * labelS * (g'⁻¹ * g)⁻¹ * (g'⁻¹ * g) := by group
          _ = labelS * (g'⁻¹ * g) := by rw [ec]
      have hx : (⟨sEquiv xs, sEquiv_mem_vStab hxc⟩ : vStab cv0) = cV0 * lamW0H := by
        apply Subtype.ext
        show sEquiv xs = (cV0 : Shat) * (lamW0H : Shat)
        rw [← sEquiv_labelS_mul_xs, ← sEquiv_labelS_eq_cV0, ← map_mul, ← mul_assoc,
          labelS_mul_self, one_mul]
      rw [← hx]
      refine (isConj_iff.2 ⟨⟨sEquiv (g'⁻¹ * g), sEquiv_mem_vStab hkc⟩, Subtype.ext ?_⟩).symm
      show sEquiv (g'⁻¹ * g) * sEquiv s * (sEquiv (g'⁻¹ * g))⁻¹ = sEquiv xs
      rw [← map_conj_eq, ew]
    · exfalso
      have e := conj_mul_of hgc' hgw'
      have h1 : ((βr (labelS * xs)) - 1).rank = ((βr (rs 6 * xs)) - 1).rank := by
        rw [← e, rank_conj']
      rw [rank_labelS_mul_xs, rank_rs6_mul_xs] at h1
      exact absurd h1 (by decide)
  · exfalso
    have e := conj_mul_of hgc hgw
    have h1 : ((βr (labelS * s)) - 1).rank = ((βr (rs 6 * xs)) - 1).rank := by
      rw [← e, rank_conj']
    rw [hr', rank_rs6_mul_xs] at h1
    exact absurd h1 (by decide)

@[expose] noncomputable def labelHom
    : Subgroup.centralizer ({labelS} : Set Sbp) →* Eam :=
  vStabEam.toMonoidHom.comp
    ((sEquiv.toMonoidHom.comp (Subgroup.centralizer ({labelS} : Set Sbp)).subtype).codRestrict
      (vStab cv0) fun h => sEquiv_mem_vStab (Subgroup.mem_centralizer_singleton_iff.1 h.2))

theorem labelHom_injective :
    Function.Injective labelHom := by
  intro a b h
  have h1 := vStabEam.injective h
  have h2 : sEquiv (a : Sbp) = sEquiv (b : Sbp) := congrArg Subtype.val h1
  exact Subtype.ext (sEquiv.injective h2)

theorem oddSq_of_oddAt
    {y : commutator Eam} {s : Sbp}
    (hs : s ∈ Subgroup.centralizer ({labelS} : Set Sbp)) (hsy : labelHom ⟨s, hs⟩ = (y : Eam))
    (h : OddAt labelS s) :
    ∃ t ∈ closure {h : commutator Eam | h * y = y * h ∧ Odd (orderOf h)}, t * t = y := by
  obtain ⟨h₁, h₂, h1c, h2c, h1y, h2y, o1, o2, hsq⟩ := h
  have m1 : h₁ ∈ Subgroup.centralizer ({labelS} : Set Sbp) :=
    Subgroup.mem_centralizer_singleton_iff.2 h1c
  have m2 : h₂ ∈ Subgroup.centralizer ({labelS} : Set Sbp) :=
    Subgroup.mem_centralizer_singleton_iff.2 h2c
  have od : ∀ {k : Sbp} (hk : k ∈ Subgroup.centralizer ({labelS} : Set Sbp)),
      Odd (orderOf k) → Odd (orderOf (labelHom ⟨k, hk⟩)) := fun hk hko => by
    rwa [orderOf_injective labelHom labelHom_injective, Subgroup.orderOf_mk]
  have mE : ∀ {k : Sbp} (hk : k ∈ Subgroup.centralizer ({labelS} : Set Sbp)),
      Odd (orderOf k) → labelHom ⟨k, hk⟩ ∈ commutator Eam := fun hk hko =>
    mem_of_odd_of_index_two Stroth21Aux.index_commutator_Eam (od hk hko)
  have cm : ∀ {k : Sbp} (hk : k ∈ Subgroup.centralizer ({labelS} : Set Sbp)), k * s = s * k →
      labelHom ⟨k, hk⟩ * (y : Eam) = (y : Eam) * labelHom ⟨k, hk⟩ := fun hk hks => by
    rw [← hsy, ← map_mul, ← map_mul]
    exact congrArg labelHom (Subtype.ext hks)
  refine ⟨⟨_, mE m1 o1⟩ * ⟨_, mE m2 o2⟩, mul_mem (subset_closure ⟨Subtype.ext (cm m1 h1y),
    by rw [Subgroup.orderOf_mk]; exact od m1 o1⟩) (subset_closure ⟨Subtype.ext (cm m2 h2y),
    by rw [Subgroup.orderOf_mk]; exact od m2 o2⟩), Subtype.ext ?_⟩
  show labelHom ⟨h₁, m1⟩ * labelHom ⟨h₂, m2⟩ * (labelHom ⟨h₁, m1⟩ * labelHom ⟨h₂, m2⟩) = (y : Eam)
  rw [← hsy, ← map_mul, ← map_mul]
  exact congrArg labelHom (Subtype.ext hsq)

theorem oddAt_of_mem_centQ
    {s : Sbp} (hsQ : s ∈ Qs) (hsc : s * labelS = labelS * s)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsl : s ≠ labelS)
    (hx : ¬ IsConj (cV0 * lamW0H) ⟨sEquiv s, sEquiv_mem_vStab hsc⟩)
    (hcx : ¬ IsConj lamW0H ⟨sEquiv s, sEquiv_mem_vStab hsc⟩) : OddAt labelS s := by
  have hr := (native_inner_involution_census labelS_mem_Qs (IsConj.refl labelS)).2.1
  rcases hr s hsQ hsc hs2 hs1 hsl with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (isConj_cV0_mul_lamW0H_of_RB hs2 hsc h1 h2) hx
  · exact absurd (isConj_lamW0H_of_RA hs2 hsc h1 h2) hcx
  · exact oddAt_of_Y2 hs2 hsc h1 h2
  · exact oddAt_of_cY2 hs2 hsc h1 h2
  · exact oddAt_of_Y3 hsQ hs2 hsc h1 h2

theorem isConj_of_vStabEam
    {a b : vStab cv0} {a' b' : Eam} (h : IsConj a b)
    (ha : vStabEam a = a') (hb : vStabEam b = b') : IsConj a' b' := by
  subst ha hb
  exact vStabEam.toMonoidHom.map_isConj h

theorem n1OddSquareTest :
    N1OddSquareTest := by
  intro y hyN hy2 hy1 hyc hx hcx
  obtain ⟨v, hvy⟩ : ∃ v : vStab cv0, vStabEam v = (y : Eam) :=
    ⟨vStabEam.symm (y : Eam), MulEquiv.apply_symm_apply _ _⟩
  have hvN : v ∈ NH := by
    show iotaH v ∈ Sp8.N1
    rw [iotaH_apply, ← coe_vStabEam, hvy]
    exact hyN
  obtain ⟨hsQ, hsc⟩ := symm_mem_centQ_of_mem_NH hvN
  obtain ⟨s, hs⟩ : ∃ s : Sbp, s = sEquiv.symm (v : Shat) := ⟨_, rfl⟩
  rw [← hs] at hsQ hsc
  have hsm : s ∈ Subgroup.centralizer ({labelS} : Set Sbp) :=
    Subgroup.mem_centralizer_singleton_iff.2 hsc
  have hsv : (⟨sEquiv s, sEquiv_mem_vStab hsc⟩ : vStab cv0) = v := by
    apply Subtype.ext
    show sEquiv s = (v : Shat)
    rw [hs, MulEquiv.apply_symm_apply]
  have hpsi : labelHom ⟨s, hsm⟩ = (y : Eam) := by
    rw [← hvy, ← hsv]
    rfl
  have hvD : ((v : Shat) : Dfull) = ((y : Eam) : Dfull) := by rw [← coe_vStabEam, hvy]
  have hyD : ((y : Eam) : Dfull) * ((y : Eam) : Dfull) = 1 := by
    have h := congrArg (fun t : commutator Eam => ((t : Eam) : Dfull)) hy2
    simpa using h
  have hv2 : v * v = 1 := Subtype.ext (Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [hvD]
    exact hyD))
  have hs2 : s * s = 1 := by
    have h := congrArg (fun t : vStab cv0 => sEquiv.symm (t : Shat)) hv2
    simp only [Subgroup.coe_mul, map_mul, Subgroup.coe_one, map_one] at h
    rw [hs]
    exact h
  have hv1 : v ≠ 1 := fun h => hy1 (by rw [← hvy, h, map_one])
  have hvc : v ≠ cV0 := fun h => hyc (by rw [← hvy, h, vStabEam_cV0])
  have e2 : vStabEam ⟨sEquiv s, sEquiv_mem_vStab hsc⟩ = (y : Eam) :=
    (congrArg vStabEam hsv).trans hvy
  exact oddSq_of_oddAt hsm hpsi (oddAt_of_mem_centQ hsQ hsc hs2
    (hs ▸ symm_ne_one_of_ne_one hv1) (hs ▸ symm_ne_labelS_of_ne hvc)
    (fun h => hx (isConj_of_vStabEam h vStabEam_cV0_mul_lamW0H e2))
    (fun h => hcx (isConj_of_vStabEam h vStabEam_lamW0H e2)))

theorem stroth21
    : Stroth21 :=
  stroth21_of_N1 (involutionsIntoN1Dfull_of involutionsIntoN1) n1OddSquareTest

end CFSG.EvenSmallLie.TwoE6
