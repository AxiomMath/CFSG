module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2CertBase
public import CFSG.Sporadic.J4.QT2LocBasicRep
public import CFSG.Sporadic.J4.QTRankInvBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2CoreBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Gen
public import CFSG.Sporadic.J4.QT2LocCntMainBase

public section

namespace CFSG.QuasithinUnique.A5.Dec2

open CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 Matrix

variable {ws : List (List ℤ)}

theorem Mx_eEl_b (hM : MatFacts) {m : ℕ} (hm : m < 16) : Mx (eEl ws m) = rowsMatrix (eR ws m) := by
  have h := QT2A.Mx_el5 hM (eW ws m)
  unfold eEl
  rw [h]
  unfold eR
  rw [eTab_get hm]

theorem Mx_gEl_b (hM : MatFacts) (k : ℕ) : Mx (gEl ws k) = rowsMatrix (wR (ws.getD k [])) :=
  QT2A.Mx_el5 hM _

theorem eEl_mul_b (hM : MatFacts) (h : chkGrp ws = true) {m m' : ℕ} (hm : m < 16)
    (hm' : m' < 16) : eEl ws m * eEl ws m' = eEl ws (m ^^^ m') := by
  obtain ⟨-, -, -, -, h5, -⟩ := chkGrp_parts h
  apply Mx_injective
  rw [map_mul, Mx_eEl_b hM hm, Mx_eEl_b hM hm', Mx_eEl_b hM (xor_lt_sixteen hm hm'),
    ← rowsMatrix_mulRows, eqRows_iff.1 (h5 m hm m' hm')]

theorem eEl_zero_b (hM : MatFacts) (h : chkGrp ws = true) : eEl ws 0 = 1 := by
  obtain ⟨-, -, h3, -⟩ := chkGrp_parts h
  apply Mx_injective
  rw [Mx_eEl_b hM (by norm_num : 0 < 16), eqRows_iff.1 h3, rowsMatrix_idRows, map_one]

theorem eEl_inj_b (hM : MatFacts) (h : chkGrp ws = true) {m m' : ℕ} (hm : m < 16)
    (hm' : m' < 16) (he : eEl ws m = eEl ws m') : m = m' := by
  by_contra hne
  obtain ⟨-, hw, -, hd, -⟩ := chkGrp_parts h
  have hd' := allDistinct_spec hd m m' (by simpa using hm) (by simpa using hm') hne
  simp only [List.getElem_map, List.getElem_range] at hd'
  apply ne_of_eqRows_false (hw m hm) (hw m' hm') hd'
  rw [← Mx_eEl_b hM hm, ← Mx_eEl_b hM hm', he]

theorem gEl_eq_b (hM : MatFacts) (h : chkGrp ws = true) {k : ℕ} (hk : k < 4) :
    gEl ws k = eEl ws (2 ^ k) := by
  obtain ⟨-, -, -, -, -, h6⟩ := chkGrp_parts h
  have hk16 : 2 ^ k < 16 := by
    have : 2 ^ k < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hk
    simpa using this
  apply Mx_injective
  rw [Mx_gEl_b hM, Mx_eEl_b hM hk16, eqRows_iff.1 (h6 k hk)]

theorem Vgrp_subset_b (hM : MatFacts) (h : chkGrp ws = true) :
    ∀ v ∈ Vgrp ws, ∃ m < 16, v = eEl ws m := by
  obtain ⟨hlen, -⟩ := chkGrp_parts h
  have hsub := QT2A.closure_subset_of_closed {x | x ∈ ws.map QT2A.el5}
    {g | ∃ m < 16, g = eEl ws m} ⟨0, by norm_num, (eEl_zero_b hM h).symm⟩ (by
      rintro _ ⟨m, hm, rfl⟩ g hg
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
      obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.1 hw
      have hk4 : k < 4 := by omega
      have hk16 : 2 ^ k < 16 := by
        have : 2 ^ k < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hk4
        simpa using this
      have hgk : gEl ws k = QT2A.el5 w := by
        unfold gEl
        rw [List.getD_eq_getElem _ _ hk, hkw]
      refine ⟨m ^^^ 2 ^ k, xor_lt_sixteen hm hk16, ?_⟩
      rw [← hgk, gEl_eq_b hM h hk4, eEl_mul_b hM h hm hk16])
  intro v hv
  exact hsub hv

theorem card_Vgrp_b (hM : MatFacts) (h : chkGrp ws = true) : Nat.card (Vgrp ws) = 16 := by
  have hset : (Vgrp ws : Set J) = ↑((Finset.range 16).image (eEl ws)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM h x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩)
    · intro hx
      obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact eEl_mem h m
  have h1 : Nat.card (Vgrp ws) = ((Finset.range 16).image (eEl ws)).card := by
    rw [← Set.ncard_coe_finset, ← hset]
    exact Nat.card_coe_set_eq _
  rw [h1, Finset.card_image_of_injOn, Finset.card_range]
  intro m hm m' hm' he
  exact eEl_inj_b hM h (Finset.mem_range.1 hm) (Finset.mem_range.1 hm') he

theorem Vgrp_comm_b (hM : MatFacts) (h : chkGrp ws = true) :
    ∀ a ∈ Vgrp ws, ∀ b ∈ Vgrp ws, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM h a ha
  obtain ⟨m', hm', rfl⟩ := Vgrp_subset_b hM h b hb
  rw [eEl_mul_b hM h hm hm', eEl_mul_b hM h hm' hm, Nat.xor_comm]

theorem Vgrp_sq_b (hM : MatFacts) (h : chkGrp ws = true) : ∀ a ∈ Vgrp ws, a * a = 1 := by
  intro a ha
  obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM h a ha
  rw [eEl_mul_b hM h hm hm, Nat.xor_self, eEl_zero_b hM h]

theorem fiveElt_conj_eEl_b (hM : MatFacts)
    (h : chkNorm ws = true) {m : ℕ} (hm : m < 16) :
    ∃ m' < 16, fiveElt * eEl ws m * fiveElt⁻¹ = eEl ws m' := by
  obtain ⟨hall, -⟩ := chkNorm_parts h
  obtain ⟨m', hm', he⟩ := hall m hm
  refine ⟨m', hm', ?_⟩
  have he' : mulRows x0GenRows[0]! (eR ws m) = mulRows (eR ws m') x0GenRows[0]! := eqRows_iff.1 he
  have hx : fiveElt * eEl ws m = eEl ws m' * fiveElt := by
    apply Mx_injective
    rw [map_mul, map_mul, Mx_fiveElt hM, Mx_eEl_b hM hm, Mx_eEl_b hM hm', ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows, he']
  calc fiveElt * eEl ws m * fiveElt⁻¹ = (eEl ws m' * fiveElt) * fiveElt⁻¹ := by rw [hx]
    _ = eEl ws m' := by group

theorem fiveElt_mem_normalizer_b (hM : MatFacts)
    (hg : chkGrp ws = true) (h : chkNorm ws = true) :
    fiveElt ∈ Subgroup.normalizer ((Vgrp ws : Subgroup J) : Set J) := by
  apply mem_normalizer_of_forward
  intro v hv
  obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM hg v hv
  obtain ⟨m', hm', he⟩ := fiveElt_conj_eEl_b hM h hm
  rw [he]
  exact eEl_mem hg m'

theorem fiveElt_fpf_b (hM : MatFacts) (hg : chkGrp ws = true)
    (h : chkNorm ws = true) : ∀ v ∈ Vgrp ws, fiveElt * v = v * fiveElt → v = 1 := by
  intro v hv hc
  obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM hg v hv
  by_contra hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (eEl_zero_b hM hg)
  obtain ⟨-, hfp⟩ := chkNorm_parts h
  have hf := hfp (m - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hf
  obtain ⟨-, hw, -, -, -, -⟩ := chkGrp_parts hg
  have hxw : wfR xR = true := x0Gens_zero_facts.1
  have h2 := congrArg Mx hc
  rw [map_mul, map_mul, Mx_fiveElt hM, Mx_eEl_b hM hm, ← rowsMatrix_mulRows,
    ← rowsMatrix_mulRows] at h2
  exact ne_of_eqRows_false (wfR_mulRows hxw (hw m hm)) (wfR_mulRows (hw m hm) hxw) hf h2

theorem fpfV_of_chk_b
    (hM : MatFacts) (hg : chkGrp ws = true) (h : chkNorm ws = true) : FpfV (Vgrp ws) :=
  ⟨card_Vgrp_b hM hg, Vgrp_comm_b hM hg, Vgrp_sq_b hM hg, fiveElt,
    fiveElt_mem_normalizer_b hM hg h, orderOf_fiveElt hM, fiveElt_fpf_b hM hg h⟩

theorem hK_of_chk_b (hM : MatFacts) (hg : chkGrp ws = true)
    (h : chkK0 ws = true) : ∀ g ∈ X0Sub, (∀ v ∈ Vgrp ws, g * v = v * g) →
      orderOf g ≠ 3 ∧ orderOf g ≠ 7 ∧ orderOf g ≠ 23 := by
  intro g hgX hcomm
  obtain ⟨q, hq, hgq⟩ := (mem_X0Sub_iff hM).1 hgX
  have hwf : wfR x0Orb.mats[q]! = true := mats_wf hq
  obtain ⟨-, hw, -, -, -, h6⟩ := chkGrp_parts hg
  have hc : ∀ k < 4, eqRows (mulRows x0Orb.mats[q]! (wR (ws.getD k [])))
      (mulRows (wR (ws.getD k [])) x0Orb.mats[q]!) = true := by
    intro k hk
    have hGk : wfR (wR (ws.getD k [])) = true := by
      rw [eqRows_iff.1 (h6 k hk)]
      exact hw _ (by
        have : 2 ^ k < 2 ^ 4 := Nat.pow_lt_pow_right (by norm_num) hk
        simpa using this)
    have h1 := hcomm (gEl ws k) (gEl_mem hg hk)
    have h2 := congrArg Mx h1
    rw [map_mul, map_mul, hgq, Mx_gEl_b hM, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows] at h2
    apply eqRows_iff.2
    exact eq_of_rowsMatrix_eq (wfR_mulRows hwf hGk) (wfR_mulRows hGk hwf) h2
  have hres := chkK0_spec h hq hc
  refine ⟨fun ho => ?_, fun ho => ?_, fun ho => ?_⟩
  · have := ordRows_of_orderOf hgq hwf ho (by norm_num)
    rw [hres.1] at this
    exact absurd this (by decide)
  · have := ordRows_of_orderOf hgq hwf ho (by norm_num)
    rw [hres.2.1] at this
    exact absurd this (by decide)
  · have := ordRows_of_orderOf hgq hwf ho (by norm_num)
    rw [hres.2.2] at this
    exact absurd this (by decide)

theorem chkN_spec_b (hM : MatFacts) (hg : chkGrp ws = true)
    (h : chkN ws = true) :
    ∃ n ∈ Subgroup.normalizer ((Vgrp ws : Subgroup J) : Set J), ∃ j : ℕ, ¬ j ≡ 1 [MOD 5] ∧
      n * fiveElt * n⁻¹ = fiveElt ^ j := by
  unfold chkN chkNcore at h
  obtain ⟨q, hq, h2⟩ := List.any_eq_true.1 h
  obtain ⟨i, hi, h3⟩ := List.any_eq_true.1 h2
  dsimp only at h3
  rw [Bool.and_eq_true] at h3
  obtain ⟨hE, hj⟩ := h3
  have hq' : q < 6720 := List.mem_range.1 hq
  obtain ⟨g₀, hg₀, hMg₀⟩ := mem_X0Sub_of_lt hM q hq'
  obtain ⟨n, hn⟩ : ∃ n : J, n = g₀ * nElt ^ (i + 1) := ⟨_, rfl⟩
  have hMn : Mx n = rowsMatrix (mulRows x0Orb.mats[q]! (powRows nRows (i + 1))) := by
    rw [hn, map_mul, map_pow, hMg₀, Mx_nElt hM, ← rowsMatrix_powRows, ← rowsMatrix_mulRows]
  have h1 : ∀ m < 16, ∃ m' < 16, n * eEl ws m = eEl ws m' * n := by
    intro m hm
    have hmem : eR ws m ∈ eList ws := mem_eList.2 ⟨m, hm, rfl⟩
    obtain ⟨e', he', hee'⟩ := List.any_eq_true.1 (List.all_eq_true.1 hE _ hmem)
    obtain ⟨m', hm', rfl⟩ := mem_eList.1 he'
    refine ⟨m', hm', ?_⟩
    apply Mx_injective
    rw [map_mul, map_mul, hMn, Mx_eEl_b hM hm, Mx_eEl_b hM hm', ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows]
    exact congrArg rowsMatrix (eqRows_iff.1 hee')
  refine ⟨n, ?_, ?_⟩
  · apply mem_normalizer_of_forward
    intro v hv
    obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM hg v hv
    obtain ⟨m', hm', he⟩ := h1 m hm
    have : n * eEl ws m * n⁻¹ = eEl ws m' := by
      calc n * eEl ws m * n⁻¹ = (eEl ws m' * n) * n⁻¹ := by rw [he]
        _ = eEl ws m' := by group
    rw [this]
    exact eEl_mem hg m'
  · obtain ⟨j, hjmem, hjeq⟩ := List.any_eq_true.1 hj
    have hj3 : j = 2 ∨ j = 3 ∨ j = 4 := by simpa using hjmem
    refine ⟨j, ?_, ?_⟩
    · rcases hj3 with rfl | rfl | rfl <;> decide
    · have hx : n * fiveElt = fiveElt ^ j * n := by
        apply Mx_injective
        rw [map_mul, map_mul, map_pow, hMn, Mx_fiveElt hM, ← rowsMatrix_powRows,
          ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
        exact congrArg rowsMatrix (eqRows_iff.1 hjeq)
      calc n * fiveElt * n⁻¹ = (fiveElt ^ j * n) * n⁻¹ := by rw [hx]
        _ = fiveElt ^ j := by group

theorem lt_relIndex_of_chkW_b (hM : MatFacts)
    (hg : chkGrp ws = true) {Q : Array V2} {q : J}
    (hMq : Mx q = rowsMatrix Q) (hW : chkW ws Q = true) :
    16 < (Subgroup.centralizer ((Vgrp ws : Subgroup J) : Set J) ⊓
      Subgroup.centralizer ({fiveElt} : Set J)).relIndex
      (Subgroup.centralizer ((Vgrp ws : Subgroup J) : Set J)) := by
  unfold chkW at hW
  dsimp only at hW
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hW
  obtain ⟨⟨⟨⟨hQw, hQIw⟩, hQQI⟩, hcomm0⟩, hdist0⟩ := hW
  obtain ⟨-, hw, -, -, -, -⟩ := chkGrp_parts hg
  have hcomm : ∀ m < 16, eqRows (mulRows Q (eR ws m)) (mulRows (eR ws m) Q) = true := hcomm0
  have hdist : allDistinct (((List.range 16).map fun m => mulRows (mulRows (eR ws m) xR)
      (eR ws m)) ++ [mulRows (mulRows Q xR) (invRows Q)]) = true := hdist0
  have hxw : wfR xR = true := x0Gens_zero_facts.1
  set QI := invRows Q with hQI
  have e1 : rowsMatrix Q * rowsMatrix QI = 1 := by
    rw [← rowsMatrix_mulRows, eqRows_iff.1 hQQI, rowsMatrix_idRows]
  have hMqinv : Mx q⁻¹ = rowsMatrix QI := by
    have e2 : Mx q⁻¹ * Mx q = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    calc Mx q⁻¹ = Mx q⁻¹ * (rowsMatrix Q * rowsMatrix QI) := by rw [e1, mul_one]
      _ = (Mx q⁻¹ * Mx q) * rowsMatrix QI := by rw [hMq, mul_assoc]
      _ = rowsMatrix QI := by rw [e2, one_mul]
  have hinv : ∀ m < 16, (eEl ws m)⁻¹ = eEl ws m := by
    intro m hm
    have hsq : eEl ws m * eEl ws m = 1 := by
      rw [eEl_mul_b hM hg hm hm, Nat.xor_self, eEl_zero_b hM hg]
    exact inv_eq_of_mul_eq_one_right hsq
  let qi : Fin 17 → J := fun i => if (i : ℕ) < 16 then eEl ws i else q
  let Lrow : Fin 17 → Array V2 := fun i =>
    if (i : ℕ) < 16 then mulRows (mulRows (eR ws i) xR) (eR ws i)
    else mulRows (mulRows Q xR) QI
  have hqmem : ∀ i, qi i ∈ Subgroup.centralizer ((Vgrp ws : Subgroup J) : Set J) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hi : (i : ℕ) < 16
    · simp only [qi, ite_eq_left hi]
      exact Vgrp_comm_b hM hg v hv _ (eEl_mem hg _)
    · simp only [qi, ite_eq_right hi]
      obtain ⟨m, hm, rfl⟩ := Vgrp_subset_b hM hg v hv
      have h2 := eqRows_iff.1 (hcomm m hm)
      apply Mx_injective
      rw [map_mul, map_mul, hMq, Mx_eEl_b hM hm, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows]
      exact congrArg rowsMatrix h2.symm
  have hconj : ∀ i : Fin 17, Mx (qi i * fiveElt * (qi i)⁻¹) = rowsMatrix (Lrow i) := by
    intro i
    by_cases hi : (i : ℕ) < 16
    · simp only [qi, Lrow, ite_eq_left hi]
      rw [hinv i hi, map_mul, map_mul, Mx_eEl_b hM hi, Mx_fiveElt hM, ← rowsMatrix_mulRows,
        ← rowsMatrix_mulRows]
      rfl
    · simp only [qi, Lrow, ite_eq_right hi]
      rw [map_mul, map_mul, hMq, hMqinv, Mx_fiveElt hM, ← rowsMatrix_mulRows,
        ← rowsMatrix_mulRows]
      rfl
  have hwfL : ∀ i : Fin 17, wfR (Lrow i) = true := by
    intro i
    by_cases hi : (i : ℕ) < 16
    · simp only [Lrow, ite_eq_left hi]
      exact wfR_mulRows (wfR_mulRows (hw i hi) hxw) (hw i hi)
    · simp only [Lrow, ite_eq_right hi]
      exact wfR_mulRows (wfR_mulRows hQw hxw) hQIw
  have hinj : Function.Injective fun i => qi i * fiveElt * (qi i)⁻¹ := by
    intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    let L : List (Array V2) := ((List.range 16).map fun m =>
        mulRows (mulRows (eR ws m) xR) (eR ws m)) ++ [mulRows (mulRows Q xR) QI]
    have hLlen : L.length = 17 := by simp [L]
    have hLget : ∀ i : Fin 17, L[(i : ℕ)]'(by rw [hLlen]; exact i.2) = Lrow i := by
      intro i
      by_cases hi : (i : ℕ) < 16
      · simp only [Lrow, ite_eq_left hi]
        simp only [L]
        rw [List.getElem_append_left (by simpa using hi)]
        simp
      · simp only [Lrow, ite_eq_right hi]
        have h16 : (i : ℕ) = 16 := by omega
        simp only [L]
        rw [List.getElem_append_right (by simp; omega)]
        simp [h16]
    have hd := allDistinct_spec (l := L) hdist i j (by rw [hLlen]; exact i.2)
      (by rw [hLlen]; exact j.2) hne'
    rw [hLget i, hLget j] at hd
    apply ne_of_eqRows_false (hwfL i) (hwfL j) hd
    rw [← hconj i, ← hconj j]
    exact congrArg Mx hij
  have h17 := le_relIndex_inf_centralizer_of_conj
    (Subgroup.centralizer ((Vgrp ws : Subgroup J) : Set J)) fiveElt qi hqmem hinj
  omega

theorem five_sq_not_dvd_card_J_b (hF : J4Basic) : ¬ 5 ^ 2 ∣ Nat.card J := by
  rw [hF.cardJ]
  norm_num

theorem card_centralizer_of_orderOf_five_b
    (hF : J4Basic)
    (hK0 : Subgroup.centralizer ({fiveElt} : Set J) ≤ X0Sub) {x : J} (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set J)) = 6720 := by
  obtain ⟨n, hn⟩ := exists_conj_fiveElt_sq hF.mat
  obtain ⟨g, hg⟩ := exists_conj_five (five_sq_not_dvd_card_J_b hF) (orderOf_fiveElt hF.mat) hn hx
  have h1 := card_centralizer_singleton_conj g x
  rw [hg] at h1
  rw [← h1]
  have h2 : Subgroup.centralizer ({fiveElt} : Set J) = X0Sub :=
    le_antisymm hK0 (X0Sub_le_centralizer hF.mat)
  rw [h2]
  exact card_X0Sub hF.mat

theorem isPGroup_centralizer_of_x0_b
    (hFb : J4Basic)
    (hK0 : Subgroup.centralizer ({fiveElt} : Set J) ≤ X0Sub)
    {V : Subgroup J} (hF : FpfV V) (hx : fiveElt ∈ Subgroup.normalizer (V : Set J))
    (hfpf : ∀ v ∈ V, fiveElt * v = v * fiveElt → v = 1)
    (hK : ∀ g ∈ X0Sub, (∀ v ∈ V, g * v = v * g) →
      orderOf g ≠ 3 ∧ orderOf g ≠ 7 ∧ orderOf g ≠ 23)
    (hn : ∃ n ∈ Subgroup.normalizer (V : Set J), ∃ j : ℕ, ¬ j ≡ 1 [MOD 5] ∧
      n * fiveElt * n⁻¹ = fiveElt ^ j) :
    IsPGroup 2 (Subgroup.centralizer (V : Set J)) := by
  classical
  have hM := hFb.mat
  have h5 : ¬ 5 ∣ Nat.card (Subgroup.centralizer (V : Set J)) :=
    five_not_dvd_card_centralizer (five_sq_not_dvd_card_J_b hFb) hF
  have hx5' : fiveElt ^ 5 = 1 := by
    rw [← orderOf_fiveElt hM]
    exact pow_orderOf_eq_one _
  obtain ⟨hc16, -, hsq, -⟩ := hF
  have hVbot : V ≠ ⊥ := by
    intro hb
    rw [hb] at hc16
    simp at hc16
  obtain ⟨⟨y, hyV⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hVbot
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hsqy : y * y = 1 := hsq y hyV
  have hxC : fiveElt ∉ Subgroup.centralizer (V : Set J) := by
    intro hc
    have h1 := Subgroup.mem_centralizer_iff.1 hc y hyV
    exact hy1' (hfpf y hyV h1.symm)
  have hdvd0 : Nat.card (Subgroup.centralizer (V : Set J)) ∣ 501397585920 := by
    have hle : Subgroup.centralizer (V : Set J) ≤ Subgroup.centralizer ({y} : Set J) :=
      fun c hc => by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact Subgroup.mem_centralizer_iff.1 hc y hyV
    have hd := Subgroup.card_dvd_of_le hle
    rcases inv_conj_root_b hFb hsqy hy1' with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      have h1 := card_centralizer_singleton_conj c (eta uJ 11 1)
      rw [hc] at h1
      have hle2 : Subgroup.centralizer ({eta uJ 11 1} : Set J) ≤ Hj := by
        intro x hx
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hx
        have h2 : x * eta uJ 11 1 = eta uJ 11 1 * x := h1
        exact centralizer_eta_one_le_Hj_b hFb h2
      have h2 := Subgroup.card_dvd_of_le hle2
      rw [hFb.cardHj] at h2
      rw [h1] at hd
      exact hd.trans h2
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      have h1 := card_centralizer_singleton_conj c (eta uJ 11 3)
      rw [hc, card_centralizer_of_mem_Zl_b hFb (mem_Zl.2 ⟨3, three_mem_zMasks, rfl⟩)] at h1
      rw [h1] at hd
      exact hd.trans (by norm_num)
  have hpos : Nat.card (Subgroup.centralizer (V : Set J)) ≠ 0 := Nat.card_pos.ne'
  apply QT2A.isPGroup_two_of_no_odd_prime
  intro r hr hr2 hrdvd
  have : Fact r.Prime := ⟨hr⟩
  have hrM : r ∣ 501397585920 := hrdvd.trans hdvd0
  have hnoprime : ∀ r : ℕ, [Fact r.Prime] → r ∣ Nat.card (Subgroup.centralizer (V : Set J)) →
      (r = 3 ∨ r = 7 ∨ r = 23) →
      ¬ r ^ (Nat.card (Subgroup.centralizer (V : Set J))).factorization r ≡ 1 [MOD 5] →
      False := by
    intro r _ _ hr3 hmod
    obtain ⟨s, hsC, hso, hsx⟩ := exists_order_prime_comm_centralizer (V : Set J) fiveElt hx hx5'
      h5 r hmod
    have hsmem : s ∈ Subgroup.centralizer ({fiveElt} : Set J) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hsx.symm
    have hsX : s ∈ X0Sub := hK0 hsmem
    have hcomm : ∀ v ∈ V, s * v = v * s := fun v hv =>
      (Subgroup.mem_centralizer_iff.1 hsC v hv).symm
    obtain ⟨h3, h7, h23⟩ := hK s hsX hcomm
    rcases hr3 with rfl | rfl | rfl
    · exact h3 hso
    · exact h7 hso
    · exact h23 hso
  rcases prime_dvd_cases hr hr2 hrM with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2⟩ := factorization_cases hr hpos hrdvd hdvd0 3 (by norm_num)
    refine hnoprime 3 hrdvd (Or.inl rfl) ?_
    generalize (Nat.card (Subgroup.centralizer (V : Set J))).factorization 3 = a at h1 h2 ⊢
    interval_cases a <;> decide
  · exact h5 hrdvd
  · obtain ⟨h1, h2⟩ := factorization_cases hr hpos hrdvd hdvd0 1 (by norm_num)
    refine hnoprime 7 hrdvd (Or.inr (Or.inl rfl)) ?_
    generalize (Nat.card (Subgroup.centralizer (V : Set J))).factorization 7 = a at h1 h2 ⊢
    interval_cases a
    decide
  · have h121 : ¬ 11 ^ 2 ∣ Nat.card (Subgroup.centralizer (V : Set J)) := fun hd => by
      have := hd.trans hdvd0
      norm_num at this
    obtain ⟨s', hs'⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer (V : Set J))) 11 hrdvd
    have hsC : (s' : J) ∈ Subgroup.centralizer (V : Set J) := s'.2
    have hs11 : orderOf (s' : J) = 11 := by
      rw [Subgroup.orderOf_coe]
      exact hs'
    obtain ⟨n, hnN, j, hj, hnj⟩ := hn
    obtain ⟨x1, hx1o, hx1⟩ := exists_order_five_centralizing_centralizer (V : Set J) fiveElt n hx
      hnN (orderOf_fiveElt hM) hxC j hj hnj 11 (s' : J) hsC hs11 h121
    have hsx1 : (s' : J) ∈ Subgroup.centralizer ({x1} : Set J) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hx1.symm
    have hd := Subgroup.orderOf_dvd_natCard _ hsx1
    rw [hs11, card_centralizer_of_orderOf_five_b hFb hK0 hx1o] at hd
    norm_num at hd
  · obtain ⟨h1, h2⟩ := factorization_cases hr hpos hrdvd hdvd0 1 (by norm_num)
    refine hnoprime 23 hrdvd (Or.inr (Or.inr rfl)) ?_
    generalize (Nat.card (Subgroup.centralizer (V : Set J))).factorization 23 = a at h1 h2 ⊢
    interval_cases a
    decide

theorem classRad_of_chkAll_b
    (hFb : J4Basic)
    (hK0 : Subgroup.centralizer ({fiveElt} : Set J) ≤ X0Sub)
    {Q : Array V2} {q : J} (hMq : Mx q = rowsMatrix Q) (h : chkAll ws Q = true) :
    ClassRad (Vgrp ws) := by
  have hM := hFb.mat
  unfold chkAll at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hg, hN⟩, hK⟩, hn⟩, hW⟩ := h
  have hF := fpfV_of_chk_b hM hg hN
  have hx := fiveElt_mem_normalizer_b hM hg hN
  have hU : IsPGroup 2 (Subgroup.centralizer ((Vgrp ws : Subgroup J) : Set J)) :=
    isPGroup_centralizer_of_x0_b hFb hK0 hF hx (fiveElt_fpf_b hM hg hN) (hK_of_chk_b hM hg hK)
      (chkN_spec_b hM hg hn)
  exact classRad_of_centralizer hx (orderOf_fiveElt hM) hF.2.1 hU
    (lt_relIndex_of_chkW_b hM hg hMq hW)

end CFSG.QuasithinUnique.A5.Dec2
