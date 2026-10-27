module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Native
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2CertB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B0
public import Certificates.Certificate4029
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Wit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Pent

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2

theorem d4_smul_row {g : ↥J} {M : Array V2} (hg : Mx g⁻¹ = rowsMatrix M) (a : V2) :
    g • toRow a.toVec = toRow (frApply (frTable M) a).toVec := by
  rw [← ofRow_inj, smul_row, frApply_toVec_eq_vecMul, ← hg]
  rfl

theorem d4El_ne_zero (w : List Int) : ∀ l ∈ d4El w, l ≠ 0 := by
  intro l hl
  unfold d4El at hl
  obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
  split_ifs with h <;> omega

theorem d4_Mx_inv (w : List Int) :
    Mx (el5 (d4El w))⁻¹ = rowsMatrix (wR (invWord (d4El w))) := by
  have hM := Certificates.certificate4029.basic.mat
  have e : (el5 (d4El w))⁻¹ = el5 (invWord (d4El w)) :=
    (wordProd_invWord gen5 (d4El w) (d4El_ne_zero w)).symm
  rw [e]
  exact Mx_el5 hM _

theorem d4_frame {r : V2} {w : List Int}
    (hroot : (frApply (frTable (wR (d4El w))) rootV).beq r = true) :
    (el5 (d4El w))⁻¹ • w₀ = toRow r.toVec := by
  have hM := Certificates.certificate4029.basic.mat
  rw [smul_w₀_eq (M := wR (d4El w)) (by rw [inv_inv, Mx_el5 hM]), V2.beq_iff.1 hroot]

theorem d4_eta_inv
    (c : ℕ) : (eta uJ 11 c)⁻¹ = eta uJ 11 c := by
  have hM := Certificates.certificate4029.basic.mat
  have h := eta_xor (elem_uJ hM) (m := 11) le_rfl c c
  rw [Nat.xor_self, eta_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

theorem d4_eta_smul (c : ℕ) (a : V2) :
    eta uJ 11 c • toRow a.toVec = toRow (frApply (frTable (etaE c)) a).toVec := by
  have hM := Certificates.certificate4029.basic.mat
  exact d4_smul_row (by rw [d4_eta_inv]; exact Mx_eta hM 11 le_rfl c) a

theorem d4_x0_step (a : V2) :
    fiveElt • toRow a.toVec = toRow (frApply (frTable (x0InvRows[0]!)) a).toVec :=
  d4_smul_row (Mx_fiveElt_inv Certificates.certificate4029.basic.mat) a

theorem d4_pow_smul (a : V2) (k : ℕ) :
    fiveElt ^ k • toRow a.toVec =
      toRow ((frApply (frTable (x0InvRows[0]!)))^[k] a).toVec := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, d4_x0_step, ih, Function.iterate_succ_apply]

theorem d4_mask
    {r : V2} {h v : ↥J} (hq : h⁻¹ • w₀ = toRow r.toVec) (hv : RIn (toRow r.toVec) v) :
    ∃ c < 2048, h * v * h⁻¹ = eta uJ 11 c := by
  have hM := Certificates.certificate4029.basic.mat
  have h1 := (RIn_rep_b hM Certificates.certificate4029.basic.stab (u := h) (r := toRow r.toVec) hq.symm v).1 hv
  obtain ⟨c, hc, he⟩ := (mem_Eg_iff (elem_uJ hM)).1 h1
  have hc' : c < 2048 := by omega
  exact ⟨c, hc', he⟩

theorem d4EtaTabs_get {c : ℕ} (hc : c < 2048) : d4EtaTabs[c]! = frTable (etaE c) := by
  unfold d4EtaTabs
  rw [getElem!_pos _ c (by simp [hc])]
  simp

theorem d4_fix_of
    {r a : V2} {w : List Int} {v : ↥J} {c k : ℕ}
    (ha : fiveElt ^ k • toRow r.toVec = toRow a.toVec)
    (hPi : wfRows (wR (invWord (d4El w))) = true) (hec : wfRows (etaE c) = true)
    (he : el5 (d4El w) * v * (el5 (d4El w))⁻¹ = eta uJ 11 c) (hc : c < 2048)
    (hfixk : v • (fiveElt ^ k • toRow r.toVec) = fiveElt ^ k • toRow r.toVec) :
    d4Fix c (frApply (frTable (wR (invWord (d4El w)))) a) = true := by
  have h1 : el5 (d4El w) • (fiveElt ^ k • toRow r.toVec) =
      toRow (frApply (frTable (wR (invWord (d4El w)))) a).toVec := by
    rw [ha]
    exact d4_smul_row (d4_Mx_inv w) a
  have h2 : eta uJ 11 c • (el5 (d4El w) • (fiveElt ^ k • toRow r.toVec)) =
      el5 (d4El w) • (fiveElt ^ k • toRow r.toVec) := by
    rw [← he, ← mul_smul,
      show el5 (d4El w) * v * (el5 (d4El w))⁻¹ * el5 (d4El w) = el5 (d4El w) * v by group,
      mul_smul, hfixk]
  rw [h1, d4_eta_smul] at h2
  have h3 : (frApply (frTable (etaE c)) (frApply (frTable (wR (invWord (d4El w)))) a)).toVec =
      (frApply (frTable (wR (invWord (d4El w)))) a).toVec := h2
  have hw1 : (frApply (frTable (wR (invWord (d4El w)))) a).wf = true :=
    frApply_frTable_wf (wfRows_mem hPi) a
  have hw2 : (frApply (frTable (etaE c)) (frApply (frTable (wR (invWord (d4El w)))) a)).wf =
      true := frApply_frTable_wf (wfRows_mem hec) _
  unfold d4Fix
  rw [d4EtaTabs_get hc]
  exact V2.beq_iff.2 ((V2.toVec_inj hw2 hw1).1 h3)

theorem d4_estab_of_pent
    {r : V2} {w : List Int}
    (hPi : wfRows (wR (invWord (d4El w))) = true)
    (hetaWf : ∀ c < 2048, wfRows (etaE c) = true)
    (hroot : (frApply (frTable (wR (d4El w))) rootV).beq r = true)
    {v : ↥J} (hv1 : v ≠ 1) (hR : RIn (toRow r.toVec) v)
    (hfix : ∀ k : ℕ, v • (fiveElt ^ k • toRow r.toVec) = fiveElt ^ k • toRow r.toVec) :
    ∃ c ∈ d4Estab (d4Us r (wR (invWord (d4El w)))),
      el5 (d4El w) * v * (el5 (d4El w))⁻¹ = eta uJ 11 c := by
  obtain ⟨c, hc, he⟩ := d4_mask (d4_frame hroot) hR
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv1
    rw [eta_zero] at he
    have e : v = (el5 (d4El w))⁻¹ * (el5 (d4El w) * v * (el5 (d4El w))⁻¹) * el5 (d4El w) := by
      group
    rw [e, he]
    group
  refine ⟨c, ?_, he⟩
  have hecw := hetaWf c hc
  have key : ∀ k : ℕ, d4Fix c (frApply (frTable (wR (invWord (d4El w))))
      ((frApply (frTable (x0InvRows[0]!)))^[k] r)) = true := fun k =>
    d4_fix_of (r := r) (k := k) (d4_pow_smul r k) hPi hecw he hc (hfix k)
  unfold d4Estab
  rw [List.mem_filter]
  refine ⟨List.mem_range.2 hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hc0, ?_⟩
  unfold d4Us
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  have k4 := key 4
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at k1 k2 k3 k4
  exact ⟨k1, k2, k3, k4⟩

open scoped Classical in
theorem d4_pt_fixed
    {p : V2} (hp : p ∈ d4Pts) :
    toRow p.toVec ∈ Pts ∧ fiveElt • toRow p.toVec = toRow p.toVec := by
  have hM := Certificates.certificate4029.basic.mat
  have hmem : toRow p.toVec ∈ x0PtSet := by
    unfold x0PtSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, rfl⟩
  obtain ⟨g, hg, hgp⟩ := exists_of_mem_pts hM hmem
  refine ⟨⟨g, hgp⟩, ?_⟩
  have hk : g * fiveElt = fiveElt * g :=
    (Subgroup.mem_centralizer_singleton_iff (G := ↥J) (g := fiveElt) (k := g)).1
      (X0Sub_le_centralizer hM hg)
  rw [← hgp]
  calc fiveElt • (g • w₀) = (fiveElt * g) • w₀ := (mul_smul _ _ _).symm
    _ = (g * fiveElt) • w₀ := by rw [hk]
    _ = g • (fiveElt • w₀) := mul_smul _ _ _
    _ = g • w₀ := by rw [smul_root_of_mem_Hj hM fiveElt_mem_Hj]

theorem hasCommonFixedPt_iff_b (hM : MatFacts) (hstab : ∀ x : J, x • w₀ = w₀ → x ∈ Hj)
    (V : Subgroup J) :
    HasCommonFixedPt V ↔ ∃ y ∈ Subgroup.normalizer (V : Set J), orderOf y = 5 ∧
      (∀ v ∈ V, y * v = v * y → v = 1) ∧ ∃ p ∈ OmV V, y • p = p := by
  constructor
  · rintro ⟨y, hy, hy5, hfpf, g, hVg, hyg⟩
    have hfix : ∀ x ∈ Hj.map (cm g), x • (g • w₀) = g • w₀ := by
      rintro x ⟨h, hh, rfl⟩
      calc cm g h • (g • w₀) = (cm g h * g) • w₀ := (mul_smul _ _ _).symm
        _ = (g * h) • w₀ := by rw [cm_apply, show g * h * g⁻¹ * g = g * h by group]
        _ = g • (h • w₀) := mul_smul _ _ _
        _ = g • w₀ := by rw [smul_root_of_mem_Hj hM hh]
    exact ⟨y, hy, hy5, hfpf, g • w₀, ⟨⟨g, rfl⟩, fun v hv => hfix v (hVg hv)⟩, hfix y hyg⟩
  · rintro ⟨y, hy, hy5, hfpf, p, ⟨⟨g, rfl⟩, hpV⟩, hpy⟩
    have hmem : ∀ x : J, x • (g • w₀) = g • w₀ → x ∈ Hj.map (cm g) := by
      intro x hx
      refine ⟨g⁻¹ * x * g, ?_, by rw [cm_apply]; group⟩
      apply hstab
      calc (g⁻¹ * x * g) • w₀ = g⁻¹ • (x • (g • w₀)) := by
            rw [mul_smul, mul_smul]
        _ = w₀ := by rw [hx, inv_smul_smul]
    exact ⟨y, hy, hy5, hfpf, g, fun v hv => hmem v (hpV v hv), hmem y hpy⟩

theorem d4_fixpt_contra
    {v : ↥J} {p : V2} (hp : p ∈ d4Pts) (hF : FpfX0 (pentSub v))
    (hv : v • toRow p.toVec = toRow p.toVec) : HasCommonFixedPt (pentSub v) := by
  obtain ⟨hPts, hx⟩ := d4_pt_fixed hp
  obtain ⟨-, -, -, hN, h5, hfpf⟩ := hF
  rw [hasCommonFixedPt_iff_b Certificates.certificate4029.basic.mat Certificates.certificate4029.basic.stab]
  refine ⟨fiveElt, hN, h5, hfpf, toRow p.toVec, ⟨hPts, ?_⟩, hx⟩
  have hpow : ∀ i : ℕ, fiveElt ^ i • toRow p.toVec = toRow p.toVec := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', mul_smul, ih, hx]
  have hconj : ∀ i : ℕ, (fiveElt ^ i * v * (fiveElt ^ i)⁻¹) • toRow p.toVec = toRow p.toVec := by
    intro i
    rw [mul_smul, mul_smul, (inv_smul_eq_iff).2 (hpow i).symm, hv, hpow i]
  have hle : pentSub v ≤ MulAction.stabilizer ↥J (toRow p.toVec) := by
    unfold pentSub pentSubAt
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hv
    · simpa using hconj 1
    · exact hconj 2
    · exact hconj 3
  intro x hx'
  exact MulAction.mem_stabilizer_iff.1 (hle hx')

theorem d4_Mx_conj
    {t : ↥J} {T : Array V2} (hT : Mx t = rowsMatrix T) :
    Mx (fiveElt * t * fiveElt⁻¹) = rowsMatrix (d4Conj T) := by
  have hM := Certificates.certificate4029.basic.mat
  unfold d4Conj
  rw [map_mul, map_mul, hT, Mx_fiveElt hM, Mx_fiveElt_inv hM, rowsMatrix_mulRows,
    rowsMatrix_mulRows]

theorem wfRows_d4Conj
    {T : Array V2} (hT : wfRows T = true) : wfRows (d4Conj T) = true :=
  wfRows_mulRows (wfRows_mulRows x0GenRows_zero_wf hT) x0InvRows_zero_wf

theorem d4_eqRows_of_mx {A B : Array V2} (hA : wfRows A = true) (hB : wfRows B = true)
    (h : rowsMatrix A = rowsMatrix B) : eqRows A B = true :=
  eqRows_iff.2 (eq_of_rowsMatrix_eq hA hB h)

theorem d4_mem_pentSub (v : ↥J) :
    v ∈ pentSub v ∧ fiveElt * v * fiveElt⁻¹ ∈ pentSub v ∧
      fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹ ∈ pentSub v ∧
      fiveElt ^ 3 * v * (fiveElt ^ 3)⁻¹ ∈ pentSub v := by
  unfold pentSub pentSubAt
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact Subgroup.subset_closure (by simp)

theorem d4_comm
    {v : ↥J} {T : Array V2} (hF : FpfX0 (pentSub v)) (hTw : wfRows T = true)
    (hT : Mx v = rowsMatrix T) :
    eqRows (mulRows T (d4Conj T)) (mulRows (d4Conj T) T) = true ∧
      eqRows (mulRows T (d4Conj (d4Conj T))) (mulRows (d4Conj (d4Conj T)) T) = true := by
  obtain ⟨-, hab, -⟩ := hF
  obtain ⟨hv0, hv1, hv2, -⟩ := d4_mem_pentSub v
  have hT1w := wfRows_d4Conj hTw
  have hT2w := wfRows_d4Conj hT1w
  have M1 := d4_Mx_conj hT
  have M2 : Mx (fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹) = rowsMatrix (d4Conj (d4Conj T)) := by
    have e2 : fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹ =
        fiveElt * (fiveElt * v * fiveElt⁻¹) * fiveElt⁻¹ := by
      simpa using (conj_pow_succ fiveElt v 1).symm
    rw [e2]
    exact d4_Mx_conj M1
  refine ⟨?_, ?_⟩
  · refine d4_eqRows_of_mx (wfRows_mulRows hTw hT1w) (wfRows_mulRows hT1w hTw) ?_
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hT, ← M1, ← map_mul, ← map_mul,
      hab _ hv0 _ hv1]
  · refine d4_eqRows_of_mx (wfRows_mulRows hTw hT2w) (wfRows_mulRows hT2w hTw) ?_
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hT, ← M2, ← map_mul, ← map_mul,
      hab _ hv0 _ hv2]

theorem d4_S_getD (ts : List (Array V2)) {m : ℕ} (hm : m < 16) :
    ((List.range 16).map (d4Sub ts)).getD m #[] = d4Sub ts m := by
  simp [List.getD_eq_getElem?_getD, hm]

theorem d4_S_mem (ts : List (Array V2)) {s : Array V2} (hs : s ∈ (List.range 16).map (d4Sub ts)) :
    ∃ m < 16, s = d4Sub ts m := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hs
  exact ⟨m, List.mem_range.1 hm, rfl⟩

open scoped Classical in
theorem d4_conj_sound {v k : ↥J} {ts : List (Array V2)} {E : Array (Array V2)} {K : Array V2}
    {V' : Subgroup ↥J} (hF : FpfX0 (pentSub v))
    (hgen : ∀ g ∈ ({v, fiveElt * v * fiveElt⁻¹, fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹,
      fiveElt ^ 3 * v * (fiveElt ^ 3)⁻¹} : Set ↥J), ∃ i < 4, Mx g = rowsMatrix (ts.getD i #[]))
    (hk : Mx k = rowsMatrix K) (hok : d4ConjOK ts E K = true)
    (hV'c : Nat.card V' = 16) (hV' : ∀ u ∈ V', ∃ m < 16, Mx u = rowsMatrix (E[m]!)) :
    pentSub v = V'.map (cm k) := by
  obtain ⟨hF16, -, -, -, -, -⟩ := hF
  unfold d4ConjOK at hok
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at hok
  obtain ⟨⟨h0, hcl⟩, hcj⟩ := hok
  have hid : d4Sub ts 0 = idRows := by
    rw [← d4_S_getD ts (by norm_num : 0 < 16)]
    exact eqRows_iff.1 h0
  have hW : ∀ x ∈ pentSub v, ∃ m < 16, Mx x = rowsMatrix (d4Sub ts m) := by
    have hsub := closure_subset_of_closed
      ({v, fiveElt * v * fiveElt⁻¹, fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹,
        fiveElt ^ 3 * v * (fiveElt ^ 3)⁻¹} : Set ↥J)
      {x | ∃ m < 16, Mx x = rowsMatrix (d4Sub ts m)}
      ⟨0, by norm_num, by rw [hid, map_one, rowsMatrix_idRows]⟩ (by
        rintro x ⟨m, hm, hxm⟩ g hg
        obtain ⟨i, hi, hgi⟩ := hgen g hg
        obtain ⟨s', hs', he⟩ := hcl m hm i hi
        obtain ⟨m', hm', rfl⟩ := d4_S_mem ts hs'
        refine ⟨m', hm', ?_⟩
        rw [map_mul, hxm, hgi, ← rowsMatrix_mulRows, ← d4_S_getD ts hm]
        exact congrArg rowsMatrix (eqRows_iff.1 he))
    intro x hx
    exact hsub hx
  have hU : ∀ u ∈ V'.map (cm k), ∃ m < 16, Mx u = rowsMatrix (d4Sub ts m) := by
    rintro _ ⟨u0, hu0, rfl⟩
    obtain ⟨m, hm, hMu⟩ := hV' u0 hu0
    obtain ⟨s', hs', he⟩ := hcj m hm
    obtain ⟨m', hm', rfl⟩ := d4_S_mem ts hs'
    refine ⟨m', hm', ?_⟩
    have he' : rowsMatrix K * rowsMatrix (E[m]!) = rowsMatrix (d4Sub ts m') * rowsMatrix K := by
      rw [← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 he]
    have hkk : Mx k * Mx k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc Mx (cm k u0) = Mx k * Mx u0 * Mx k⁻¹ := by rw [cm_apply, map_mul, map_mul]
      _ = (rowsMatrix K * rowsMatrix (E[m]!)) * Mx k⁻¹ := by rw [hk, hMu]
      _ = (rowsMatrix (d4Sub ts m') * rowsMatrix K) * Mx k⁻¹ := by rw [he']
      _ = rowsMatrix (d4Sub ts m') * (Mx k * Mx k⁻¹) := by rw [mul_assoc, ← hk]
      _ = rowsMatrix (d4Sub ts m') := by rw [hkk, mul_one]
  let Sfin : Finset (Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
    (Finset.range 16).image fun m => rowsMatrix (d4Sub ts m)
  have hmemS : ∀ x : Matrix (Fin 112) (Fin 112) (ZMod 2),
      (∃ m < 16, x = rowsMatrix (d4Sub ts m)) → x ∈ (↑Sfin : Set _) := by
    rintro x ⟨m, hm, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩)
  refine subgroup_eq_of_images Mx Mx_injective (↑Sfin : Set _) (Finset.finite_toSet _)
    (n := 16) ?_ (fun w hw => ?_) (fun u hu => ?_) hF16 ?_
  · rw [Set.ncard_coe_finset]
    exact (Finset.card_image_le).trans (by simp)
  · obtain ⟨m, hm, h⟩ := hW w hw
    exact hmemS _ ⟨m, hm, h⟩
  · obtain ⟨m, hm, h⟩ := hU u hu
    exact hmemS _ ⟨m, hm, h⟩
  · rw [Subgroup.card_map_of_injective (cm_injective k)]
    exact hV'c

theorem d4_gen_mats
    {v : ↥J} {T : Array V2} (hT : Mx v = rowsMatrix T) :
    ∀ g ∈ ({v, fiveElt * v * fiveElt⁻¹, fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹,
      fiveElt ^ 3 * v * (fiveElt ^ 3)⁻¹} : Set ↥J), ∃ i < 4,
      Mx g = rowsMatrix
        ([T, d4Conj T, d4Conj (d4Conj T), d4Conj (d4Conj (d4Conj T))].getD i #[]) := by
  have M1 := d4_Mx_conj hT
  have e2 : fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹ =
      fiveElt * (fiveElt * v * fiveElt⁻¹) * fiveElt⁻¹ := by
    simpa using (conj_pow_succ fiveElt v 1).symm
  have M2 : Mx (fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹) = rowsMatrix (d4Conj (d4Conj T)) := by
    rw [e2]
    exact d4_Mx_conj M1
  have e3 : fiveElt ^ 3 * v * (fiveElt ^ 3)⁻¹ =
      fiveElt * (fiveElt ^ 2 * v * (fiveElt ^ 2)⁻¹) * fiveElt⁻¹ := by
    simpa using (conj_pow_succ fiveElt v 2).symm
  have M3 : Mx (fiveElt ^ 3 * v * (fiveElt ^ 3)⁻¹) = rowsMatrix (d4Conj (d4Conj (d4Conj T))) := by
    rw [e3]
    exact d4_Mx_conj M2
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨0, by norm_num, hT⟩
  · exact ⟨1, by norm_num, M1⟩
  · exact ⟨2, by norm_num, M2⟩
  · exact ⟨3, by norm_num, M3⟩

theorem d4_pair_sound
    {L : List (Subgroup ↥J)} {wit : List (Nat × Nat × Nat × Nat)}
    {Es : List (Array (Array V2))} {i c : ℕ} {w : List Int}
    (hP : wfRows (wR (d4El w)) = true) (hPi : wfRows (wR (invWord (d4El w))) = true)
    (hetaWf : ∀ c' < 2048, wfRows (etaE c') = true) (hc : c < 2048)
    (hpair : d4PairOK wit Es i c (wR (d4El w)) (wR (invWord (d4El w)))
      (d4Pts.map (frApply (frTable (wR (invWord (d4El w)))))) = true)
    (hE : ∀ j < 2, ∃ V' ∈ L, Nat.card V' = 16 ∧
      ∀ u ∈ V', ∃ m < 16, Mx u = rowsMatrix ((Es.getD j #[])[m]!))
    {v : ↥J} (he : el5 (d4El w) * v * (el5 (d4El w))⁻¹ = eta uJ 11 c)
    (hF : FpfX0 (pentSub v)) (hN : ¬ HasCommonFixedPt (pentSub v)) :
    ∃ V' ∈ L, ∃ g : ↥J, pentSub v = V'.map (cm g) := by
  have hM := Certificates.certificate4029.basic.mat
  have hv : v = (el5 (d4El w))⁻¹ * eta uJ 11 c * el5 (d4El w) := by
    rw [← he]
    group
  have hMv : Mx v = rowsMatrix (mulRows (mulRows (wR (invWord (d4El w))) (etaE c))
      (wR (d4El w))) := by
    rw [hv, map_mul, map_mul, d4_Mx_inv w, Mx_eta hM 11 le_rfl c, Mx_el5 hM,
      rowsMatrix_mulRows, rowsMatrix_mulRows]
    rfl
  have hTw : wfRows (mulRows (mulRows (wR (invWord (d4El w))) (etaE c)) (wR (d4El w))) = true :=
    wfRows_mulRows (wfRows_mulRows hPi (hetaWf c hc)) hP
  unfold d4PairOK at hpair
  rw [Bool.or_eq_true] at hpair
  rcases hpair with hfix | hrest
  · exfalso
    obtain ⟨p', hp', hfp'⟩ := List.any_eq_true.1 hfix
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hp'
    apply hN
    refine d4_fixpt_contra hp hF ?_
    have h1 : el5 (d4El w) • toRow p.toVec =
        toRow (frApply (frTable (wR (invWord (d4El w)))) p).toVec := d4_smul_row (d4_Mx_inv w) p
    have h2 : eta uJ 11 c • toRow (frApply (frTable (wR (invWord (d4El w)))) p).toVec =
        toRow (frApply (frTable (wR (invWord (d4El w)))) p).toVec := by
      rw [d4_eta_smul]
      unfold d4Fix at hfp'
      rw [d4EtaTabs_get hc] at hfp'
      rw [V2.beq_iff.1 hfp']
    calc v • toRow p.toVec
        = ((el5 (d4El w))⁻¹ * eta uJ 11 c * el5 (d4El w)) • toRow p.toVec := by rw [← hv]
      _ = (el5 (d4El w))⁻¹ • (eta uJ 11 c • (el5 (d4El w) • toRow p.toVec)) := by
          rw [mul_smul, mul_smul]
      _ = toRow p.toVec := by rw [h1, h2, ← h1, inv_smul_smul]
  · unfold d4Rest at hrest
    rw [Bool.or_eq_true, Bool.or_eq_true] at hrest
    obtain ⟨hc1, hc2⟩ := d4_comm hF hTw hMv
    rcases hrest with (h | h) | h
    · rw [hc1] at h
      exact absurd h (by simp)
    · rw [hc2] at h
      exact absurd h (by simp)
    · cases hf : wit.find? (fun w => w.1 == i && w.2.1 == c) with
      | none =>
        rw [hf] at h
        exact absurd h (by simp)
      | some w' =>
        rw [hf] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hj, hn⟩, hok⟩ := h
        obtain ⟨k, -, hk⟩ := mem_X0Sub_of_lt hM w'.2.2.2 hn
        obtain ⟨V', hV', hV'c, hV'm⟩ := hE w'.2.2.1 hj
        exact ⟨V', hV', k, d4_conj_sound hF (d4_gen_mats hMv) hk hok hV'c hV'm⟩

theorem d4_tables
    (hg0 : Dec2.chkGrp b1344Words = true) (hg1 : Dec2.chkGrp a85Words = true) :
    ∀ j < 2, ∃ V' ∈ [B1344, A85], Nat.card V' = 16 ∧
      ∀ u ∈ V', ∃ m < 16,
        Mx u = rowsMatrix ((([b1344Words, a85Words].map Dec2.eTab).getD j #[])[m]!) := by
  have hM := Certificates.certificate4029.basic.mat
  intro j hj
  interval_cases j
  · refine ⟨B1344, by simp, Dec2.card_Vgrp_b hM hg0, fun u hu => ?_⟩
    obtain ⟨m, hm, rfl⟩ := Dec2.Vgrp_subset_b hM hg0 u hu
    exact ⟨m, hm, Dec2.Mx_eEl_b hM hm⟩
  · refine ⟨A85, by simp, Dec2.card_Vgrp_b hM hg1, fun u hu => ?_⟩
    obtain ⟨m, hm, rfl⟩ := Dec2.Vgrp_subset_b hM hg1 u hu
    exact ⟨m, hm, Dec2.Mx_eEl_b hM hm⟩

theorem d4_sound
    (hg0 : Dec2.chkGrp b1344Words = true) (hg1 : Dec2.chkGrp a85Words = true)
    (hchk : chkD4 d4Reps d4Words d4Wit [b1344Words, a85Words] = true) :
    ∀ (q : Row) (v : ↥J), q ∈ {q : Row | ∃ w ∈ d4Reps.toList, q = toRow w.toVec} →
      PentCand q v → FpfX0 (pentSub v) → ¬ HasCommonFixedPt (pentSub v) →
      ∃ V' ∈ [B1344, A85], ∃ g : ↥J, pentSub v = V'.map (cm g) := by
  rintro q v ⟨r, hr, rfl⟩ ⟨-, hv1, -, hR, -, hfix⟩ hF hN
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.1 hr
  have hi' : i < d4Reps.size := by simpa using hi
  have hri : d4Reps[i]! = r := by
    rw [getElem!_pos d4Reps i hi']
    simpa using hir
  unfold chkD4 at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hetaWf⟩, hall⟩ := hchk
  have hrep := hall i hi'
  unfold d4RepOK at hrep
  rw [hri] at hrep
  simp only [Bool.and_eq_true, List.all_eq_true] at hrep
  obtain ⟨⟨⟨⟨-, hP⟩, hPi⟩, hroot⟩, hpairs⟩ := hrep
  obtain ⟨c, hcmem, he⟩ := d4_estab_of_pent hPi (fun c hc => by simpa using hetaWf c hc) hroot hv1
    hR hfix
  have hc : c < 2048 := by
    have h := hcmem
    unfold d4Estab at h
    exact List.mem_range.1 (List.mem_filter.1 h).1
  exact d4_pair_sound hP hPi (fun c' hc' => by simpa using hetaWf c' hc') hc (hpairs c hcmem)
    (d4_tables hg0 hg1) he hF hN

end CFSG.QuasithinUnique.A5
