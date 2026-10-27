module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1B7Native
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.J4.QT2AMod
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QT2LocCntProofBase
public import CFSG.Sporadic.J4.QT2LocFiveProofBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.A5.B7

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.Sporadic.J4.QT2.B7 CFSG.Sporadic.J4.QT2A Matrix

theorem Mx_inv_rows {x : J} {X Xi : Array V2} (hx : Mx x = rowsMatrix X)
    (h : eqRows (mulRows X Xi) idRows = true) : Mx x⁻¹ = rowsMatrix Xi := by
  have h1 : rowsMatrix X * rowsMatrix Xi = 1 := by
    have := congrArg rowsMatrix (eqRows_iff.1 h)
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have h2 : Mx x⁻¹ * Mx x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc Mx x⁻¹ = Mx x⁻¹ * (rowsMatrix X * rowsMatrix Xi) := by rw [h1, mul_one]
    _ = (Mx x⁻¹ * Mx x) * rowsMatrix Xi := by rw [hx, mul_assoc]
    _ = rowsMatrix Xi := by rw [h2, one_mul]

theorem smul_toRow_rows {x : J} {Xi : Array V2} (hx : Mx x⁻¹ = rowsMatrix Xi) (v : V2) :
    x • toRow v.toVec = toRow (frApply (frTable Xi) v).toVec := by
  rw [← ofRow_inj, smul_row, frApply_toVec_eq_vecMul, ← hx]
  rfl

theorem smul_fix_of_apply {x : J} {X : Array V2} (hx : Mx x = rowsMatrix X) (v : V2)
    (h : (frApply (frTable X) v).toVec = v.toVec) : x • toRow v.toVec = toRow v.toVec := by
  have h' : v.toVec ᵥ* Mx x = v.toVec := by
    rw [hx, ← frApply_toVec_eq_vecMul]
    exact h
  rw [← ofRow_inj, smul_row]
  show v.toVec ᵥ* Mx x⁻¹ = v.toVec
  conv_lhs => rw [← h']
  rw [Matrix.vecMul_vecMul, ← map_mul, mul_inv_cancel, map_one, Matrix.vecMul_one]

theorem toVec_eq_of_differs_false {a b : V2} (h : differs a b = false) : a.toVec = b.toVec := by
  unfold differs at h
  simp only [List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, not_not] at h
  funext j
  rw [V2.toVec_apply, V2.toVec_apply, h j.val j.isLt]

theorem differs_false_of_toVec_eq {a b : V2} (e : a.toVec = b.toVec) : differs a b = false := by
  by_contra h
  exact differs_toVec (by simpa using h) e

theorem rowsMatrix_ne_one_of_neId {M : Array V2} (h : neId M = true) : rowsMatrix M ≠ 1 := by
  intro e
  unfold neId at h
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨i, hi, hd⟩ := h
  apply differs_toVec hd
  funext j
  have := congrFun (congrFun e ⟨i, hi⟩) j
  rw [← rowsMatrix_idRows] at this
  rw [rowsMatrix_apply, rowsMatrix_apply] at this
  exact this

theorem Mx_eta_of {u : ℕ → J} {T : Array (Array V2)} {n : ℕ}
    (hu : ∀ j < n, Mx (u j) = rowsMatrix (T[j]?.getD idRows)) :
    ∀ m ≤ n, ∀ c, Mx (eta u m c) = rowsMatrix (etaRows T m c)
  | 0, _, c => by simp [eta, etaRows, rowsMatrix_idRows]
  | m + 1, hm, c => by
    rw [eta_succ, etaRows_succ, map_mul]
    split_ifs with h
    · rw [Mx_eta_of hu m (by omega) c, hu m (by omega), rowsMatrix_mulRows]
    · rw [map_one, Mx_eta_of hu m (by omega) c, mul_one]

theorem etaTab_get {c : ℕ} (hc : c < 2048) : etaTab[c]! = etaRows uRows 11 c := by
  rw [etaTab, getElem!_pos _ c (by simpa using hc), Array.getElem_map, Array.getElem_range]

@[expose] noncomputable def vEl (t : J) : ℕ → J
  | 0 => t
  | j + 1 => fiveElt * vEl t j * fiveElt⁻¹

theorem vRows_zero (T0 : Array V2) : (vRows T0)[0]?.getD idRows = T0 := rfl

theorem vRows_one (T0 : Array V2) : (vRows T0)[1]?.getD idRows = conjXi T0 := rfl

theorem vRows_two (T0 : Array V2) : (vRows T0)[2]?.getD idRows = conjXi (conjXi T0) := rfl

theorem vRows_three (T0 : Array V2) :
    (vRows T0)[3]?.getD idRows = conjXi (conjXi (conjXi T0)) := rfl

theorem vRows_size (T0 : Array V2) : (vRows T0).size = 4 := rfl

theorem Mx_vEl {t : J} {T0 : Array V2} (hξ : Mx fiveElt = rowsMatrix fiveRows)
    (hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv) (hT : Mx t = rowsMatrix T0) :
    ∀ j < 4, Mx (vEl t j) = rowsMatrix ((vRows T0)[j]?.getD idRows) := by
  have hc : ∀ {y : J} {Y : Array V2}, Mx y = rowsMatrix Y →
      Mx (fiveElt * y * fiveElt⁻¹) = rowsMatrix (conjXi Y) := by
    intro y Y hy
    rw [map_mul, map_mul, hξ, hξi, hy, conjXi, rowsMatrix_mulRows, rowsMatrix_mulRows]
  intro j hj
  interval_cases j
  · rw [vRows_zero]; exact hT
  · rw [vRows_one]; exact hc hT
  · rw [vRows_two]; exact hc (hc hT)
  · rw [vRows_three]; exact hc (hc (hc hT))

theorem chkB7V_parts {T0 : Array V2} {g0w : List Int} {c0 : ℕ} (h : chkB7V T0 g0w c0 = true) :
    eqRows (mulRows fiveRows xiInv) idRows = true ∧
    (∀ i < 4, eqRows (mulRows ((vRows T0)[i]?.getD idRows) ((vRows T0)[i]?.getD idRows))
      idRows = true) ∧
    (∀ i < 4, ∀ j < 4, eqRows (mulRows ((vRows T0)[i]?.getD idRows) ((vRows T0)[j]?.getD idRows))
      (mulRows ((vRows T0)[j]?.getD idRows) ((vRows T0)[i]?.getD idRows)) = true) ∧
    eqRows (conjXi ((vRows T0)[3]?.getD idRows)) (prodRows (vRows T0) 15) = true ∧
    differs (frApply (frTable ((vRows T0)[0]?.getD idRows)) rootV) rootV = false ∧
    eqRows (mulRows (wR g0w) (invRows (wR g0w))) idRows = true ∧ c0 ∈ tMasks ∧ c0 < 2048 ∧
    eqRows (mulRows (mulRows (invRows (wR g0w)) ((vRows T0)[0]?.getD idRows)) (wR g0w))
      etaTab[c0]! = true := by
  unfold chkB7V at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

structure B7Facts (t g0 : J) (c0 : ℕ) : Prop where
  elem : Elem (vEl t) 4
  norm : fiveElt * vEl t 3 * fiveElt⁻¹ = eta (vEl t) 4 15
  fix : t • w₀ = w₀
  conj : t = g0 * eta uJ 11 c0 * g0⁻¹
  mask : c0 ∈ tMasks

theorem b7Facts_of_chk (hM : MatFacts) {t : J} {T0 : Array V2} (hT : Mx t = rowsMatrix T0)
    {g0w : List Int} {c0 : ℕ} (h : chkB7V T0 g0w c0 = true) :
    Mx fiveElt⁻¹ = rowsMatrix xiInv ∧ Mx (el5 g0w)⁻¹ = rowsMatrix (invRows (wR g0w)) ∧
      B7Facts t (el5 g0w) c0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chkB7V_parts h
  have hξ : Mx fiveElt = rowsMatrix fiveRows := Mx_wordProd hM fiveWord
  have hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv := Mx_inv_rows hξ h1
  have hV := Mx_vEl hξ hξi hT
  have hg0 : Mx (el5 g0w) = rowsMatrix (wR g0w) := Mx_el5 hM g0w
  have hg0i : Mx (el5 g0w)⁻¹ = rowsMatrix (invRows (wR g0w)) := Mx_inv_rows hg0 h6
  rw [vRows_zero] at h5 h9
  refine ⟨hξi, hg0i, ⟨⟨fun j hj => ?_, fun i hi j hj => ?_⟩, ?_, ?_, ?_, h7⟩⟩
  · apply Mx_injective
    rw [map_mul, hV j hj, map_one, ← rowsMatrix_mulRows, eqRows_iff.1 (h2 j hj),
      rowsMatrix_idRows]
  · apply Mx_injective
    rw [map_mul, map_mul, hV i hi, hV j hj, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
      eqRows_iff.1 (h3 i hi j hj)]
  · apply Mx_injective
    have hc : Mx (fiveElt * vEl t 3 * fiveElt⁻¹) =
        rowsMatrix (conjXi ((vRows T0)[3]?.getD idRows)) := by
      rw [map_mul, map_mul, hξ, hξi, hV 3 (by norm_num), conjXi, rowsMatrix_mulRows,
        rowsMatrix_mulRows]
    rw [hc, Mx_eta_of hV 4 le_rfl 15, eqRows_iff.1 h4]
    rfl
  · exact smul_fix_of_apply hT rootV (toVec_eq_of_differs_false h5)
  · have hc0 : Mx (eta uJ 11 c0) = rowsMatrix (etaRows uRows 11 c0) := Mx_eta hM 11 le_rfl c0
    have h10 : (el5 g0w)⁻¹ * t * el5 g0w = eta uJ 11 c0 := by
      apply Mx_injective
      rw [map_mul, map_mul, hg0i, hT, hg0, hc0, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
        eqRows_iff.1 h9, etaTab_get h8]
    rw [← h10]
    group

theorem acts_of_actTabOK
    (hM : MatFacts) {x : J} {Mq Mqi : Array V2} (hx : Mx x = rowsMatrix Mq)
    (hxi : Mx x⁻¹ = rowsMatrix Mqi) {t : List ℕ} (h : actTabOK Mq Mqi t = true) : Acts x t := by
  unfold actTabOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hlen, hj⟩ := h
  have hl : lenOK t = true := by
    refine lenOK_of hlen fun y hy => ?_
    obtain ⟨j, hjl, rfl⟩ := List.getElem_of_mem hy
    have := (hj j (by omega)).1
    rwa [List.getD_eq_getElem _ _ hjl] at this
  refine ⟨hl, fun c hc => ?_⟩
  have hx11 : ∀ j < 11, x * uJ j * x⁻¹ = eta uJ 11 (t.getD j 0) := by
    intro j hjl
    obtain ⟨hlt, heq⟩ := hj j hjl
    apply Mx_injective
    rw [map_mul, map_mul, hx, hxi, Mx_uJ hM hjl, Mx_eta hM 11 le_rfl, ← rowsMatrix_mulRows,
      ← rowsMatrix_mulRows]
    change rowsMatrix (mulRows (mulRows Mq (uRows[j]?.getD idRows)) Mqi) =
      rowsMatrix (etaRows uRows 11 (t.getD j 0))
    rw [eqRows_iff.1 heq, etaTab_get hlt]
  exact conj_eta (elem_uJ hM) x (fun j => t.getD j 0) hx11 (le_refl 11) c

theorem fixedBy_of_fix {t : J} {T0 : Array V2} (hξ : Mx fiveElt = rowsMatrix fiveRows)
    (hξi : Mx fiveElt⁻¹ = rowsMatrix xiInv) (hT : Mx t = rowsMatrix T0)
    (hsq : ∀ j < 4, vEl t j * vEl t j = 1) {qv : V2}
    (hfix : ∀ j < 4, vEl t j • toRow qv.toVec = toRow qv.toVec) :
    fixedBy ((vRows T0).map frTable) qv = true := by
  have hV := Mx_vEl hξ hξi hT
  unfold fixedBy
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true']
  intro j hj
  have hget : (((vRows T0).map frTable)[j]?.getD #[]) = frTable ((vRows T0)[j]?.getD idRows) := by
    have hs : j < (vRows T0).size := by rw [vRows_size]; exact hj
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hs]
    simp
  rw [hget]
  apply differs_false_of_toVec_eq
  rw [frApply_toVec_eq_vecMul, ← hV j hj]
  have h1 := hfix j hj
  rw [← ofRow_inj, smul_row] at h1
  have hinv : (vEl t j)⁻¹ = vEl t j := inv_eq_of_mul_eq_one_right (hsq j hj)
  rw [hinv] at h1
  exact h1

theorem normalizer_of_conj_maps {G : Type*} [Group G] [Finite G] (V : Subgroup G) (x : G)
    (h : ∀ v ∈ V, x * v * x⁻¹ ∈ V) : x ∈ Subgroup.normalizer (V : Set G) := by
  have hpow : ∀ k : ℕ, ∀ v ∈ V, x ^ k * v * (x ^ k)⁻¹ ∈ V := by
    intro k
    induction k with
    | zero => intro v hv; simp [hv]
    | succ k ih =>
      intro v hv
      have h1 := h _ (ih v hv)
      have e : x ^ (k + 1) * v * (x ^ (k + 1))⁻¹ = x * (x ^ k * v * (x ^ k)⁻¹) * x⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨h v, fun hv => ?_⟩
  have hN : 0 < orderOf x := orderOf_pos x
  have h1 := hpow (orderOf x - 1) _ hv
  have e : x ^ (orderOf x - 1) * (x * v * x⁻¹) * (x ^ (orderOf x - 1))⁻¹ = v := by
    have hx : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hN, pow_orderOf_eq_one]
    have hx' : x ^ (orderOf x - 1) = x⁻¹ := eq_inv_of_mul_eq_one_left hx
    rw [hx']
    group
  rwa [e] at h1

end CFSG.QuasithinUnique.A5.B7
