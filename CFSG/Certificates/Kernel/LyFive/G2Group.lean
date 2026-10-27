module

public import CFSG.Certificates.Kernel.LyFive.G2Count
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Sporadic.Schreier.LySevenProofBase

public section

namespace CFSG.KS.LyFive.G2

open CFSG.KC.LyG2 CFSG.KC.Enum CFSG.KS.SporSch.LySev CFSG.KS.SporSch.LySvC
open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open Matrix

theorem lit_e1 : (1048576 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 1) := by decide
theorem lit_e2 : (1099511627776 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 2) := by decide
theorem lit_e3 : (1152921504606846976 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 3) := by decide
theorem lit_e4 : (1208925819614629174706176 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 4) := by decide
theorem lit_e5 : (1267650600228229401496703205376 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 5) := by decide
theorem lit_e6 : (1329227995784915872903807060280344576 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 6) := by
  decide
theorem lit_e0 : (1 : ℕ) = Nat.shiftLeft 1 (Nat.mul 20 0) := by decide

theorem invChk_spec {cols ui : List ℕ} (hc : ∀ x ∈ cols, Can x) (hl : cols.length ≤ 7)
    (hu : ∀ x ∈ ui, Can x) (h : invChk cols ui = true) : colM ui * colM cols = 1 := by
  apply mul_eq_one_comm.1
  change bAnd(Nat.beq (mvL cols (getL ui 0)) 1, bAnd(Nat.beq (mvL cols (getL ui 1)) 1048576,
    bAnd(Nat.beq (mvL cols (getL ui 2)) 1099511627776,
    bAnd(Nat.beq (mvL cols (getL ui 3)) 1152921504606846976,
    bAnd(Nat.beq (mvL cols (getL ui 4)) 1208925819614629174706176,
    bAnd(Nat.beq (mvL cols (getL ui 5)) 1267650600228229401496703205376,
      Nat.beq (mvL cols (getL ui 6)) 1329227995784915872903807060280344576)))))) = true at h
  simp only [CFSG.KS.SporSch.LyLoop.bAnd_eqP, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  have key : ∀ t : Fin 7, mvL cols (getL ui t.val) = Nat.shiftLeft 1 (Nat.mul 20 t.val) := by
    intro t
    match t with
    | ⟨0, _⟩ => rw [h0]; exact lit_e0
    | ⟨1, _⟩ => rw [h1]; exact lit_e1
    | ⟨2, _⟩ => rw [h2]; exact lit_e2
    | ⟨3, _⟩ => rw [h3]; exact lit_e3
    | ⟨4, _⟩ => rw [h4]; exact lit_e4
    | ⟨5, _⟩ => rw [h5]; exact lit_e5
    | ⟨6, _⟩ => rw [h6]; exact lit_e6
  ext r t
  have e := congrFun (mvL_spec hc hl (can_getL hu t.val)).2 r
  rw [key, dv_e] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  have : (colM cols *ᵥ dv (getL ui t.val)) r = ∑ x, colM cols r x * colM ui x t := by
    rw [Matrix.mulVec, dotProduct]
    rfl
  rw [← this, ← e, Pi.single_apply]

theorem colM_mulVec_single (cols : List ℕ) (i : Fin 7) : colM cols *ᵥ Pi.single i 1 = dv (getL cols i.val) := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem isAut_of_autChk {CC : List (List ℕ)} (hCC : TabOK CC) {g : List ℕ} (hg : ∀ x ∈ g, Can x)
    (hl : g.length ≤ 7) (h : autChk CC g = true) : IsAut (ccOf CC) (colM g) := by
  apply isAut_of_basis
  intro i j
  have h1 := CFSG.KS.allN_spec h (7 * i.val + j.val)
    (by change 7 * i.val + j.val < 49; have := i.isLt; have := j.isLt; omega)
  rw [nmod_eq, ndiv_eq, show (7 * i.val + j.val) % 7 = j.val by omega,
    show (7 * i.val + j.val) / 7 = i.val by omega, Nat.beq_eq] at h1
  have hrow : Can (getL (getLL CC i.val) j.val) := by
    rw [getLL_eq]
    by_cases hi : i.val < CC.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact can_getL (hCC.2 _ (List.getElem_mem hi)).2 j.val
    · rw [List.getD_eq_default _ _ (by omega)]
      exact can_getL (fun x hx => absurd hx List.not_mem_nil) j.val
  have e1 := (mvL_spec hg hl hrow).2
  have e2 := (crs_spec hCC (can_getL hg i.val) (can_getL hg j.val)).2
  rw [h1] at e1
  rw [colM_mulVec_single, colM_mulVec_single, ← e2, e1]
  rfl

theorem arr_get! (R : List ℕ) (k : ℕ) : (⟨R⟩ : Array ℕ)[k]! = R.getD k 0 := by
  by_cases h : k < R.length
  · rw [getElem!_pos (⟨R⟩ : Array ℕ) k (by simpa using h), List.getD_eq_getElem _ _ h]
    rfl
  · rw [getElem!_neg (⟨R⟩ : Array ℕ) k (by simpa using h), List.getD_eq_default _ _ (by omega)]
    rfl

theorem packCol_eq (R : List ℕ) (j : ℕ) :
    packCol R j = laneSum (fun L => getL R (7 * L + j)) 7 := by
  unfold packCol laneSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, shl_eq, Nat.add_eq]
  norm_num
  ring_nf

theorem can_packCol {R : List ℕ} (hR : ∀ x ∈ R, x < 5) (j : ℕ) : Can (packCol R j) := by
  rw [packCol_eq]
  refine can_laneSum fun L _ => ?_
  rw [getL_eq]
  by_cases h : 7 * L + j < R.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hR _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem colM_packCols {R : List ℕ} (hR : ∀ x ∈ R, x < 5) : colM (packCols R) = mat7 ⟨R⟩ := by
  ext r t
  have hlt : ∀ L < 7, getL R (7 * L + t.val) < 2 ^ 20 := by
    intro L _
    rw [getL_eq]
    by_cases h : 7 * L + t.val < R.length
    · rw [List.getD_eq_getElem _ _ h]
      have := hR _ (List.getElem_mem h)
      omega
    · rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  have e : getL (packCols R) t.val = packCol R t.val := by
    rw [getL_eq]
    unfold packCols
    obtain ⟨k, hk⟩ := t
    simp only
    interval_cases k <;> simp only [List.getD_cons_succ, List.getD_cons_zero]
  simp only [colM, of_apply, mat7]
  rw [e, packCol_eq, dv_laneSum hlt, getL_eq, arr_get!]

theorem packCols_ok {R : List ℕ} (hR : ∀ x ∈ R, x < 5) :
    (packCols R).length ≤ 7 ∧ ∀ x ∈ packCols R, Can x := by
  refine ⟨le_of_eq rfl, ?_⟩
  unfold packCols
  exact List.forall_mem_cons.2 ⟨can_packCol hR 0, List.forall_mem_cons.2 ⟨can_packCol hR 1,
    List.forall_mem_cons.2 ⟨can_packCol hR 2, List.forall_mem_cons.2 ⟨can_packCol hR 3,
    List.forall_mem_cons.2 ⟨can_packCol hR 4, List.forall_mem_cons.2 ⟨can_packCol hR 5,
    List.forall_mem_cons.2 ⟨can_packCol hR 6, fun x hx => absurd hx List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩

@[expose] noncomputable def gM (j : ℕ) : M := mat7 (hGenPairs asArr)[j]!.1

@[expose] noncomputable def gMi (j : ℕ) : M := mat7 (hGenPairs asArr)[j]!.2

@[expose] def G7 : Subgroup (M)ˣ := Subgroup.closure {u | ∃ j < 5, (u : M) = gM j}

theorem gM_mul {j : ℕ} (hj : j < 5) : gM j * gMi j = 1 := by
  have hinv := sevenFacts.hpInv (hGenPairs asArr)[j]! (by
    rw [getElem!_pos (hGenPairs asArr) j (by rw [hGenPairs_size]; exact hj)]
    exact Array.getElem_mem _)
  have e := congrArg mat7 hinv
  rw [mat7_mul7, mat7_id7] at e
  exact e

@[expose] noncomputable def uG (j : ℕ) (hj : j < 5) : (M)ˣ :=
  ⟨gM j, gMi j, gM_mul hj, mul_eq_one_comm.1 (gM_mul hj)⟩

theorem uG_mem (j : ℕ) (hj : j < 5) : uG j hj ∈ G7 :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem genArr_eq {j : ℕ} (hj : j < 5) : genArr j = (hGenPairs asArr)[j]!.1 := by
  rw [hGenPairs_get hj]

@[expose] def dagGensOK : Bool := hDag.toList.all fun e => e.1 != 0 || decide (e.2.1 < 5)

theorem dagGensOK_eq : dagGensOK = true := by decide

theorem dag_gen_lt {k : ℕ} (hk : k < hDag.size) (h0 : hDag[k]!.1 = 0) : hDag[k]!.2.1 < 5 := by
  have h := List.all_eq_true.1 dagGensOK_eq hDag[k]! (by
    rw [getElem!_pos hDag k hk, Array.mem_toList_iff]
    exact Array.getElem_mem hk)
  simp only [h0, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at h
  exact h

theorem mat7_valsArr_mem :
    ∀ k < hDag.size, ∃ u ∈ G7, (u : M) = mat7 valsArr[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [dag_local k hk]
    split_ifs with h0 h1
    · have h5 : hDag[k]!.2.1 < 5 := dag_gen_lt hk h0
      exact ⟨uG _ h5, uG_mem _ h5, by rw [genArr_eq h5]; rfl⟩
    · rcases sevenFacts.dagOrder k hk with h | h
      · exact absurd h h0
      · obtain ⟨u, hu, e⟩ := ih _ h.1 (by omega)
        refine ⟨u⁻¹, G7.inv_mem hu, ?_⟩
        have hinv := dag_inv k hk h1
        rw [dag_local k hk, if_neg h0, if_pos h1, getD_valsArr (by omega)] at hinv
        rw [getD_valsArr (by omega)]
        have e2 := congrArg mat7 hinv
        rw [mat7_mul7, mat7_id7, ← e] at e2
        have e3 : ((u⁻¹ : (M)ˣ) : M) = mat7 (inv7 valsArr[hDag[k]!.2.1]!) := by
          calc ((u⁻¹ : (M)ˣ) : M) = ((u⁻¹ : (M)ˣ) : M) * ((u : M) * mat7 (inv7 valsArr[hDag[k]!.2.1]!)) := by
                rw [e2, Matrix.mul_one]
            _ = mat7 (inv7 valsArr[hDag[k]!.2.1]!) := by
                rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        exact e3
    · rcases sevenFacts.dagOrder k hk with h | h
      · exact absurd h h0
      · have h2 := h.2.resolve_left h1
        obtain ⟨u, hu, e⟩ := ih _ h.1 (by omega)
        obtain ⟨v, hv, e'⟩ := ih _ h2 (by omega)
        refine ⟨u * v, G7.mul_mem hu hv, ?_⟩
        rw [getD_valsArr (by omega), getD_valsArr (by omega), mat7_mul7, Units.val_mul, e, e']

theorem mat7_lvArr_mem {i : ℕ} {R : Array ℕ} (hR : R ∈ lvArr i) :
    ∃ u ∈ G7, (u : M) = mat7 R := by
  rw [lvArr, List.mem_toArray, List.mem_map] at hR
  obtain ⟨m, -, rfl⟩ := hR
  by_cases hm : m < hDag.size
  · rw [getD_valsArr hm]
    exact mat7_valsArr_mem m hm
  · refine ⟨1, G7.one_mem, ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
      rw [sevenFacts.valsSize]; omega), Option.getD_none, mat7_id7, Units.val_one]

theorem level_witness7 (i : ℕ) (hfix : ∀ R ∈ lvArr i, ∀ l < i,
      mat7 R *ᵥ toVec7 (stdVec l) = toVec7 (stdVec l))
    (htree : vecTreeOK (stdVec i) (lvArr i) (vecBFS (stdVec i) (lvArr i)) = true) :
    ∀ k < (vecBFS (stdVec i) (lvArr i)).1.size, ∃ g ∈ G7,
      (∀ l < i, g • toVec7 (stdVec l) = toVec7 (stdVec l)) ∧
      g • toVec7 (stdVec i) = toVec7 ((vecBFS (stdVec i) (lvArr i)).1[k]!) := by
  obtain ⟨h0, -, hstep, -⟩ := vecTree_parts htree
  set T := vecBFS (stdVec i) (lvArr i)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, G7.one_mem, fun l _ => one_smul _ _, by rw [h0, one_smul]⟩
    · obtain ⟨hp, hl, he⟩ := hstep k hpos hk
      obtain ⟨g, hg, hgfix, hgv⟩ := ih _ hp (by omega)
      have hR : (lvArr i)[T.2.2[k]!]! ∈ lvArr i := by
        rw [getElem!_pos (lvArr i) T.2.2[k]! hl]; exact Array.getElem_mem hl
      obtain ⟨u, hu, hum⟩ := mat7_lvArr_mem hR
      refine ⟨u * g, G7.mul_mem hu hg, fun l hli => ?_, ?_⟩
      · rw [mul_smul, hgfix l hli, Units.smul_def]
        change (u : M) *ᵥ _ = _
        rw [hum]
        exact hfix _ hR l hli
      · rw [mul_smul, hgv, Units.smul_def]
        change (u : M) *ᵥ _ = _
        rw [hum, ← toVec7_mv7, he]

theorem card_G7_ge : 5859000000 ≤ Nat.card G7 := by
  have hfix : ∀ i < 3, ∀ R ∈ lvArr i, ∀ l < i,
      mat7 R *ᵥ toVec7 (stdVec l) = toVec7 (stdVec l) := by
    intro i hi
    interval_cases i
    · intro R _ l hl; omega
    · exact levelFix_parts 1 sevenFacts.fix1
    · exact levelFix_parts 2 sevenFacts.fix2
  have htree : ∀ i < 3, vecTreeOK (stdVec i) (lvArr i) (vecBFS (stdVec i) (lvArr i)) = true := by
    intro i hi
    interval_cases i
    · exact sevenFacts.tree0
    · exact sevenFacts.tree1
    · exact sevenFacts.tree2
  have h := prod_card_le_card_of_witnesses G7 (fun i => toVec7 (stdVec i)) 3
    (fun i => (Finset.range (vecBFS (stdVec i) (lvArr i)).1.size).image
      fun k => toVec7 ((vecBFS (stdVec i) (lvArr i)).1[k]!))
    (fun i hi y hy => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
      exact level_witness7 i (hfix i hi) (htree i hi) k (Finset.mem_range.1 hk))
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, card_level 0 (htree 0 (by norm_num)),
    card_level 1 (htree 1 (by norm_num)), card_level 2 (htree 2 (by norm_num)),
    sevenFacts.size0, sevenFacts.size1, sevenFacts.size2] at h
  norm_num at h
  exact h

end CFSG.KS.LyFive.G2

end
