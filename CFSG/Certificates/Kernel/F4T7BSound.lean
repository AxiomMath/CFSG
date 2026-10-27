module

public import CFSG.Certificates.Kernel.F4T7BList
import all CFSG.Fischer.F4
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.ChecksT7

public section

namespace CFSG.KC.F4T7B

open CFSG.Fischer CFSG.KC.F4M3B CFSG.RankThree.PartTwo.Sec10.KS1012GL34
  CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

@[expose] def tt (i : Fin 6) (A : M3) (k j : Fin 6) : Bool := isMultL (mulV A (ptL i k)) (ptL i j)

@[expose] def tabF (t : Fin 6 → Fin 6 → Bool) : List (List Bool) :=
  (List.finRange 6).map fun k => (List.finRange 6).map (t k)

@[expose] def oc (i k : Fin 6) : Pt := (omC i.val).getD k.val (0, 0, 0)

theorem omC_eq (i : Fin 6) : omC i.val = (List.finRange 6).map (oc i) := by
  revert i
  decide

theorem oc_ok (i k : Fin 6) : PtOK (oc i k) := by
  unfold PtOK
  revert i k
  decide

theorem ptOf_oc (i k : Fin 6) : ptOf (oc i k) = ptL i k := by
  revert i k
  decide

theorem mulOf_img (A : M3) (u v : Pt) (hu : PtOK u) (hv : PtOK v) :
    mulOf boolOps (img boolOps (bits A) u) v = isMultL (mulV A (ptOf u)) (ptOf v) := by
  rw [img_bits A u hu, mulOf_vb _ v hv]
  rfl

theorem mtab_bits (i : Fin 6) (A : M3) :
    mtab boolOps (bits A) (omC i.val) = tabF (tt i A) := by
  rw [omC_eq]
  simp only [mtab, tabF, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro k _
  apply List.map_congr_left
  intro j _
  rw [mulOf_img A _ _ (oc_ok i k) (oc_ok i j), ptOf_oc, ptOf_oc]
  rfl

theorem zr_bool : zr boolOps = false := rfl

theorem tabF_getD (t : Fin 6 → Fin 6 → Bool) (k j : Nat) (hk : k < 6) (hj : j < 6) :
    ((tabF t).getD k []).getD j false = t ⟨k, hk⟩ ⟨j, hj⟩ := by
  interval_cases k <;> interval_cases j <;> rfl

theorem f4_cancel : ∀ c ∈ NZL, ∀ c' ∈ NZL, ∃ d ∈ NZL, ∀ x y : F4, c * x = c' * y → x = d * y := by
  decide

theorem isMultL_trans {w u v : V3} (h1 : isMultL w u = true) (h2 : isMultL w v = true) :
    isMultL u v = true := by
  obtain ⟨c, hc, hw⟩ := List.any_eq_true.1 h1
  obtain ⟨c', hc', hw'⟩ := List.any_eq_true.1 h2
  have he : smulV c u = smulV c' v := (of_decide_eq_true hw).symm.trans (of_decide_eq_true hw')
  obtain ⟨d, hd, H⟩ := f4_cancel c hc c' hc'
  refine List.any_eq_true.2 ⟨d, hd, decide_eq_true ?_⟩
  obtain ⟨ux, uy, uz⟩ := u
  simp only [smulV, V3.mk.injEq] at he ⊢
  exact ⟨H _ _ he.1, H _ _ he.2.1, H _ _ he.2.2⟩

theorem ptL_inj : ∀ i j j' : Fin 6, isMultL (ptL i j) (ptL i j') = true → j = j' := by
  decide

theorem tt_unique {i : Fin 6} {A : M3} {k j j' : Fin 6} (h : tt i A k j = true)
    (h' : tt i A k j' = true) : j = j' :=
  ptL_inj i j j' (isMultL_trans h h')

theorem idxL_eq (i : Fin 6) (A : M3) (k : Fin 6) :
    idxL i A k = ((List.finRange 6).find? fun j => tt i A k j).getD 0 := rfl

theorem idxL_spec {i : Fin 6} {A : M3} {k j : Fin 6} (h : tt i A k j = true) : idxL i A k = j := by
  rw [idxL_eq]
  cases hf : (List.finRange 6).find? fun j => tt i A k j with
  | none => exact absurd h (List.find?_eq_none.1 hf j (List.mem_finRange j))
  | some a => exact tt_unique (List.find?_some hf) h

theorem stabT_tabF {t : Fin 6 → Fin 6 → Bool} (h : stabT boolOps (tabF t) = true) (k : Fin 6) :
    ∃ j, t k j = true := by
  rw [stabT, andL_bool, List.all_eq_true] at h
  have h1 := h (orL boolOps ((List.finRange 6).map (t k)))
    (List.mem_map.2 ⟨_, List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩, rfl⟩)
  rw [id_eq, orL_bool, List.any_eq_true] at h1
  obtain ⟨b, hb, hb'⟩ := h1
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb
  exact ⟨j, hb'⟩

theorem invT_tabF {t u : Fin 6 → Fin 6 → Bool} (h : invT boolOps (tabF t) (tabF u) = true)
    (k j : Fin 6) : (t k j = true → u j k = true) ∧ (u k j = true → t j k = true) := by
  rw [invT, andL_bool, List.all_eq_true] at h
  have h1 := h _ (List.mem_flatMap.2 ⟨k.val, List.mem_range.2 k.isLt,
    List.mem_map.2 ⟨j.val, List.mem_range.2 j.isLt, rfl⟩⟩)
  simp only [id_eq, zr_bool, tabF_getD _ _ _ k.isLt j.isLt, tabF_getD _ _ _ j.isLt k.isLt,
    Fin.eta, a_bool, bor_bool, bnot_bool] at h1
  revert h1
  cases t k j <;> cases u j k <;> cases u k j <;> cases t j k <;> decide

theorem kerT_tabF (t : Fin 6 → Fin 6 → Bool) :
    kerT boolOps (tabF t) = true ↔ ∀ k, t k k = true := by
  rw [kerT, andL_bool, List.all_eq_true]
  constructor
  · intro h k
    have h1 := h _ (List.mem_map.2 ⟨k.val, List.mem_range.2 k.isLt, rfl⟩)
    simpa only [id_eq, zr_bool, tabF_getD _ _ _ k.isLt k.isLt, Fin.eta] using h1
  · intro h b hb
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
    rw [List.mem_range] at hk
    simpa only [id_eq, zr_bool, tabF_getD _ _ _ hk hk] using h ⟨k, hk⟩

@[expose] def rowF (a : Fin 6) : List Bool := (List.finRange 6).map fun j => decide (a = j)

@[expose] def pairsF : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

theorem invP_row : ∀ a b : Fin 6, invP boolOps (rowF a) (rowF b) = decide (b < a) := by
  decide

theorem parT_rows (f : Fin 6 → Fin 6) :
    parT boolOps ((List.finRange 6).map fun k => rowF (f k)) =
      (pairsF.map fun p => invP boolOps (rowF (f p.1)) (rowF (f p.2))).foldr xor false := rfl

@[expose] def sgnB (b : Bool) : ℤˣ := if b then -1 else 1

theorem sgnB_foldr (l : List Bool) : sgnB (l.foldr xor false) = (l.map sgnB).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.map_cons, List.prod_cons, ← ih]
    cases a <;> cases l.foldr xor false <;> decide

theorem pairsF_lt : ∀ p ∈ pairsF, p.1 < p.2 := by decide

theorem prod_pairsF (g : Fin 6 → Fin 6 → ℤˣ) :
    ∏ j, ∏ i ∈ Finset.Iio j, g i j = (pairsF.map fun p => g p.1 p.2).prod := by
  rw [Finset.prod_sigma']
  have hs : (Finset.univ.sigma fun j : Fin 6 => Finset.Iio j) =
      (pairsF.map fun p => (⟨p.2, p.1⟩ : (_ : Fin 6) × Fin 6)).toFinset := by
    decide
  rw [hs, List.prod_toFinset _ (by decide), List.map_map]
  rfl

theorem sign_pairs (σ : Equiv.Perm (Fin 6)) :
    Equiv.Perm.sign σ = sgnB ((pairsF.map fun p => decide (σ p.2 < σ p.1)).foldr xor false) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio, prod_pairsF, sgnB_foldr, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hne : σ p.1 ≠ σ p.2 := σ.injective.ne (ne_of_lt (pairsF_lt p hp))
  simp only [Function.comp_apply, sgnB]
  by_cases h : σ p.1 < σ p.2
  · simp [h, not_lt.2 h.le]
  · simp [h, lt_of_le_of_ne (not_lt.1 h) (Ne.symm hne)]

theorem idxL_tt {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true) (k : Fin 6) :
    tt i A k (idxL i A k) = true := by
  obtain ⟨j, hj⟩ := stabT_tabF hst k
  rwa [idxL_spec hj]

theorem tt_iff {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true) (k j : Fin 6) :
    tt i A k j = decide (idxL i A k = j) := by
  by_cases h : idxL i A k = j
  · rw [decide_eq_true h, ← h, idxL_tt hst]
  · rw [decide_eq_false h]
    cases ht : tt i A k j
    · rfl
    · exact absurd (idxL_spec ht) h

theorem tabF_rows {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true) :
    tabF (tt i A) = (List.finRange 6).map fun k => rowF (idxL i A k) := by
  unfold tabF rowF
  apply List.map_congr_left
  intro k _
  apply List.map_congr_left
  intro j _
  exact tt_iff hst k j

theorem inv_pair {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true)
    (hsa : stabT boolOps (tabF (tt i (adjL A))) = true)
    (hinv : invT boolOps (tabF (tt i A)) (tabF (tt i (adjL A))) = true) :
    (∀ k, idxL i (adjL A) (idxL i A k) = k) ∧ (∀ k, idxL i A (idxL i (adjL A) k) = k) :=
  ⟨fun k => idxL_spec ((invT_tabF hinv k _).1 (idxL_tt hst k)),
    fun k => idxL_spec ((invT_tabF hinv k _).2 (idxL_tt hsa k))⟩

theorem permLOf_apply {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true)
    (hsa : stabT boolOps (tabF (tt i (adjL A))) = true)
    (hinv : invT boolOps (tabF (tt i A)) (tabF (tt i (adjL A))) = true) (k : Fin 6) :
    permLOf i A k = idxL i A k := by
  unfold permLOf t7PermOf
  rw [dif_pos (inv_pair hst hsa hinv)]
  rfl

theorem sign_permLOf {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true)
    (hsa : stabT boolOps (tabF (tt i (adjL A))) = true)
    (hinv : invT boolOps (tabF (tt i A)) (tabF (tt i (adjL A))) = true)
    (hpar : parT boolOps (tabF (tt i A)) = false) :
    Equiv.Perm.sign (permLOf i A) = 1 := by
  rw [tabF_rows hst, parT_rows] at hpar
  simp only [invP_row] at hpar
  rw [sign_pairs]
  simp only [permLOf_apply hst hsa hinv, hpar]
  rfl

theorem permLOf_one {i : Fin 6} {A : M3} (hst : stabT boolOps (tabF (tt i A)) = true)
    (hsa : stabT boolOps (tabF (tt i (adjL A))) = true)
    (hinv : invT boolOps (tabF (tt i A)) (tabF (tt i (adjL A))) = true) :
    decide (permLOf i A = 1) = kerT boolOps (tabF (tt i A)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, kerT_tabF]
  simp only [tt_iff hst, decide_eq_true_iff, Equiv.ext_iff, Equiv.Perm.one_apply,
    permLOf_apply hst hsa hinv]

theorem ml_e (x y z w : F4) :
    ml boolOps (lbF x) (hbF x) (lbF y) (hbF y) (lbF z) (hbF z) (lbF w) (hbF w) =
      lbF (x * y + z * w) := by
  simp only [ml, lbF, hbF, pl_enc, xl_enc, cadd_code, cmul_code]

theorem mh_e (x y z w : F4) :
    mh boolOps (lbF x) (hbF x) (lbF y) (hbF y) (lbF z) (hbF z) (lbF w) (hbF w) =
      hbF (x * y + z * w) := by
  simp only [mh, lbF, hbF, ph_enc, xh_enc, cadd_code, cmul_code]

theorem adjT_bits (A : M3) : adjT boolOps (bits A) = bits (adjL A) := by
  have hs : ∀ a b : F4, a - b = a + b := fun _ _ => rfl
  have hn : ∀ a b : F4, -a + b = a + b := fun _ _ => rfl
  simp only [adjT, bits, adjL, ml_e, mh_e, hs, hn]

theorem scal_bits (A : M3) : scal boolOps (bits A) = decide (toL A).IsScalar := by
  rw [bits_eq, scal_ofM3]

theorem scalL_of {A : M3} (hs : (toL A).IsScalar) (hd : Light.detL A = 1) : scalL A = true := by
  obtain ⟨⟨a00⟩, ⟨a01⟩, ⟨a02⟩, ⟨a10⟩, ⟨a11⟩, ⟨a12⟩, ⟨a20⟩, ⟨a21⟩, ⟨a22⟩⟩ := A
  obtain ⟨h01, h02, h10, h12, h20, h21, h0, h1⟩ := hs
  simp only [toL] at h01 h02 h10 h12 h20 h21 h0 h1
  subst h01 h02 h10 h12 h20 h21 h0 h1
  revert a00 hd
  decide

theorem chk_at {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true) (A : M3) :
    stabX boolOps (bits A) (omC i.val) = decide (codeL A ∈ C) ∧
      (stabX boolOps (bits A) (omC i.val) && badX boolOps (bits A) (omC i.val)) = false ∧
      (stabX boolOps (bits A) (omC i.val) &&
        kerT boolOps (mtab boolOps (bits A) (omC i.val))) = decide (codeL A ∈ K) ∧
      ((stabX boolOps (bits A) (omC i.val) &&
        kerT boolOps (mtab boolOps (bits A) (omC i.val))) && !scal boolOps (bits A)) = false := by
  obtain ⟨T, hT, h1⟩ := chkAll_eq h
  unfold chkI at h1
  simp only [Bool.and_eq_true] at h1
  have hX := Nat.eq_of_beq_eq_true h1.1.1.1.2
  have hKp := Nat.eq_of_beq_eq_true h1.1.1.2
  have hB := Nat.eq_of_beq_eq_true h1.1.2
  have hS := Nat.eq_of_beq_eq_true h1.2
  have ha : ∀ p q : Nat, ((natOps T).a p q).testBit (codeL A) =
      boolOps.a (p.testBit (codeL A)) (q.testBit (codeL A)) :=
    fun p q => Nat.testBit_and p q (codeL A)
  have hx : ∀ p q : Nat, ((natOps T).x p q).testBit (codeL A) =
      boolOps.x (p.testBit (codeL A)) (q.testBit (codeL A)) :=
    fun p q => Nat.testBit_xor p q (codeL A)
  have ht : (natOps T).t.testBit (codeL A) = boolOps.t := hT _ (codeM_lt _)
  have bX := stabX_bit hT A (omC i.val)
  have bB : (badX (natOps T) (plns 18) (omC i.val)).testBit (codeL A) =
      badX boolOps (bits A) (omC i.val) := by
    rw [badX_map (natOps T) boolOps (fun n => n.testBit (codeL A)) ha hx ht, plns_bits]
  have bK : (kerT (natOps T) (mtab (natOps T) (plns 18) (omC i.val))).testBit (codeL A) =
      kerT boolOps (mtab boolOps (bits A) (omC i.val)) := by
    rw [kerT_map (natOps T) boolOps (fun n => n.testBit (codeL A)) ha hx ht,
      mtab_map (natOps T) boolOps (fun n => n.testBit (codeL A)) ha hx ht, plns_bits]
  have bS : (bnot (natOps T) (scal (natOps T) (plns 18))).testBit (codeL A) =
      !scal boolOps (bits A) := by
    rw [bnot_map (natOps T) boolOps (fun n => n.testBit (codeL A)) ha hx ht,
      scal_map (natOps T) boolOps (fun n => n.testBit (codeL A)) ha hx ht, plns_bits, bnot_bool]
  have eX := congrArg (fun n => n.testBit (codeL A)) hX
  have eK := congrArg (fun n => n.testBit (codeL A)) hKp
  have eB := congrArg (fun n => n.testBit (codeL A)) hB
  have eS := congrArg (fun n => n.testBit (codeL A)) hS
  simp only [ha, bX, bB, bK, bS, testBit_sumPow, Nat.zero_testBit, a_bool] at eX eK eB eS
  exact ⟨eX, eB, eK, eS⟩

theorem incB_chk {om : List Pt} {C K : List Nat} (h : chkAll om C K = true) :
    incB C = true ∧ incB K = true := by
  obtain ⟨T, -, h1⟩ := chkAll_eq h
  unfold chkI at h1
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1.1.1

theorem stabX_split (A : MatT Bool) (om : List Pt) :
    stabX boolOps A om = (isOne boolOps (F4M3B.detL boolOps A) (detH boolOps A) &&
      stabT boolOps (mtab boolOps A om)) := rfl

theorem badX_split (A : MatT Bool) (om : List Pt) :
    badX boolOps A om = (!stabT boolOps (mtab boolOps (adjT boolOps A) om) ||
      !invT boolOps (mtab boolOps A om) (mtab boolOps (adjT boolOps A) om) ||
      parT boolOps (mtab boolOps A om)) := by
  simp only [badX, bor_bool, bnot_bool]

theorem mem_facts {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true) {A : M3}
    (hA : A ∈ piLS (slL ()) i) :
    stabT boolOps (tabF (tt i A)) = true ∧ stabT boolOps (tabF (tt i (adjL A))) = true ∧
      invT boolOps (tabF (tt i A)) (tabF (tt i (adjL A))) = true ∧
      parT boolOps (tabF (tt i A)) = false ∧
      kerT boolOps (tabF (tt i A)) = decide (codeL A ∈ K) ∧
      (kerT boolOps (tabF (tt i A)) = true → scal boolOps (bits A) = true) := by
  have hX : stabX boolOps (bits A) (omC i.val) = true := by
    rw [stabX_omC]
    exact (mem_piLS i A).1 hA
  obtain ⟨-, hB, hK, hS⟩ := chk_at h A
  rw [hX, Bool.true_and] at hB hK hS
  rw [stabX_split, Bool.and_eq_true] at hX
  rw [badX_split, adjT_bits, mtab_bits, mtab_bits] at hB
  rw [mtab_bits] at hX hK hS
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hB
  refine ⟨hX.2, hB.1.1, hB.1.2, hB.2, hK, fun hk => ?_⟩
  rw [hk, Bool.true_and, Bool.not_eq_false'] at hS
  exact hS

theorem decL_mem {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true) {c : Nat}
    (hc : c ∈ K) (hlt : c < 2 ^ 18) :
    decL c ∈ piLS (slL ()) i ∧ kerT boolOps (tabF (tt i (decL c))) = true := by
  obtain ⟨-, -, hK, -⟩ := chk_at h (decL c)
  rw [codeL_decL c hlt, decide_eq_true hc, Bool.and_eq_true, mtab_bits] at hK
  refine ⟨(mem_piLS i _).2 ?_, hK.2⟩
  rw [← stabX_omC]
  exact hK.1

theorem t7CheckAtS_of {i : Fin 6} {C K : List Nat} (h : chkAll (omC i.val) C K = true)
    (hC : C.length = 1080) (hK : K.length = 3) : t7CheckAtS (slL ()) i = true := by
  obtain ⟨hiC, hiK⟩ := incB_chk h
  obtain ⟨hKnd, hKlt⟩ := incB_of hiK
  have hker : ∀ A ∈ piLS (slL ()) i, decide (permLOf i A = 1) = decide (codeL A ∈ K) := by
    intro A hA
    obtain ⟨h1, h2, h3, -, h5, -⟩ := mem_facts h hA
    rw [permLOf_one h1 h2 h3, h5]
  have hperm : List.Perm (((piLS (slL ()) i).filter fun A => decide (permLOf i A = 1)).map codeL)
      K := by
    refine (List.perm_ext_iff_of_nodup
      (((nodup_piLS i).filter _).map codeL_injective) hKnd).2 fun c => ?_
    constructor
    · intro hc
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hc
      rw [List.mem_filter] at hA
      rw [hker A hA.1] at hA
      exact of_decide_eq_true hA.2
    · intro hc
      obtain ⟨hm, hk⟩ := decL_mem h hc (hKlt c hc)
      refine List.mem_map.2 ⟨decL c, List.mem_filter.2 ⟨hm, ?_⟩, codeL_decL c (hKlt c hc)⟩
      rw [hker _ hm, codeL_decL c (hKlt c hc)]
      exact decide_eq_true hc
  have hKL : ((piLS (slL ()) i).filter fun A => decide (permLOf i A = 1)).length = 3 := by
    rw [← List.length_map (f := codeL), hperm.length_eq, hK]
  have hsg : ∀ A ∈ piLS (slL ()) i, Equiv.Perm.sign (permLOf i A) = 1 := by
    intro A hA
    obtain ⟨h1, h2, h3, h4, -, -⟩ := mem_facts h hA
    exact sign_permLOf h1 h2 h3 h4
  have hsc : ∀ A ∈ (piLS (slL ()) i).filter (fun A => decide (permLOf i A = 1)),
      scalL A = true := by
    intro A hA
    rw [List.mem_filter] at hA
    obtain ⟨h1, h2, h3, -, -, h6⟩ := mem_facts h hA.1
    have hk := hA.2
    rw [permLOf_one h1 h2 h3] at hk
    have hs := h6 hk
    rw [scal_bits] at hs
    have hd : Light.detL A = 1 := by
      have := (mem_piLS i A).1 hA.1
      rw [Bool.and_eq_true] at this
      exact of_decide_eq_true this.1
    exact scalL_of (of_decide_eq_true hs) hd
  unfold t7CheckAtS
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨⟨⟨⟨nodup_piLS i, (piLS_length h hiC).trans hC⟩, hsg⟩, hKL⟩, hsc⟩

theorem t7Check_of
    (h : ∀ i : Fin 6, ∃ C K, chkAll (omC i.val) C K = true ∧ C.length = 1080 ∧ K.length = 3) :
    t7Check () = true := by
  rw [t7Check, t7CheckAll, decide_eq_true_iff]
  intro i
  obtain ⟨C, K, h1, h2, h3⟩ := h i
  exact t7CheckAtS_of h1 h2 h3

end CFSG.KC.F4T7B

end
