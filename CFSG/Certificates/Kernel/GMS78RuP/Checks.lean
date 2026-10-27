module

public import CFSG.Certificates.Kernel.GMS78RuP.Codes
public import CFSG.Certificates.Kernel.GMS78RuGenS

public section

namespace CFSG.KC.GMS.P117

open CFSG.KLie.CT CFSG.GMS78RuSim CFSG.GMS78RuS CFSG.GMS78RuSP

structure MulCode (m : Nat → Nat → Nat) (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8))
    (dct : List Lin8) : Prop where
  code : ∀ p q : Pt, p.1 < 256 → q.1 < 256 →
    m (pCode p) (pCode q) = pCode (Gen.pMulG gA dA dct p q)
  lt : ∀ p q : Pt, p.1 < 256 → q.1 < 256 → (Gen.pMulG gA dA dct p q).1 < 256

section Facts

variable {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8} {xs : List Pt}
  {m : Nat → Nat → Nat} {JM : Nat} {CXL F1L KL : List Nat}

theorem all_congr' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall_congr' fun x => forall_congr' fun hx => by rw [h x hx]

theorem pInJ_code (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256) {p : Pt}
    (hp : p.1 < 256) : pInJ m (xs.map pCode) (pCode p) = Gen.inJG gA dA dct xs p := by
  unfold pInJ Gen.inJG
  rw [neAllL_eq, List.all_map]
  refine all_congr' fun x hx => ?_
  have hx' := hxs x hx
  have hf : m 256 (pCode (Gen.pMulG gA dA dct x p)) =
      pCode (Gen.pMulG gA dA dct fPt (Gen.pMulG gA dA dct x p)) := by
    have := hM.code fPt _ (by decide) (hM.lt x p hx' hp)
    rwa [pCode_f] at this
  simp only [Function.comp]
  rw [hM.code p x hp hx', hM.code x p hx' hp, hf, orB_eq, beq_code (hM.lt p x hp hx')
    (hM.lt x p hx' hp), beq_code (hM.lt p x hp hx') (hM.lt _ _ (by decide) (hM.lt x p hx' hp))]

theorem pInCX_code (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256) {p : Pt}
    (hp : p.1 < 256) : pInCX m (xs.map pCode) (pCode p) = Gen.inCXG gA dA dct xs p := by
  unfold pInCX Gen.inCXG
  rw [neAllL_eq, List.all_map]
  refine all_congr' fun x hx => ?_
  have hx' := hxs x hx
  simp only [Function.comp]
  rw [hM.code p x hp hx', hM.code x p hx' hp, beq_code (hM.lt p x hp hx') (hM.lt x p hx' hp)]

theorem pCmt_code (hM : MulCode m gA dA dct) {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) :
    pCmt m (pCode q) (pCode p) = Gen.cmtG gA dA dct q p := by
  unfold pCmt Gen.cmtG
  rw [hM.code p q hp hq, hM.code q p hq hp, beq_code (hM.lt p q hp hq) (hM.lt q p hq hp)]

theorem sq_code (hM : MulCode m gA dA dct) {p : Pt} (hp : p.1 < 256) :
    Nat.beq (m (pCode p) (pCode p)) 0 = (Gen.sqPtG gA dA dct p == onePt) := by
  have := beq_code (hM.lt p p hp hp) (by decide : onePt.1 < 256)
  rw [pCode_one] at this
  rw [hM.code p p hp hp]
  exact this

theorem pJL_eq (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (hJ : ∀ i < 16384, pBit JM i = pInJ m (xs.map pCode) (pCodeOf i)) :
    pJL JM = (Gen.jPtsG gA dA dct xs).map pCode := by
  unfold pJL Gen.jPtsG
  rw [pMap_eq, sFilter_eq, allPt_eq, List.filter_map, List.map_map]
  have hf : (List.range 16384).filter (pBit JM) =
      (List.range 16384).filter (Gen.inJG gA dA dct xs ∘ decPt) := by
    refine List.filter_congr fun i hi => ?_
    have hi' := List.mem_range.1 hi
    have hdec : (decPt i).1 < 256 := by change i / 64 < 256; omega
    rw [hJ i hi', ← pCode_decPt i, pInJ_code hM hxs hdec]
    rfl
  rw [hf]
  exact List.map_congr_left fun i _ => (pCode_decPt i).symm

theorem jMem_eq_inJ {p : Pt} (hp : p.1 < 256) :
    Gen.jMemG gA dA dct xs p = Gen.inJG gA dA dct xs p := by
  unfold Gen.jMemG
  rw [if_pos (encPt_lt hp), decPt_encPt hp]

theorem pJMem_code (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (hJ : ∀ i < 16384, pBit JM i = pInJ m (xs.map pCode) (pCodeOf i)) {p : Pt} (hp : p.1 < 256) :
    pJMem JM (pCode p) = Gen.jMemG gA dA dct xs p := by
  rw [jMem_eq_inJ hp]
  unfold pJMem
  rw [pIdxOf_code hp, hJ _ (encPt_lt hp), pCodeOf_encPt hp, pInJ_code hM hxs hp]

theorem mem_jPts {p : Pt} :
    p ∈ Gen.jPtsG gA dA dct xs ↔ p.1 < 256 ∧ Gen.inJG gA dA dct xs p = true := by
  unfold Gen.jPtsG
  rw [List.mem_filter, mem_allPt]

theorem checkAG_of (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (h1 : pInJ m (xs.map pCode) 102 = true) (h2 : pInCX m (xs.map pCode) 102 = false)
    (h3 : Nat.beq (m 102 102) 0 = true) : Gen.checkAG gA dA dct xs = true := by
  have ha : aPt.1 < 256 := by decide
  have e1 : Gen.inJG gA dA dct xs aPt = true := by
    rw [← pInJ_code hM hxs ha, pCode_a]; exact h1
  have e2 : Gen.inCXG gA dA dct xs aPt = false := by
    rw [← pInCX_code hM hxs ha, pCode_a]; exact h2
  have e3 : (Gen.sqPtG gA dA dct aPt == onePt) = true := by
    rw [← sq_code hM ha, pCode_a]; exact h3
  unfold Gen.checkAG
  rw [e1, e2, e3]
  rfl

theorem checkCaG_of (hM : MulCode m gA dA dct)
    (h : Nat.beq (pCount (pCmt m 102) pAll) 1024 = true) : Gen.checkCaG gA dA dct = true := by
  have ha : aPt.1 < 256 := by decide
  have h' := Nat.eq_of_beq_eq_true h
  rw [pCount_eq, pAll_eq, List.countP_map] at h'
  have hc : allPt.countP (Gen.cmtG gA dA dct aPt) = 1024 := by
    rw [← h']
    refine (List.countP_congr fun y hy => ?_).symm
    have hy' := mem_allPt.1 hy
    simp only [Function.comp]
    rw [← pCode_a, pCmt_code hM hy' ha]
  unfold Gen.checkCaG
  rw [hc]
  rfl

theorem checkJdG_of (hJL : pJL JM = (Gen.jPtsG gA dA dct xs).map pCode)
    (h : neAllL (fun d => czAny (fun x => Nat.beq (Nat.shiftRight x 11) d) (pJL JM))
      [0, 1, 4, 5] = true) : Gen.checkJdG gA dA dct xs = true := by
  have key : ∀ d : Nat, d < 8 →
      czAny (fun x => Nat.beq (Nat.shiftRight x 11) d) (pJL JM) = true →
      (Gen.jPtsG gA dA dct xs).any (fun j => j.2.2 == fin8Of d) = true := by
    intro d hd hc
    rw [czAny_eq, hJL, List.any_map, List.any_eq_true] at hc
    obtain ⟨j, hj, hjd⟩ := hc
    obtain ⟨hj1, -⟩ := mem_jPts.1 hj
    rw [List.any_eq_true]
    refine ⟨j, hj, ?_⟩
    simp only [Function.comp, beq_eq, beq_iff_eq] at hjd
    rw [beq_iff_eq]
    apply Fin.ext
    have ht := j.2.1.isLt
    have hd' := j.2.2.isLt
    rw [shr11, pCode_eq hj1] at hjd
    change j.2.2.val = d % 8
    omega
  rw [neAllL_eq] at h
  have h0 := List.all_eq_true.1 h 0 (by simp)
  have h1 := List.all_eq_true.1 h 1 (by simp)
  have h4 := List.all_eq_true.1 h 4 (by simp)
  have h5 := List.all_eq_true.1 h 5 (by simp)
  unfold Gen.checkJdG
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨key 0 (by omega) h0, key 1 (by omega) h1, key 4 (by omega) h4, key 5 (by omega) h5⟩

theorem checkCxG_of (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (hJL : pJL JM = (Gen.jPtsG gA dA dct xs).map pCode)
    (hL : czListEq CXL (pFilt (fun x => andB (notB (pInCX m (xs.map pCode) x))
      (Nat.beq (m x x) 0)) (pJL JM)) = true)
    (hCx : ∀ i < CXL.length, kCx m JM (CXL.getD i 0) = true) :
    Gen.checkCxG gA dA dct xs = true := by
  rw [czListEq_iff, pFilt_eq] at hL
  unfold Gen.checkCxG
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨hx1, -⟩ := mem_jPts.1 hx
  by_cases hc : Gen.inCXG gA dA dct xs x = true
  · simp [hc]
  by_cases hs : Gen.sqPtG gA dA dct x = onePt
  swap
  · simp [hs]
  have hmem : pCode x ∈ CXL := by
    rw [hL, List.mem_filter, hJL]
    refine ⟨List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    rw [andB_eq, notB_eq, Bool.and_eq_true, pInCX_code hM hxs hx1, sq_code hM hx1, hs]
    simp only [Bool.not_eq_true', beq_self_eq_true, and_true]
    simpa using hc
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hmem
  have hk := hCx i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hie] at hk
  unfold kCx at hk
  rw [pCount_eq, hJL, List.countP_map, ble_eq] at hk
  have hk' := of_decide_eq_true hk
  have hcnt : (Gen.jPtsG gA dA dct xs).countP (Gen.cmtG gA dA dct x) ≤ 128 := by
    refine Nat.le_trans (Nat.le_of_eq (List.countP_congr fun j hj => ?_)) hk'
    have hj1 := (mem_jPts.1 hj).1
    simp only [Function.comp]
    rw [pCmt_code hM hj1 hx1]
  simp [hcnt]

theorem checkF1G_of (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (hJ : ∀ i < 16384, pBit JM i = pInJ m (xs.map pCode) (pCodeOf i))
    (hL : czListEq (pMap (fun e => Nat.land e 16383) F1L) (pFilt (fun y => andB (pCmt m 102 y)
      (andB (pJMem JM (m y y)) (andB (notB (pJMem JM y)) (notB (pEvenD y))))) pAll) = true)
    (hF1 : ∀ i < F1L.length, kF1 m JM (F1L.getD i 0) = true) :
    Gen.checkF1G gA dA dct xs = true := by
  have ha : aPt.1 < 256 := by decide
  rw [czListEq_iff, pMap_eq, pFilt_eq, pAll_eq] at hL
  unfold Gen.checkF1G
  rw [List.all_eq_true]
  intro y hy
  have hy1 := mem_allPt.1 hy
  have hsq : (Gen.sqPtG gA dA dct y).1 < 256 := hM.lt y y hy1 hy1
  cases c1 : Gen.cmtG gA dA dct aPt y
  · simp
  cases c2 : Gen.jMemG gA dA dct xs (Gen.sqPtG gA dA dct y)
  · simp
  cases c3 : Gen.jMemG gA dA dct xs y
  swap
  · simp
  cases c4 : evenD y.2.2
  swap
  · simp
  have hmem : pCode y ∈ F1L.map (fun e => Nat.land e 16383) := by
    rw [hL, List.mem_filter]
    refine ⟨List.mem_map.2 ⟨y, hy, rfl⟩, ?_⟩
    simp only [andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← pCode_a, pCmt_code hM hy1 ha]; exact c1
    · rw [hM.code y y hy1 hy1]; exact (pJMem_code hM hxs hJ hsq).trans c2
    · rw [pJMem_code hM hxs hJ hy1]; exact c3
    · rw [pEvenD_code hy1]; exact c4
  obtain ⟨e, he, he'⟩ := List.mem_map.1 hmem
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
  have hk := hF1 i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hie] at hk
  unfold kF1 at hk
  rw [he'] at hk
  dsimp only at hk
  simp only [andB_eq, Bool.and_eq_true, blt_eq, decide_eq_true_eq] at hk
  obtain ⟨hj1, hj2, hj3, hj4⟩ := hk
  obtain ⟨hjc, hjp⟩ := pCode_pDec hj1
  rw [← hjc] at hj2 hj3 hj4
  have hmul := hM.code y (pDec (Nat.shiftRight e 14)) hy1 hjp
  rw [hmul] at hj4
  rw [sq_code hM (hM.lt _ _ hy1 hjp)] at hj4
  rw [pJMem_code hM hxs hJ hjp, jMem_eq_inJ hjp] at hj2
  rw [← pCode_a, pCmt_code hM hjp ha] at hj3
  have hany : (Gen.jPtsG gA dA dct xs).any (fun j => Gen.cmtG gA dA dct aPt j &&
      Gen.sqPtG gA dA dct (Gen.pMulG gA dA dct y j) == onePt) = true :=
    List.any_eq_true.2 ⟨pDec (Nat.shiftRight e 14), mem_jPts.2 ⟨hjp, hj2⟩,
      by rw [Bool.and_eq_true]; exact ⟨hj3, hj4⟩⟩
  simp only [Bool.not_true, Bool.false_or]
  exact hany

theorem checkF3G_of (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (hJ : ∀ i < 16384, pBit JM i = pInJ m (xs.map pCode) (pCodeOf i))
    (h1 : pInJ m (xs.map pCode) 9216 = true) (h2 : pInCX m (xs.map pCode) 9216 = false)
    (hL : czListEq (pMap (fun e => Nat.land e 16383) KL)
      (pFilt (fun k => andB (pInCX m (xs.map pCode) k)
        (Nat.beq (m (m k 9216) (m k 9216)) 0)) (pJL JM)) = true)
    (hF3 : ∀ i < KL.length, kF3 m JM (KL.getD i 0) = true) :
    Gen.checkF3G gA dA dct xs = true := by
  have hJL := pJL_eq hM hxs hJ
  have hc0 : cPt.1 < 256 := by decide
  have e1 : Gen.inJG gA dA dct xs cPt = true := by
    rw [← pInJ_code hM hxs hc0, pCode_c0]; exact h1
  have e2 : Gen.inCXG gA dA dct xs cPt = false := by
    rw [← pInCX_code hM hxs hc0, pCode_c0]; exact h2
  rw [czListEq_iff, pMap_eq, pFilt_eq] at hL
  unfold Gen.checkF3G
  rw [e1, e2, Bool.not_false, Bool.true_and, Bool.true_and]
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_filter] at hk
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hk3, hk4⟩ := mem_jPts.1 hk1
  have hr : (Gen.pMulG gA dA dct k cPt).1 < 256 := hM.lt k cPt hk3 hc0
  by_cases hs : Gen.sqPtG gA dA dct (Gen.pMulG gA dA dct k cPt) = onePt
  swap
  · simp [hs]
  rw [Bool.or_eq_true]
  right
  have hmr : m (pCode k) 9216 = pCode (Gen.pMulG gA dA dct k cPt) := by
    have := hM.code k cPt hk3 hc0
    rwa [pCode_c0] at this
  have hmem : pCode k ∈ KL.map (fun e => Nat.land e 16383) := by
    rw [hL, List.mem_filter, hJL]
    refine ⟨List.mem_map.2 ⟨k, hk1, rfl⟩, ?_⟩
    rw [andB_eq, Bool.and_eq_true, pInCX_code hM hxs hk3, hmr, sq_code hM hr, hs]
    exact ⟨hk2, rfl⟩
  obtain ⟨e, he, he'⟩ := List.mem_map.1 hmem
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 he
  have hk' := hF3 i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hie] at hk'
  unfold kF3 at hk'
  rw [he'] at hk'
  dsimp only at hk'
  rw [hmr] at hk'
  simp only [andB_eq, Bool.and_eq_true, notB_eq, Bool.not_eq_true', blt_eq,
    decide_eq_true_eq] at hk'
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hk'
  obtain ⟨up, hupc, hup⟩ : ∃ up : Pt, pCode up = Nat.shiftRight e 14 ∧ up.1 < 256 :=
    ⟨pDec _, pCode_pDec hu1⟩
  rw [← hupc] at hu2 hu3 hu4 hu5 hu6
  have c1 : Gen.cmtG gA dA dct (Gen.pMulG gA dA dct k cPt) up = true := by
    rw [← pCmt_code hM hup hr]; exact hu2
  have c2 : Gen.jMemG gA dA dct xs (Gen.sqPtG gA dA dct up) = true := by
    rw [hM.code up up hup hup] at hu3
    exact (pJMem_code hM hxs hJ (hM.lt up up hup hup)).symm.trans hu3
  have c3 : Gen.jMemG gA dA dct xs up = false := by
    rw [← pJMem_code hM hxs hJ hup]; exact hu4
  have c4 : evenD up.2.2 = false := by
    rw [← pEvenD_code hup]; exact hu5
  have c5 : (Gen.jPtsG gA dA dct xs).all (fun j => !Gen.cmtG gA dA dct
      (Gen.pMulG gA dA dct k cPt) j || Gen.sqPtG gA dA dct (Gen.pMulG gA dA dct up j) != onePt) =
      true := by
    rw [neAllL_eq, hJL, List.all_map, List.all_eq_true] at hu6
    rw [List.all_eq_true]
    intro j hj
    have hj1 := (mem_jPts.1 hj).1
    have := hu6 j hj
    simp only [Function.comp, orB_eq, notB_eq] at this
    rw [pCmt_code hM hj1 hr, hM.code up j hup hj1, sq_code hM (hM.lt up j hup hj1)] at this
    exact this
  rw [List.any_eq_true]
  refine ⟨up, mem_allPt.2 hup, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨c1, c2⟩, ?_⟩, ?_⟩, c5⟩
  · rw [c3]; rfl
  · rw [c4]; rfl

theorem checks_of (hM : MulCode m gA dA dct) (hxs : ∀ x ∈ xs, x.1 < 256)
    (hJ : ∀ i < 16384, kJM m (xs.map pCode) JM i = true)
    (hA : kA117 m (xs.map pCode) JM = true)
    (hL : kLists117 m (xs.map pCode) JM CXL F1L KL = true)
    (hCx : ∀ i < CXL.length, kCx m JM (CXL.getD i 0) = true)
    (hF1 : ∀ i < F1L.length, kF1 m JM (F1L.getD i 0) = true)
    (hF3 : ∀ i < KL.length, kF3 m JM (KL.getD i 0) = true) :
    Gen.checkAG gA dA dct xs = true ∧ Gen.checkCaG gA dA dct = true ∧
      Gen.checkCxG gA dA dct xs = true ∧ Gen.checkF1G gA dA dct xs = true ∧
      Gen.checkF3G gA dA dct xs = true ∧ Gen.checkJdG gA dA dct xs = true := by
  have hJ' : ∀ i < 16384, pBit JM i = pInJ m (xs.map pCode) (pCodeOf i) := by
    intro i hi
    have h := hJ i hi
    unfold kJM at h
    cases hb : pBit JM i
    · rw [hb] at h
      exact (notB_iff.1 h).symm
    · rw [hb] at h
      exact h.symm
  have hJL := pJL_eq hM hxs hJ'
  unfold kA117 at hA
  obtain ⟨a1, hA⟩ := andB_iff.1 hA
  obtain ⟨a2, hA⟩ := andB_iff.1 hA
  obtain ⟨a3, hA⟩ := andB_iff.1 hA
  obtain ⟨a4, hA⟩ := andB_iff.1 hA
  obtain ⟨a5, hA⟩ := andB_iff.1 hA
  obtain ⟨a6, a7⟩ := andB_iff.1 hA
  unfold kLists117 at hL
  obtain ⟨l1, hL⟩ := andB_iff.1 hL
  obtain ⟨l2, l3⟩ := andB_iff.1 hL
  exact ⟨checkAG_of hM hxs a1 (notB_iff.1 a2) a3, checkCaG_of hM a4,
    checkCxG_of hM hxs hJL l1 hCx, checkF1G_of hM hxs hJ' l2 hF1,
    checkF3G_of hM hxs hJ' a5 (notB_iff.1 a6) l3 hF3, checkJdG_of hJL a7⟩

end Facts

end CFSG.KC.GMS.P117

end
