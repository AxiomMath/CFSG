module

public import Certificates.Data.Kernel.Misc.G24
public import CFSG.LieType.Multipliers.G24Data
import CFSG.Certificates.Kernel.Misc.Spec.F2Blow
import CFSG.Certificates.Kernel.Misc.Spec.RowsArr
import CFSG.Certificates.Kernel.Misc.Spec.F3Lanes
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.Misc.G24

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.G24 CFSG.Quasithin.G2U CFSG.Fischer

@[expose] def strOf (l : List Nat) : String := String.ofList (l.map Char.ofNat)

@[expose] def digitRows (M : Matrix (Fin 14) (Fin 14) F4) : List (List Nat) :=
  (ofMat M).toList.map fun r => r.toList.map fun x => x.code.val

@[expose] def genArrsOf (GRs : List (List String)) : List (Array (Array F4)) :=
  GRs.map fun rs => (rs.map fun s => (s.toList.map f4Digit).toArray).toArray

@[expose] def wordArrOf (gs : List (Array (Array F4))) (w : List (Fin 6 × Bool)) :
    Array (Array F4) :=
  w.foldr (fun l A => mulArr 14 (gs.getD l.1 #[]) A) one14

@[expose] def pairsOf (PSs : List (List (String × String))) (i : Fin 6) :
    List (List (Fin 6 × Bool) × List (Fin 6 × Bool)) :=
  (PSs.getD i []).map fun p => (parseWord p.1, parseWord p.2)

@[expose] def invCheckG (GRs : List (List String)) : Bool :=
  (List.finRange 6).all fun i =>
    decide (mulArr 14 ((genArrsOf GRs).getD i #[]) ((genArrsOf GRs).getD i #[]) = one14)

@[expose] def relCheckG (GRs : List (List String)) (RSs : List String) : Bool :=
  (RSs.map parseWord).all fun r => decide (wordArrOf (genArrsOf GRs) r = one14)

@[expose] def commCheckG (GRs : List (List String)) (PSs : List (List (String × String))) : Bool :=
  (List.finRange 6).all fun i =>
    decide (wordArrOf (genArrsOf GRs) (commWords (pairsOf PSs i)) = (genArrsOf GRs).getD i #[])

@[expose] def rootCheckG (GRs : List (List String)) (XSs YSs : List String) : Bool :=
  (List.finRange CFSG.Blueprint.Chevalley.Tag.G2.rank).all fun i => allF4.all fun c =>
    decide (ofMat (XMat F4 i c) =
        wordArrOf (genArrsOf GRs) (parseWord (XSs.getD (4 * i.val + c.code.val) ""))) &&
      decide (ofMat (YMat F4 i c) =
        wordArrOf (genArrsOf GRs) (parseWord (YSs.getD (4 * i.val + c.code.val) "")))

@[expose] def liftArrsOf (LRs : List (List String)) : List (Array (Array (ZMod 3))) :=
  LRs.map fun rs => (rs.map fun s => (s.toList.map z3Digit).toArray).toArray

@[expose] def wordArr3Of (LRs : List (List String)) (w : List (Fin 6 × Bool)) :
    Array (Array (ZMod 3)) :=
  w.foldr (fun l A => mulArr 12 (if l.2 then (liftArrsOf LRs).getD l.1 #[]
    else ((liftArrsOf LRs).map fun A => mulArr 12 A (mulArr 12 A A)).getD l.1 #[]) A) one12

@[expose] def unitCheckG (LRs : List (List String)) : Bool :=
  (List.finRange 6).all fun i =>
    decide (mulArr 12 ((liftArrsOf LRs).getD i #[])
      (((liftArrsOf LRs).map fun A => mulArr 12 A (mulArr 12 A A)).getD i #[]) = one12) &&
    decide (mulArr 12 (((liftArrsOf LRs).map fun A => mulArr 12 A (mulArr 12 A A)).getD i #[])
      ((liftArrsOf LRs).getD i #[]) = one12)

@[expose] def coverCheckG (LRs : List (List String)) (RSs : List String)
    (PSs : List (List (String × String))) : Bool :=
  (coverWords (RSs.map parseWord) fun i => commWords (pairsOf PSs i)).all fun r =>
    decide (wordArr3Of LRs r = one12)

@[expose] def kerCheckG (LRs : List (List String)) : Bool :=
  !decide (wordArr3Of LRs dSq = one12) &&
    decide (mulArr 12 (wordArr3Of LRs dSq) (wordArr3Of LRs dSq) = one12)

theorem invCheck_eq : invCheck = invCheckG genRows := rfl
theorem relCheck_eq : relCheck = relCheckG genRows relStrings := rfl
theorem commCheck_eq : commCheck = commCheckG genRows pairStrings := rfl
theorem rootCheck_eq : rootCheck = rootCheckG genRows genStringsX genStringsY := rfl
theorem unitCheck_eq : unitCheck = unitCheckG liftRows := rfl
theorem coverCheck_eq : coverCheck = coverCheckG liftRows relStrings pairStrings := rfl
theorem kerCheck_eq : kerCheck = kerCheckG liftRows := rfl

open CFSG.KC.Misc.Spec

private theorem asciiK_iff {rs : List (List ℕ)} :
    asciiK rs = true ↔ ∀ r ∈ rs, ∀ c ∈ r, c < 128 := by
  unfold asciiK
  rw [CFSG.KS.PK.allLL_iff]
  refine forall_congr' fun r => forall_congr' fun _ => ?_
  rw [CFSG.KS.PK.allL_lqt_iff]
  simp only [Nat.blt_eq]

private theorem digitsOf_eq (rs : List (List ℕ)) :
    digitsOf rs = rs.map (List.map fun c => (c - 48) % 4) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show _ :: digitsOf rs = _
    rw [ih]
    refine congrArg₂ List.cons ?_ rfl
    induction r with
    | nil => rfl
    | cons c r ihr =>
      show _ :: _ = _ :: _
      rw [ihr]
      rfl


private theorem genArrsOf_getD (GR : List (List (List ℕ))) (i : ℕ) :
    (genArrsOf (GR.map (List.map strOf))).getD i #[] = rowsArr f4Digit (GR.getD i []) := by
  have h : genArrsOf (GR.map (List.map strOf)) = GR.map (rowsArr f4Digit) := by
    unfold genArrsOf
    rw [List.map_map]
    rfl
  rw [h]
  exact List.getD_map GR [] (n := i) (rowsArr f4Digit)

private theorem gen_shape {rows : List (List ℕ)} (hs : shape4 (digitsOf rows) = true) :
    rows.length = 14 ∧ ∀ r ∈ rows, r.length = 14 := by
  obtain ⟨h1, h2⟩ := (shape4_iff _).1 hs
  rw [digitsOf_eq] at h1 h2
  refine ⟨by simpa using h1, fun r hr => ?_⟩
  have := (h2 (r.map fun c => (c - 48) % 4) (List.mem_map_of_mem hr)).1
  simpa using this

private theorem toNat_ofNat_lt {c : ℕ} (hc : c < 128) : (Char.ofNat c).toNat = c := by
  rw [Char.toNat_ofNat, if_pos]
  exact Or.inl (by omega)

private theorem rowsArr_f4 {rows : List (List ℕ)} (ha : asciiK rows = true)
    (hs : shape4 (digitsOf rows) = true) :
    toMat 14 (rowsArr f4Digit rows) = digMat (digitsOf rows) ∧
      rowsArr f4Digit rows = ofMat (digMat (digitsOf rows)) := by
  obtain ⟨hlen, hrow⟩ := gen_shape hs
  have hascii := asciiK_iff.1 ha
  have hmem : ∀ i < 14, rows.getD i [] ∈ rows := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  have hT : toMat 14 (rowsArr f4Digit rows) = digMat (digitsOf rows) := by
    ext i j
    have hi : i.val < 14 := i.isLt
    have hj : j.val < (rows.getD i.val []).length := by rw [hrow _ (hmem _ hi)]; exact j.isLt
    have e1 : toMat 14 (rowsArr f4Digit rows) i j = f4Digit (Char.ofNat
        ((rows.getD i.val []).getD j.val 0)) := by
      show ((rowsArr f4Digit rows).getD i.val #[]).getD j.val 0 = _
      exact getD_rowsArr f4Digit rows hj
    have hc : (rows.getD i.val []).getD j.val 0 < 128 :=
      hascii _ (hmem _ hi) _ (getD_mem_of_lt hj)
    have e2 : ((digitsOf rows).getD i.val []).getD j.val 0 =
        ((rows.getD i.val []).getD j.val 0 - 48) % 4 := by
      rw [digitsOf_eq]
      have : (rows.map (List.map fun c => (c - 48) % 4)).getD i.val [] =
          (rows.getD i.val []).map fun c => (c - 48) % 4 :=
        List.getD_map rows [] (n := i.val) (List.map fun c => (c - 48) % 4)
      rw [this]
      generalize rows.getD i.val [] = r at hj ⊢
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [e1]
    show _ = (⟨⟨((digitsOf rows).getD i.val []).getD j.val 0 % 4, _⟩⟩ : F4)
    unfold f4Digit
    congr 1
    refine Fin.ext ?_
    simp only [e2, toNat_ofNat_lt hc]
    omega
  refine ⟨hT, ?_⟩
  rw [← hT]
  symm
  refine ofMat_toMat 14 _ (by rw [rowsArr_size, hlen]) fun r hr => ?_
  obtain ⟨c, hc, hr'⟩ := rowsArr_row_size f4Digit rows hr
  rw [hr', hrow c hc]

private theorem digitRows_getD (M : Matrix (Fin 14) (Fin 14) F4) (i j : Fin 14) :
    ((digitRows M).getD i.val []).getD j.val 0 = (M i j).code.val := by
  unfold digitRows ofMat
  simp [List.map_map, Function.comp_def, List.getD_eq_getElem?_getD, List.getElem?_map]

private theorem f4_ext {x y : F4} (h : x.code.val = y.code.val) : x = y := by
  obtain ⟨⟨a, ha⟩⟩ := x
  obtain ⟨⟨b, hb⟩⟩ := y
  simp only at h
  subst h
  rfl

private theorem digMat_digitRows (M : Matrix (Fin 14) (Fin 14) F4) :
    digMat (digitRows M) = M := by
  ext i j
  refine f4_ext ?_
  show ((digitRows M).getD i.val []).getD j.val 0 % 4 = (M i j).code.val
  rw [digitRows_getD]
  exact Nat.mod_eq_of_lt (M i j).code.isLt

private theorem pairsOf_map (PS : List (List (List ℕ × List ℕ))) (i : Fin 6) :
    pairsOf (PS.map (List.map fun p => (strOf p.1, strOf p.2))) i =
      (PS.getD i.val []).map fun p => (parseWord (String.ofList (p.1.map Char.ofNat)),
        parseWord (String.ofList (p.2.map Char.ofNat))) := by
  unfold pairsOf
  rw [show (PS.map (List.map fun p => (strOf p.1, strOf p.2))).getD i.val [] =
      (PS.getD i.val []).map fun p => (strOf p.1, strOf p.2) from
    List.getD_map PS [] (n := i.val) (List.map fun p => (strOf p.1, strOf p.2)), List.map_map]
  rfl

theorem g24F4_sound {GRs : List (List String)} {RSs XSs YSs : List String}
    {PSs : List (List (String × String))}
    {GR : List (List (List Nat))} {Gb : List Nat} {RS XS YS : List (List Nat)}
    {PS : List (List (List Nat × List Nat))} {XL YL : List (List (List Nat))}
    (hG : GRs = GR.map (List.map strOf)) (hR : RSs = RS.map strOf)
    (hP : PSs = PS.map (List.map fun p => (strOf p.1, strOf p.2)))
    (hX : XSs = XS.map strOf) (hY : YSs = YS.map strOf)
    (hXL : ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank) (c : F4),
      digitRows (XMat F4 i c) = nthLL XL (4 * i.val + c.code.val))
    (hYL : ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank) (c : F4),
      digitRows (YMat F4 i c) = nthLL YL (4 * i.val + c.code.val))
    (h : g24F4K GR Gb RS PS XS YS XL YL = true) :
    invCheckG GRs = true ∧ relCheckG GRs RSs = true ∧ commCheckG GRs PSs = true ∧
      rootCheckG GRs XSs YSs = true := by
  subst hG hR hP hX hY
  have h' := h
  unfold g24F4K at h'
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allN_lqt_iff,
    CFSG.KS.PK.allLL_iff] at h'
  obtain ⟨-, hgen, hinv, hrel, hcomm, hroot⟩ := h'
  set gs := genArrsOf (GR.map (List.map strOf)) with hgs
  set Mg : ℕ → Matrix (Fin 14) (Fin 14) F4 := fun i => digMat (digitsOf (nthLL GR i)) with hMgdef
  have hMg : ∀ i < 6, gs.getD i #[] = ofMat (Mg i) ∧ pkMat 28 (Gb.getD i 0) = blowMat (Mg i) := by
    intro i hi
    obtain ⟨⟨ha, hs⟩, hb⟩ := hgen i hi
    refine ⟨?_, ?_⟩
    · rw [hgs, genArrsOf_getD, ← nthLL_eq]
      exact (rowsArr_f4 ha hs).2
    · rw [← nthV_eq, ← hb, pkMat_blow14 hs]
  have hword : ∀ w : List (Fin 6 × Bool),
      wordArrOf gs w = ofMat (wordProd (fun l : Fin 6 × Bool => Mg l.1.val) w) := by
    intro w
    have h1 := foldr_mulArr 14 (fun l : Fin 6 × Bool => gs.getD l.1.val #[]) w
    have h2 : wordProd (fun l : Fin 6 × Bool => toMat 14 (gs.getD l.1.val #[])) w =
        wordProd (fun l : Fin 6 × Bool => Mg l.1.val) w := by
      congr 1
      funext l
      rw [(hMg l.1.val l.1.isLt).1, toMat_ofMat]
    rw [h2] at h1
    exact h1
  have hbw : ∀ w : List (Fin 6 × Bool), pkMat 28 (wordF4 Gb (encG w)) =
      blowMat (wordProd (fun l : Fin 6 × Bool => Mg l.1.val) w) :=
    pkMat_wordF4 (fun i hi => (hMg i hi).2)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold invCheckG
    rw [List.all_eq_true]
    intro i _
    rw [decide_eq_true_iff]
    have hm : Mg i.val * Mg i.val = 1 := by
      have h1 := hinv i.val i.isLt
      rw [nthV_eq] at h1
      have h2 := congrArg (pkMat 28) h1
      rw [pkMat_mulF2, pkMat_oneF2, (hMg i.val i.isLt).2, ← blowMat_mul, ← blowMat_one] at h2
      exact blowMat_injective h2
    show mulArr 14 (gs.getD i.val #[]) (gs.getD i.val #[]) = one14
    rw [(hMg i.val i.isLt).1, mulArr_eq_ofMat, toMat_ofMat, hm]
    rfl
  · unfold relCheckG
    rw [List.all_eq_true]
    intro r hr
    rw [decide_eq_true_iff]
    obtain ⟨r0, hr0, rfl⟩ : ∃ r0 ∈ RS, parseWord (strOf r0) = r := by
      simpa using hr
    have h1 := hrel r0 hr0
    rw [parseK_eq] at h1
    have h2 := congrArg (pkMat 28) h1
    rw [hbw, pkMat_oneF2, ← blowMat_one] at h2
    show wordArrOf gs (parseWord (String.ofList (r0.map Char.ofNat))) = one14
    rw [hword, blowMat_injective h2]
    rfl
  · unfold commCheckG
    rw [List.all_eq_true]
    intro i _
    rw [decide_eq_true_iff]
    have h1 := hcomm i.val i.isLt
    rw [nthP_eq, commsK_eq, nthV_eq] at h1
    have h2 := congrArg (pkMat 28) h1
    rw [hbw, (hMg i.val i.isLt).2] at h2
    show wordArrOf gs (commWords (pairsOf (PS.map (List.map fun p => (strOf p.1, strOf p.2))) i)) =
      gs.getD i.val #[]
    rw [pairsOf_map, hword, blowMat_injective h2, (hMg i.val i.isLt).1]
  · unfold rootCheckG
    have hroot1 : ∀ (M : Matrix (Fin 14) (Fin 14) F4) (L : List (List ℕ)) (S : List ℕ),
        digitRows M = L → shape4 L = true → blow14 L = wordF4 Gb (parseK S) →
        ofMat M = wordArrOf gs (parseWord (String.ofList (S.map Char.ofNat))) := by
      intro M L S hL hs hb
      subst hL
      rw [hword]
      rw [parseK_eq] at hb
      have h2 := congrArg (pkMat 28) hb
      rw [pkMat_blow14 hs, hbw, digMat_digitRows] at h2
      rw [blowMat_injective h2]
    rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro c _
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    have hk : 4 * i.val + c.code.val < 8 := by
      have h1 : i.val < CFSG.Blueprint.Chevalley.Tag.G2.rank := i.isLt
      have h2 := c.code.isLt
      have h3 : CFSG.Blueprint.Chevalley.Tag.G2.rank = 2 := rfl
      omega
    obtain ⟨⟨hsX, hsY⟩, hbX, hbY⟩ := hroot _ hk
    have eX : (XS.map strOf).getD (4 * i.val + c.code.val) "" =
        strOf (XS.getD (4 * i.val + c.code.val) []) :=
      List.getD_map XS [] (n := 4 * i.val + c.code.val) strOf
    have eY : (YS.map strOf).getD (4 * i.val + c.code.val) "" =
        strOf (YS.getD (4 * i.val + c.code.val) []) :=
      List.getD_map YS [] (n := 4 * i.val + c.code.val) strOf
    rw [eX, eY]
    refine ⟨hroot1 _ _ _ (hXL i c) hsX ?_, hroot1 _ _ _ (hYL i c) hsY ?_⟩
    · rw [← nthL_eq]
      exact hbX
    · rw [← nthL_eq]
      exact hbY

private theorem res3Of_eq (rs : List (List ℕ)) :
    res3Of rs = rs.map (List.map fun c => (c - 48) % 3) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show _ :: res3Of rs = _
    rw [ih]
    refine congrArg₂ List.cons ?_ rfl
    induction r with
    | nil => rfl
    | cons c r ihr =>
      show _ :: _ = _ :: _
      rw [ihr]
      rfl

private theorem lift_shape {rows : List (List ℕ)} (hs : shape12 rows = true) :
    (rows.length = 12 ∧ ∀ r ∈ rows, r.length = 12) ∧ shape12 (res3Of rows) = true := by
  obtain ⟨h1, h2⟩ := (shape12_iff _).1 hs
  refine ⟨⟨h1, h2⟩, (shape12_iff _).2 ⟨?_, ?_⟩⟩
  · rw [res3Of_eq]
    simpa using h1
  · intro r hr
    rw [res3Of_eq] at hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    simpa using h2 r0 hr0

private theorem liftArrsOf_getD (LR : List (List (List ℕ))) (i : ℕ) :
    (liftArrsOf (LR.map (List.map strOf))).getD i #[] = rowsArr z3Digit (LR.getD i []) := by
  have h : liftArrsOf (LR.map (List.map strOf)) = LR.map (rowsArr z3Digit) := by
    unfold liftArrsOf
    rw [List.map_map]
    rfl
  rw [h]
  exact List.getD_map LR [] (n := i) (rowsArr z3Digit)

private theorem rowsArr_z3 {rows : List (List ℕ)} (ha : asciiK rows = true)
    (hs : shape12 rows = true) :
    toMat 12 (rowsArr z3Digit rows) = digMat3 (res3Of rows) ∧
      rowsArr z3Digit rows = ofMat (digMat3 (res3Of rows)) := by
  obtain ⟨⟨hlen, hrow⟩, -⟩ := lift_shape hs
  have hascii := asciiK_iff.1 ha
  have hmem : ∀ i < 12, rows.getD i [] ∈ rows := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  have hT : toMat 12 (rowsArr z3Digit rows) = digMat3 (res3Of rows) := by
    ext i j
    have hi : i.val < 12 := i.isLt
    have hj : j.val < (rows.getD i.val []).length := by rw [hrow _ (hmem _ hi)]; exact j.isLt
    have e1 : toMat 12 (rowsArr z3Digit rows) i j = z3Digit (Char.ofNat
        ((rows.getD i.val []).getD j.val 0)) := by
      show ((rowsArr z3Digit rows).getD i.val #[]).getD j.val 0 = _
      exact getD_rowsArr z3Digit rows hj
    have hc : (rows.getD i.val []).getD j.val 0 < 128 :=
      hascii _ (hmem _ hi) _ (getD_mem_of_lt hj)
    have e2 : ((res3Of rows).getD i.val []).getD j.val 0 =
        ((rows.getD i.val []).getD j.val 0 - 48) % 3 := by
      rw [res3Of_eq]
      have : (rows.map (List.map fun c => (c - 48) % 3)).getD i.val [] =
          (rows.getD i.val []).map fun c => (c - 48) % 3 :=
        List.getD_map rows [] (n := i.val) (List.map fun c => (c - 48) % 3)
      rw [this]
      generalize rows.getD i.val [] = r at hj ⊢
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rw [e1]
    show _ = (((((res3Of rows).getD i.val []).getD j.val 0 : ℕ)) : ZMod 3)
    rw [e2, ZMod.natCast_mod]
    unfold z3Digit
    rw [toNat_ofNat_lt hc]
  refine ⟨hT, ?_⟩
  rw [← hT]
  symm
  refine ofMat_toMat 12 _ (by rw [rowsArr_size, hlen]) fun r hr => ?_
  obtain ⟨c, hc, hr'⟩ := rowsArr_row_size z3Digit rows hr
  rw [hr', hrow c hc]

theorem g24F3_sound {LRs : List (List String)} {RSs : List String}
    {PSs : List (List (String × String))}
    {LR : List (List (List Nat))} {Lb Lib : List Nat} {RS : List (List Nat)}
    {PS : List (List (List Nat × List Nat))}
    (hL : LRs = LR.map (List.map strOf)) (hR : RSs = RS.map strOf)
    (hP : PSs = PS.map (List.map fun p => (strOf p.1, strOf p.2)))
    (h : g24F3K LR Lb Lib RS PS = true) :
    unitCheckG LRs = true ∧ coverCheckG LRs RSs PSs = true ∧ kerCheckG LRs = true := by
  subst hL hR hP
  have h' := h
  unfold g24F3K at h'
  simp only [CFSG.KS.PK.andB_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.PK.allN_lqt_iff,
    CFSG.KS.PK.allLL_iff, CFSG.KS.PK.letB_eq, CFSG.KS.PK.notB_eq] at h'
  obtain ⟨-, hgen, hcube, hunit, hcover, hker1, hker2⟩ := h'
  set gs := liftArrsOf (LR.map (List.map strOf)) with hgs
  set Ml : ℕ → Matrix (Fin 12) (Fin 12) (ZMod 3) := fun i => digMat3 (res3Of (nthLL LR i))
    with hMl
  have hlb : ∀ i < 6, Canon3 (Lb.getD i 0) ∧ pkMat3 (Lb.getD i 0) = Ml i := by
    intro i hi
    obtain ⟨⟨ha, hs⟩, hb⟩ := hgen i hi
    rw [← nthV_eq, ← hb]
    refine canon3_pack (lift_shape hs).2 ?_
    intro r hr d hd
    rw [res3Of_eq] at hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact Nat.mod_lt _ (by norm_num)
  have hlib : ∀ i < 6, Canon3 (Lib.getD i 0) ∧ pkMat3 (Lib.getD i 0) = Ml i * (Ml i * Ml i) := by
    intro i hi
    obtain ⟨c1, m1⟩ := hlb i hi
    obtain ⟨c2, m2⟩ := canon3_mulF3 c1 c1
    obtain ⟨c3, m3⟩ := canon3_mulF3 c1 c2
    have e := hcube i hi
    simp only [nthV_eq] at e
    rw [← e]
    exact ⟨c3, by rw [m3, m2, m1]⟩
  have hlenLR : ∀ i < 6, i < LR.length := by
    intro i hi
    by_contra hcon
    obtain ⟨⟨ha, hs⟩, hb⟩ := hgen i hi
    have h0 : nthLL LR i = [] := by
      rw [nthLL_eq]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : LR.length ≤ i)]
    rw [h0] at hs
    have := ((shape12_iff _).1 hs).1
    simp at this
  have hArr : ∀ i < 6, gs.getD i #[] = ofMat (Ml i) ∧
      (gs.map fun A => mulArr 12 A (mulArr 12 A A)).getD i #[] =
        ofMat (Ml i * (Ml i * Ml i)) := by
    intro i hi
    obtain ⟨⟨ha, hs⟩, hb⟩ := hgen i hi
    have h1 : gs.getD i #[] = ofMat (Ml i) := by
      rw [hgs, liftArrsOf_getD, ← nthLL_eq]
      exact (rowsArr_z3 ha hs).2
    refine ⟨h1, ?_⟩
    have hlen : i < gs.length := by
      rw [hgs]
      unfold liftArrsOf
      simpa using hlenLR i hi
    have e : (gs.map fun A => mulArr 12 A (mulArr 12 A A)).getD i #[] =
        mulArr 12 (gs.getD i #[]) (mulArr 12 (gs.getD i #[]) (gs.getD i #[])) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rw [e, h1, mulArr_eq_ofMat, mulArr_eq_ofMat, toMat_ofMat, toMat_ofMat]
  set Fl : Fin 6 × Bool → Matrix (Fin 12) (Fin 12) (ZMod 3) := fun l =>
    if l.2 then Ml l.1.val else Ml l.1.val * (Ml l.1.val * Ml l.1.val) with hFl
  have hword : ∀ w : List (Fin 6 × Bool),
      wordArr3Of (LR.map (List.map strOf)) w = ofMat (wordProd Fl w) := by
    intro w
    unfold wordArr3Of
    have h1 := foldr_mulArr 12 (fun l : Fin 6 × Bool => if l.2 then gs.getD l.1.val #[] else
      (gs.map fun A => mulArr 12 A (mulArr 12 A A)).getD l.1.val #[]) w
    have h2 : wordProd (fun l : Fin 6 × Bool => toMat 12 (if l.2 then gs.getD l.1.val #[] else
        (gs.map fun A => mulArr 12 A (mulArr 12 A A)).getD l.1.val #[])) w = wordProd Fl w := by
      congr 1
      funext l
      by_cases hl : l.2 = true
      · simp only [hl, if_true, hFl]
        rw [(hArr l.1.val l.1.isLt).1, toMat_ofMat]
      · simp only [hl, Bool.false_eq_true, if_false, hFl]
        rw [(hArr l.1.val l.1.isLt).2, toMat_ofMat]
    rw [h2] at h1
    exact h1
  have hw3 := word3_eval hlb hlib
  refine ⟨?_, ?_, ?_⟩
  · unfold unitCheckG
    rw [List.all_eq_true]
    intro i _
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    obtain ⟨hA1, hA2⟩ := hArr i.val i.isLt
    obtain ⟨hu1, hu2⟩ := hunit i.val i.isLt
    obtain ⟨c1, m1⟩ := hlb i.val i.isLt
    obtain ⟨c2, m2⟩ := hlib i.val i.isLt
    have u1 : Ml i.val * (Ml i.val * (Ml i.val * Ml i.val)) = 1 := by
      have := congrArg pkMat3 hu1
      simp only [nthV_eq] at this
      rw [(canon3_mulF3 c1 c2).2, m1, m2, canon3_one3.2] at this
      exact this
    have u2 : Ml i.val * (Ml i.val * Ml i.val) * Ml i.val = 1 := by
      have := congrArg pkMat3 hu2
      simp only [nthV_eq] at this
      rw [(canon3_mulF3 c2 c1).2, m1, m2, canon3_one3.2] at this
      exact this
    constructor
    · show mulArr 12 (gs.getD i.val #[]) ((gs.map fun A => mulArr 12 A (mulArr 12 A A)).getD
        i.val #[]) = one12
      rw [hA1, hA2, mulArr_eq_ofMat, toMat_ofMat, toMat_ofMat, u1]
      rfl
    · show mulArr 12 ((gs.map fun A => mulArr 12 A (mulArr 12 A A)).getD i.val #[])
        (gs.getD i.val #[]) = one12
      rw [hA1, hA2, mulArr_eq_ofMat, toMat_ofMat, toMat_ofMat, u2]
      rfl
  · unfold coverCheckG
    rw [List.all_eq_true]
    intro r hr
    rw [decide_eq_true_iff]
    have hcov : (coverWords (List.map parseWord (List.map strOf RS))
        fun i => commWords (pairsOf (PS.map (List.map fun p => (strOf p.1, strOf p.2))) i)) =
        coverWords (m := 6) (RS.map fun r => parseWord (String.ofList (r.map Char.ofNat)))
          fun i => commWords ((PS.getD i.val []).map fun p =>
            (parseWord (String.ofList (p.1.map Char.ofNat)),
              parseWord (String.ofList (p.2.map Char.ofNat)))) := by
      congr 1
      · rw [List.map_map]
        rfl
      · funext i
        rw [pairsOf_map]
    have hmem : encG r ∈ coverK RS PS := by
      rw [coverK_eq]
      exact List.mem_map_of_mem (hcov ▸ hr)
    have h2 := congrArg pkMat3 (hcover (encG r) hmem)
    rw [(hw3 r).2, canon3_one3.2] at h2
    show wordArr3Of (LR.map (List.map strOf)) r = one12
    rw [hword]
    rw [show wordProd Fl r = 1 from h2]
    rfl
  · unfold kerCheckG
    have hd : encG dSq = [7, 7] := by decide +kernel
    obtain ⟨hz1, hz2⟩ := hw3 dSq
    rw [hd] at hz1 hz2
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [Bool.not_eq_true', decide_eq_false_iff_not, hword]
      intro heq
      have hW : wordProd Fl dSq = 1 := by
        have := congrArg (toMat 12) heq
        rwa [toMat_ofMat, show one12 = ofMat (1 : Matrix (Fin 12) (Fin 12) (ZMod 3)) from rfl,
          toMat_ofMat] at this
      have hZ : word3 Lb Lib [7, 7] = one3 :=
        canon3_inj hz1 canon3_one3.1 (by rw [hz2, hW, canon3_one3.2])
      rw [hZ] at hker1
      simp at hker1
    · rw [decide_eq_true_iff, hword, mulArr_eq_ofMat, toMat_ofMat]
      have h3 := congrArg pkMat3 hker2
      rw [(canon3_mulF3 hz1 hz1).2, hz2, canon3_one3.2] at h3
      show ofMat (wordProd Fl dSq * wordProd Fl dSq) = ofMat 1
      rw [show wordProd Fl dSq * wordProd Fl dSq = 1 from h3]

end CFSG.KC.Misc.G24

end
