module

public import Certificates.Data.NT44Model
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.NativeSchreierCard

public noncomputable section

namespace CFSG.GH74.GLS.NT44.PermutationInputs

open CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native
open PermutationNative
open CFSG.Certificates
open CFSG.Certificates.Native

@[expose] def ksPerm (i : Fin 2) : Equiv.Perm (Fin 2688) :=
  CFSG.Monster.B.Co2.permOfArr 2688 (PermutationNative.inputs ()).ks[i.val]!

@[expose] def Khat : Subgroup (Equiv.Perm (Fin 2688)) :=
  Subgroup.closure (Set.range ksPerm)

@[expose] def ksIn (i : Fin 2) : Khat :=
  ⟨ksPerm i, Subgroup.subset_closure ⟨i, rfl⟩⟩

@[expose] def presentationGenerator (i : Fin 2) : Khat :=
  (FreeGroup.lift ksIn)
    (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2
      (PermutationNative.inputs ()).fwd[i.val]!))

private theorem toLetters_schreierLetterCode_cons {j : ℕ}
    (a : CFSG.Certificates.SchreierLetter j) (w : List ℤ) :
    CFSG.Monster.B.Co2.toLetters j
      (CFSG.Certificates.schreierLetterCode a :: w) =
      a :: CFSG.Monster.B.Co2.toLetters j w := by
  obtain ⟨i, s⟩ := a
  cases s
  · have h : (-((i.val + 1 : ℕ) : ℤ)) ≠ 0 ∧ i.val + 1 ≤ j := by
      constructor <;> omega
    simp only [CFSG.Certificates.schreierLetterCode, Bool.false_eq_true, if_false,
      CFSG.Monster.B.Co2.toLetters, List.filterMap_cons, dite_eq_left h,
      Int.natAbs_neg, Int.natAbs_natCast]
    simp
  · have h : ((i.val + 1 : ℕ) : ℤ) ≠ 0 ∧ i.val + 1 ≤ j := by
      constructor <;> omega
    simp only [CFSG.Certificates.schreierLetterCode, if_true,
      CFSG.Monster.B.Co2.toLetters, List.filterMap_cons, dite_eq_left h,
      Int.natAbs_natCast]
    simp

theorem toLetters_map_schreierLetterCode {j : ℕ}
    (w : List (CFSG.Certificates.SchreierLetter j)) :
    CFSG.Monster.B.Co2.toLetters j
      (w.map CFSG.Certificates.schreierLetterCode) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.map_cons, toLetters_schreierLetterCode_cons, ih]

private theorem presentationGenerator_coe (i : Fin 2) :
    (presentationGenerator i : Equiv.Perm (Fin 2688)) =
      Quiver.SchreierGraph.evalWord (fun k : Fin 2 => ksPerm k)
        (CFSG.Monster.B.Co2.toLetters 2
          (PermutationNative.inputs ()).fwd[i.val]!) := by
  unfold presentationGenerator
  exact FreeGroup.lift_unique (f := fun k : Fin 2 => ksPerm k)
    (Khat.subtype.comp (FreeGroup.lift ksIn)) (fun k => rfl)

private theorem coe_lift_presentationGenerator (x : FreeGroup (Fin 2)) :
    ((FreeGroup.lift presentationGenerator) x : Equiv.Perm (Fin 2688)) =
      FreeGroup.lift
        (fun i : Fin 2 => (presentationGenerator i : Equiv.Perm (Fin 2688))) x :=
  FreeGroup.lift_unique
    (f := fun i : Fin 2 => (presentationGenerator i : Equiv.Perm (Fin 2688)))
    (Khat.subtype.comp (FreeGroup.lift presentationGenerator)) (fun _ => rfl)

theorem bridgeCheck_facts {rels : List (List ℤ)} {z : List ℤ}
    (hcheck : PermutationNative.bridgeCheck rels z = true) :
    let D := PermutationNative.inputs ()
    let KI := D.ks.map (invCand 2688)
    let V := D.fwd.map fun w => wordA 2688 D.ks KI w
    let VI := V.map (invCand 2688)
    let I := idA 2688
    let OK := D.sk.extract 0 2
    let OP := D.sp.extract 0 9
    shapeOK D = true ∧
      allLt 2 (fun i => isInvA 2688 D.ks[i]! KI[i]!) = true ∧
      coverCheck rels z D V VI I = true ∧
      restrictionCheck D OK OP KI = true := by
  dsimp only
  simp only [PermutationNative.bridgeCheck] at hcheck
  split_ifs at hcheck with hs
  · simp only [Bool.and_eq_true] at hcheck
    exact ⟨by simpa using hs, hcheck.1.1.1.1.1.1.1.1, hcheck.1.1.1.1.1.2, hcheck.1.1.1.1.2⟩

private theorem shapeOK_facts {D : PermutationNative.NT44Inputs}
    (h : shapeOK D = true) :
    D.ks.size = 2 ∧ D.fwd.size = 2 ∧ D.rev.size = 2 ∧
      wordsLettersOK 2 D.fwd = true := by
  unfold shapeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

private theorem coverCheck_facts {rels : List (List ℤ)} {z : List ℤ}
    {D : PermutationNative.NT44Inputs} {V VI : Array (Array ℕ)} {I : Array ℕ}
    (h : coverCheck rels z D V VI I = true) :
    allLt 2 (fun i => isInvA 2688 V[i]! VI[i]!) = true ∧
      rels.all (fun w => lettersOK 2 w &&
        eqA 2688 (wordA 2688 V VI w) I) = true ∧
      (lettersOK 2 z = true ∧ eqA 2688 (wordA 2688 V VI z) I = true) ∧
      allLt 2 (fun i => lettersOK 2 D.rev[i]! &&
        eqA 2688 (wordA 2688 V VI D.rev[i]!) D.ks[i]!) = true := by
  unfold coverCheck at h
  simp only [Bool.and_eq_true] at h
  tauto

theorem shapeOK_restriction_facts {D : PermutationNative.NT44Inputs}
    (h : shapeOK D = true) :
    D.pts.size = 448 ∧ allLt 448 (fun i => D.pts[i]! < 2688) = true ∧
      distinctValues D.pts = true ∧ D.sk.size = 7 ∧ D.bk.size = 4 ∧
      allLt 4 (fun i => D.bk[i]! < 448) = true ∧ distinctValues D.bk = true := by
  unfold shapeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  tauto

theorem distinctValues_injective {a : Array ℕ} (h : distinctValues a = true) :
    Function.Injective (fun i : Fin a.size => a[i.val]!) := by
  intro i j hij
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hdistinct_j : allLt j.val (fun k => a[j.val]! != a[k]!) = true :=
      allLt_spec h j.isLt
    have hcontra : a[j.val]! ≠ a[i.val]! := by
      have h' := allLt_spec hdistinct_j hlt
      rwa [bne_iff_ne] at h'
    exact hcontra hij.symm
  · have hdistinct_i : allLt i.val (fun k => a[i.val]! != a[k]!) = true :=
      allLt_spec h i.isLt
    have hcontra : a[i.val]! ≠ a[j.val]! := by
      have h' := allLt_spec hdistinct_i hgt
      rwa [bne_iff_ne] at h'
    exact hcontra hij

private theorem distinctValues_injective_nat {a : Array ℕ}
    (h : distinctValues a = true) {i j : ℕ}
    (hi : i < a.size) (hj : j < a.size) (hij : a[i]! = a[j]!) : i = j := by
  have hinj := distinctValues_injective h
  have hfin : (⟨i, hi⟩ : Fin a.size) = ⟨j, hj⟩ := hinj hij
  exact congrArg Fin.val hfin

private theorem restrictionCheck_facts {D : PermutationNative.NT44Inputs}
    {OK OP KI : Array (Array ℕ)}
    (h : restrictionCheck D OK OP KI = true) :
    allLt 2 (fun i => allLt 448 fun x =>
      D.pts[(OK[i]!)[x]!]! == (D.ks[i]!)[D.pts[x]!]!) = true ∧
      rawChainOK 448 OK D.sk D.bk D.wk 8 = true ∧
      (rawOrbitSizes 448 D.sk D.bk).prod = 322560 := by
  unfold restrictionCheck at h
  simp only [Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · tauto
  · tauto
  · have hprod : ((rawOrbitSizes 448 D.sk D.bk).prod == 322560) = true := by tauto
    simpa [beq_iff_eq] using hprod

private theorem presentation_word_rep
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (w : List ℤ) (hw : lettersOK 2 w = true) :
    let D := PermutationNative.inputs ()
    let KI := D.ks.map (invCand 2688)
    let V := D.fwd.map fun u => wordA 2688 D.ks KI u
    let VI := V.map (invCand 2688)
    Rep 2688 (wordA 2688 V VI w)
      (Quiver.SchreierGraph.evalWord
        (fun k : Fin 2 => (presentationGenerator k : Equiv.Perm (Fin 2688)))
        (CFSG.Monster.B.Co2.toLetters 2 w)) := by
  let D := PermutationNative.inputs ()
  let KI := D.ks.map (invCand 2688)
  let V := D.fwd.map fun u => wordA 2688 D.ks KI u
  let VI := V.map (invCand 2688)
  obtain ⟨hshape, hksInv, hcover, -⟩ := bridgeCheck_facts hcheck
  obtain ⟨hVInv, -, -, -⟩ := coverCheck_facts hcover
  obtain ⟨-, hfwdSize, -, hwordsFwd⟩ := shapeOK_facts hshape
  have hlettersFwd (i : Fin 2) : lettersOK 2 D.fwd[i.val]! = true := by
    have h : allLt D.fwd.size (fun k => lettersOK 2 D.fwd[k]!) = true := by
      simpa [wordsLettersOK] using hwordsFwd
    exact allLt_spec h (by rw [hfwdSize]; exact i.isLt)
  let gsK : ℕ → Equiv.Perm (Fin 2688) := fun h => permOfArr 2688 D.ks[h]!
  let gsV : ℕ → Equiv.Perm (Fin 2688) := fun h => permOfArr 2688 V[h]!
  have hksInvSpec (h : ℕ) (hh : h < 2) : isInvA 2688 D.ks[h]! KI[h]! = true :=
    allLt_spec hksInv hh
  have hS : ∀ h < 2, Rep 2688 D.ks[h]! (gsK h) := fun h hh =>
    (rep_permOfArr (hksInvSpec h hh)).1
  have hSinv : ∀ h < 2, Rep 2688 KI[h]! (gsK h)⁻¹ := fun h hh =>
    (rep_permOfArr (hksInvSpec h hh)).2
  have hVget (h : ℕ) (hh : h < 2) :
      V[h]! = wordA 2688 D.ks KI D.fwd[h]! := by
    change (D.fwd.map (fun w => wordA 2688 D.ks KI w))[h]! = _
    rw [getElem!_pos _ h (by rw [Array.size_map, hfwdSize]; exact hh),
      Array.getElem_map, getElem!_pos D.fwd h (by rw [hfwdSize]; exact hh)]
  have hVwordRep (h : ℕ) (hh : h < 2) :
      Rep 2688 V[h]! (Quiver.SchreierGraph.evalWord (fun k : Fin 2 => gsK k)
        (CFSG.Monster.B.Co2.toLetters 2 D.fwd[h]!)) := by
    have hw := rep_wordA (n := 2688) (S := D.ks) (Sinv := KI) (gs := gsK) (j := 2)
      hS hSinv D.fwd[h]! (hlettersFwd ⟨h, hh⟩)
    rw [hVget h hh]
    exact hw
  have hVauto (h : ℕ) (hh : h < 2) : Rep 2688 V[h]! (gsV h) :=
    (rep_permOfArr (allLt_spec hVInv hh)).1
  have hVIauto (h : ℕ) (hh : h < 2) : Rep 2688 VI[h]! (gsV h)⁻¹ :=
    (rep_permOfArr (allLt_spec hVInv hh)).2
  have hgsVgen (i : Fin 2) :
      gsV i.val = (presentationGenerator i : Equiv.Perm (Fin 2688)) := by
    apply Rep.unique (hVauto i.val i.isLt)
    rw [presentationGenerator_coe i]
    simpa [gsK, ksPerm, D] using hVwordRep i.val i.isLt
  have hwordV (u : List ℤ) (hu : lettersOK 2 u = true) :
      Rep 2688 (wordA 2688 V VI u)
        (Quiver.SchreierGraph.evalWord
          (fun k : Fin 2 => (presentationGenerator k : Equiv.Perm (Fin 2688)))
          (CFSG.Monster.B.Co2.toLetters 2 u)) := by
    have h := rep_wordA (n := 2688) (S := V) (Sinv := VI) (gs := gsV) (j := 2)
      hVauto hVIauto u hu
    have hfun : (fun k : Fin 2 => gsV k) =
        (fun k : Fin 2 => (presentationGenerator k : Equiv.Perm (Fin 2688))) :=
      funext hgsVgen
    rwa [hfun] at h
  exact hwordV w hw

theorem presentation_relators
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ r ∈ {r : FreeGroup (Fin 2) |
        r ∈ CFSG.LieType.Multipliers.L34.coverWs.map FreeGroup.mk},
      (FreeGroup.lift presentationGenerator) r = (1 : Khat) := by
  intro r hr
  change r ∈ CFSG.LieType.Multipliers.L34.coverWs.map FreeGroup.mk at hr
  rcases List.mem_map.mp hr with ⟨w, hw, rfl⟩
  let D := PermutationNative.inputs ()
  let KI := D.ks.map (invCand 2688)
  let V := D.fwd.map fun w => wordA 2688 D.ks KI w
  let VI := V.map (invCand 2688)
  let I := idA 2688
  obtain ⟨-, -, hcover, -⟩ := bridgeCheck_facts hcheck
  obtain ⟨-, hrel, -, -⟩ := coverCheck_facts hcover
  have hrelw : (lettersOK 2 (w.map CFSG.Certificates.schreierLetterCode) &&
      eqA 2688 (wordA 2688 V VI (w.map CFSG.Certificates.schreierLetterCode)) I) = true :=
    (List.all_eq_true.mp hrel) _ (List.mem_map_of_mem hw)
  have hrelParts := hrelw
  rw [Bool.and_eq_true] at hrelParts
  have hlettersCode : lettersOK 2 (w.map CFSG.Certificates.schreierLetterCode) = true :=
    hrelParts.1
  have heqCode :
      eqA 2688 (wordA 2688 V VI (w.map CFSG.Certificates.schreierLetterCode)) I = true :=
    hrelParts.2
  have hword := presentation_word_rep hcheck
    (w.map CFSG.Certificates.schreierLetterCode) hlettersCode
  rw [toLetters_map_schreierLetterCode w] at hword
  have heq : Quiver.SchreierGraph.evalWord
      (fun k : Fin 2 => (presentationGenerator k : Equiv.Perm (Fin 2688))) w = 1 :=
    (eqA_iff hword (rep_idA (n := 2688))).1 heqCode
  apply Subtype.ext
  rw [coe_lift_presentationGenerator]
  exact heq

theorem presentation_zThree
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (FreeGroup.lift presentationGenerator)
      (FreeGroup.mk CFSG.LieType.Multipliers.L34.zThree) = (1 : Khat) := by
  let D := PermutationNative.inputs ()
  let KI := D.ks.map (invCand 2688)
  let V := D.fwd.map fun w => wordA 2688 D.ks KI w
  let VI := V.map (invCand 2688)
  let I := idA 2688
  obtain ⟨-, -, hcover, -⟩ := bridgeCheck_facts hcheck
  obtain ⟨-, -, hz, -⟩ := coverCheck_facts hcover
  have hword := presentation_word_rep hcheck
    (CFSG.LieType.Multipliers.L34.zThree.map CFSG.Certificates.schreierLetterCode) hz.1
  rw [toLetters_map_schreierLetterCode CFSG.LieType.Multipliers.L34.zThree] at hword
  have heq : Quiver.SchreierGraph.evalWord
      (fun k : Fin 2 => (presentationGenerator k : Equiv.Perm (Fin 2688)))
        CFSG.LieType.Multipliers.L34.zThree = 1 :=
    (eqA_iff hword (rep_idA (n := 2688))).1 hz.2
  apply Subtype.ext
  rw [coe_lift_presentationGenerator]
  exact heq

theorem presentation_reverse
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ i : Fin 2,
      (FreeGroup.lift presentationGenerator)
        (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2
          (PermutationNative.inputs ()).rev[i.val]!)) = ksIn i := by
  intro i
  let D := PermutationNative.inputs ()
  let KI := D.ks.map (invCand 2688)
  let V := D.fwd.map fun w => wordA 2688 D.ks KI w
  let VI := V.map (invCand 2688)
  let I := idA 2688
  obtain ⟨-, hksInv, hcover, -⟩ := bridgeCheck_facts hcheck
  obtain ⟨-, -, -, hrev⟩ := coverCheck_facts hcover
  have hrevSpec := allLt_spec hrev i.isLt
  have hrevParts := hrevSpec
  rw [Bool.and_eq_true] at hrevParts
  have hlettersRev : lettersOK 2 D.rev[i.val]! = true := hrevParts.1
  have heqRev : eqA 2688 (wordA 2688 V VI D.rev[i.val]!) D.ks[i.val]! = true :=
    hrevParts.2
  have hword := presentation_word_rep hcheck D.rev[i.val]! hlettersRev
  have hksrep : Rep 2688 D.ks[i.val]! (ksPerm i) := by
    simpa [ksPerm, D] using (rep_permOfArr (allLt_spec hksInv i.isLt)).1
  have heq := (eqA_iff hword hksrep).1 heqRev
  apply Subtype.ext
  rw [coe_lift_presentationGenerator]
  exact heq

@[expose] noncomputable def restrictedKsPerm (i : Fin 2) : Equiv.Perm (Fin 448) :=
  CFSG.Monster.B.Co2.permOfArr 448 (PermutationNative.inputs ()).sk[i.val]!

@[expose] noncomputable def K448 : Subgroup (Equiv.Perm (Fin 448)) :=
  Subgroup.closure (Set.range restrictedKsPerm)

@[irreducible] noncomputable def pointEmbeddingVal
    (_hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) (x : Fin 448) : ℕ :=
  (PermutationNative.inputs ()).pts[x.val]!

private theorem pointEmbeddingVal_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) (x : Fin 448) :
    pointEmbeddingVal hcheck x = (PermutationNative.inputs ()).pts[x.val]! := by
  unfold pointEmbeddingVal
  rfl

@[expose] noncomputable def pointEmbeddingFun
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) (x : Fin 448) : Fin 2688 :=
  let D := PermutationNative.inputs ()
  have hshape := (bridgeCheck_facts hcheck).1
  have hbound : allLt 448 (fun i => D.pts[i]! < 2688) = true :=
    (shapeOK_restriction_facts hshape).2.1
  ⟨pointEmbeddingVal hcheck x, by
    rw [pointEmbeddingVal_eq hcheck x]
    exact of_decide_eq_true (allLt_spec hbound x.isLt)⟩

private theorem pointEmbeddingFun_val
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) (x : Fin 448) :
    (pointEmbeddingFun hcheck x).val = (PermutationNative.inputs ()).pts[x.val]! :=
  pointEmbeddingVal_eq hcheck x

theorem pointEmbeddingFun_injective
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Function.Injective (pointEmbeddingFun hcheck) := by
  intro x y hxy
  let D := PermutationNative.inputs ()
  have hshape := (bridgeCheck_facts hcheck).1
  have hpts := shapeOK_restriction_facts hshape
  have hsize : D.pts.size = 448 := hpts.1
  have hdistinct : distinctValues D.pts = true := hpts.2.2.1
  have hval' : pointEmbeddingVal hcheck x = pointEmbeddingVal hcheck y := by
    have h := hxy
    change (⟨pointEmbeddingVal hcheck x, _⟩ : Fin 2688) =
      ⟨pointEmbeddingVal hcheck y, _⟩ at h
    exact (Fin.mk.injEq ..).mp h
  have hval : (PermutationNative.inputs ()).pts[x.val]! =
      (PermutationNative.inputs ()).pts[y.val]! := by
    rwa [pointEmbeddingVal_eq hcheck x, pointEmbeddingVal_eq hcheck y] at hval'
  have hxyval : x.val = y.val :=
    distinctValues_injective_nat hdistinct
      (by rw [hsize]; exact x.isLt)
      (by rw [hsize]; exact y.isLt) hval
  exact Fin.ext hxyval

@[expose] noncomputable def pointEmbedding
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) : Fin 448 ↪ Fin 2688 :=
  { toFun := pointEmbeddingFun hcheck
    inj' := pointEmbeddingFun_injective hcheck }

theorem pointEmbedding_val
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (x : Fin 448) :
    (pointEmbedding hcheck x).val = (PermutationNative.inputs ()).pts[x.val]! := by
  exact pointEmbeddingFun_val hcheck x

theorem ksPerm_pointEmbedding
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ (i : Fin 2) (x : Fin 448),
      pointEmbedding hcheck (restrictedKsPerm i x) =
        ksPerm i (pointEmbedding hcheck x) := by
  intro i x
  let D := PermutationNative.inputs ()
  let KI := D.ks.map (invCand 2688)
  let OK := D.sk.extract 0 2
  let OP := D.sp.extract 0 9
  obtain ⟨hshape, hksInv, -, hrestriction⟩ := bridgeCheck_facts hcheck
  obtain ⟨hptsSize, hptsBound, hptsDistinct, hskSize, hbkSize, hbkBound, hbkDistinct⟩ :=
    shapeOK_restriction_facts hshape
  obtain ⟨hpres, hraw, hprod⟩ := restrictionCheck_facts hrestriction
  have hOKget : OK[i.val]! = D.sk[i.val]! := by
    dsimp only [OK]
    have hiExtract : i.val < (D.sk.extract 0 2).size := by
      have h2 : 2 ≤ D.sk.size := by rw [hskSize]; norm_num
      simp [Nat.min_eq_left h2]
      omega
    have hi7 : i.val < D.sk.size := by rw [hskSize]; omega
    rw [getElem!_pos _ i.val hiExtract, getElem!_pos D.sk i.val hi7,
      Array.getElem_extract]
    simp
  have hrepSK : Rep 448 D.sk[i.val]! (restrictedKsPerm i) := by
    have hF := chainCheckFacts hraw
    have hguard := hF.strong_inv i.val (by rw [hskSize]; omega)
    simpa [restrictedKsPerm, D] using (rep_permOfArr hguard).1
  have hrepKS : Rep 2688 D.ks[i.val]! (ksPerm i) := by
    simpa [ksPerm, D] using (rep_permOfArr (allLt_spec hksInv i.isLt)).1
  have hSKget : (D.sk[i.val]!)[x.val]! = (restrictedKsPerm i x).val := by
    simpa [restrictedKsPerm, D] using hrepSK.apply x.isLt
  have hpres_i : allLt 448 (fun y =>
      D.pts[(OK[i.val]!)[y]!]! == (D.ks[i.val]!)[D.pts[y]!]!) = true :=
    allLt_spec hpres i.isLt
  have hpres_x :
      (D.pts[(OK[i.val]!)[x.val]!]! == (D.ks[i.val]!)[D.pts[x.val]!]!) = true :=
    allLt_spec (n := 448)
      (p := fun j : Nat =>
        D.pts[(OK[i.val]!)[j]!]! == (D.ks[i.val]!)[D.pts[j]!]!)
      hpres_i (i := x.val) x.isLt
  have heq : D.pts[(restrictedKsPerm i x).val]! =
      (D.ks[i.val]!)[D.pts[x.val]!]! := by
    have h := hpres_x
    rw [hOKget, hSKget] at h
    simpa [beq_iff_eq] using h
  have hKSget : (D.ks[i.val]!)[(pointEmbedding hcheck x).val]! =
      (ksPerm i (pointEmbedding hcheck x)).val := by
    simpa [ksPerm, D] using hrepKS.apply (pointEmbedding hcheck x).isLt
  apply Fin.ext
  rw [pointEmbedding_val, heq, ← pointEmbedding_val]
  exact hKSget

theorem card_K448
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card K448 = 322560 := by
  let D := PermutationNative.inputs ()
  let OK := D.sk.extract 0 2
  let OP := D.sp.extract 0 9
  obtain ⟨hshape, -, -, hrestriction⟩ := bridgeCheck_facts hcheck
  obtain ⟨hptsSize, hptsBound, hptsDistinct, hskSize, hbkSize, hbkBound, hbkDistinct⟩ :=
    shapeOK_restriction_facts hshape
  obtain ⟨hpres, hraw, hprod⟩ := restrictionCheck_facts hrestriction
  have hbnd : ∀ a ∈ D.bk.toList, a < 448 := by
    intro a ha
    rw [Array.mem_toList_iff, Array.mem_iff_getElem] at ha
    obtain ⟨i, hi, hia⟩ := ha
    have hi4 : i < 4 := by rwa [hbkSize] at hi
    have hlt := allLt_spec hbkBound hi4
    have hia' : D.bk[i]! = a := by rw [getElem!_pos D.bk i hi, hia]
    rw [hia'] at hlt
    exact of_decide_eq_true hlt
  let b : List (Fin 448) :=
    D.bk.toList.pmap (fun a (ha : a < 448) => (⟨a, ha⟩ : Fin 448)) hbnd
  have hbListNodup : D.bk.toList.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro i j hij
    have hi : i.val < D.bk.size := by simp [Array.length_toList]
    have hj : j.val < D.bk.size := by simp [Array.length_toList]
    have hval : D.bk[i.val]! = D.bk[j.val]! := by
      have hget_i : D.bk.toList.get i = D.bk[i.val]! := by
        rw [List.get_eq_getElem, Array.getElem_toList, getElem!_pos D.bk i.val hi]
      have hget_j : D.bk.toList.get j = D.bk[j.val]! := by
        rw [List.get_eq_getElem, Array.getElem_toList, getElem!_pos D.bk j.val hj]
      rw [← hget_i, ← hget_j, hij]
    have hinj := distinctValues_injective hbkDistinct
    let i' : Fin D.bk.size := ⟨i.val, hi⟩
    let j' : Fin D.bk.size := ⟨j.val, hj⟩
    have hii : i' = j' := hinj hval
    exact Fin.ext (congrArg (fun z : Fin D.bk.size => z.val) hii)
  have hb : b.Nodup := by
    unfold b
    refine List.Nodup.pmap (fun a ha c hc h => ?_) hbListNodup
    exact congrArg (fun z : Fin 448 => z.val) h
  have hbase : (b.map Fin.val).toArray = D.bk := by
    unfold b
    rw [List.map_pmap, List.pmap_eq_map, List.map_id']
  have hk : 2 ≤ D.sk.size := by rw [hskSize]; norm_num
  let Q : RawSchreierDatum 448 :=
    RawSchreierDatum.ofArrays 448 (by decide) D.sk 2 hk b hb D.wk
  have hF := chainCheckFacts hraw
  have hA : ChainArrays Q OK D.sk D.bk D.wk := by
    have hA' := chainArrays_ofArrays (hn := by decide) (k := 2) (hk := hk)
      (base := b) (hb := hb) (W := D.wk) hF.strong_inv
    rwa [hbase] at hA'
  have hcard := card_originalSubgroup_of_chainOK hA (by decide : 0 < 8) hraw
  have hQ : Q.originalSubgroup = K448 := by
    dsimp only [Q]
    unfold RawSchreierDatum.originalSubgroup
    apply congrArg Subgroup.closure
    ext g
    rw [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, by simp [restrictedKsPerm, D]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.isLt, by simp [restrictedKsPerm, D]⟩
  rw [← hQ, hcard, hprod]

end CFSG.GH74.GLS.NT44.PermutationInputs
