module

public import CFSG.GH74.GLS.NT44.PermutationModel
public import CFSG.GH74.GLS.NT44.PermutationActions
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.StandardType.PSL3FourThreeFixedPoints

public noncomputable section

namespace CFSG.GH74.GLS.NT44.PermutationSylow

open PermutationInputs
open CFSG.GH74.GLS.NT44.PermutationNative
open CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native
open CFSG.Certificates
open CFSG.Certificates.Native

@[expose] def p0Perm (i : Fin 9) : Equiv.Perm (Fin 2688) :=
  CFSG.Monster.B.Co2.permOfArr 2688 (PermutationNative.inputs ()).p0[i.val]!

@[expose] def restrictedP0Perm (i : Fin 9) : Equiv.Perm (Fin 448) :=
  CFSG.Monster.B.Co2.permOfArr 448 (PermutationNative.inputs ()).sp[i.val]!

@[expose] def P0448 : Subgroup (Equiv.Perm (Fin 448)) :=
  Subgroup.closure (Set.range restrictedP0Perm)

private def D : NT44Inputs := PermutationNative.inputs ()

private abbrev KI : Array (Array Nat) := D.ks.map (invCand 2688)

private abbrev PI : Array (Array Nat) := D.p0.map (invCand 2688)

private abbrev LI : Array (Array Nat) := D.lifts.map (invCand 2688)

private abbrev sig : Array (Array (Array Nat)) :=
  Array.ofFn (n := 256) fun i =>
    Array.ofFn (n := 2) fun j =>
      compA 2688 (compA 2688 D.lifts[i.val]! D.ks[j.val]!) LI[i.val]!

private def ksFam : ℕ → Equiv.Perm (Fin 2688) :=
  fun h => if hh : h < 2 then ksPerm ⟨h, hh⟩ else 1

private structure ShapeFacts where
  spSize : (PermutationNative.inputs ()).sp.size = 10
  bpSize : (PermutationNative.inputs ()).bp.size = 3
  bpLt : allLt 3 (fun i => (PermutationNative.inputs ()).bp[i]! < 448) = true
  bpDistinct : distinctValues (PermutationNative.inputs ()).bp = true
  innLt : allLt 9 (fun i => (PermutationNative.inputs ()).inn[i]! < 256) = true

private theorem shape_facts
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) : ShapeFacts := by
  have h := hcheck
  simp only [PermutationNative.bridgeCheck] at h
  split_ifs at h with hs
  have hs' := hs
  unfold shapeOK at hs'
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hs'
  have hspSize : (PermutationNative.inputs ()).sp.size = 10 :=
    hs'.2.2.2.2.2.2.2.2.2.2.1
  have hbpSize : (PermutationNative.inputs ()).bp.size = 3 :=
    hs'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbpLt :
      allLt 3 (fun i => (PermutationNative.inputs ()).bp[i]! < 448) = true :=
    hs'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbpDistinct : distinctValues (PermutationNative.inputs ()).bp = true :=
    hs'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinnLt :
      allLt 9 (fun i => (PermutationNative.inputs ()).inn[i]! < 256) = true :=
    hs'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact
    { spSize := hspSize
      bpSize := hbpSize
      bpLt := hbpLt
      bpDistinct := hbpDistinct
      innLt := hinnLt }

private theorem bridge_checks
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    allLt 2 (fun i => isInvA 2688 D.ks[i]! KI[i]!) = true ∧
    allLt 9 (fun i => isInvA 2688 D.p0[i]! PI[i]!) = true ∧
    allLt 256 (fun i => isInvA 2688 D.lifts[i]! LI[i]!) = true ∧
    restrictionCheck D (D.sk.extract 0 2) (D.sp.extract 0 9) KI = true ∧
    innerCheck D PI sig = true := by
  have h := hcheck
  dsimp only [D, KI, PI, LI, sig]
  simp only [PermutationNative.bridgeCheck] at h
  split_ifs at h with hs
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hks, hp0, hlifts, -, hrestrict, -, -, -, hinner⟩ := h
  exact ⟨hks, hp0, hlifts, hrestrict, hinner⟩

private structure RestrictionFacts where
  p0Point : allLt 9 (fun i => allLt 448 fun x =>
    D.pts[((D.sp.extract 0 9)[i]!)[x]!]! == (D.p0[i]!)[D.pts[x]!]!) = true
  chain : rawChainOK 448 (D.sp.extract 0 9) D.sp D.bp D.wp 8 = true
  orbit : (rawOrbitSizes 448 D.sp D.bp).prod = 1024
  words : allLt 9 (fun i => lettersOK 2 D.pw[i]! &&
    eqA 2688 (wordA 2688 D.ks KI D.pw[i]!) D.p0[i]!) = true

private theorem restriction_facts
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) : RestrictionFacts := by
  have h := (bridge_checks hcheck).2.2.2.1
  unfold restrictionCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨-, hp0Point, -, -, hchain, horbit, hwords⟩ := h
  exact ⟨hp0Point, hchain, horbit, hwords⟩

private theorem p0_word_facts
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) :
    lettersOK 2 D.pw[i.val]! = true ∧
    eqA 2688 (wordA 2688 D.ks KI D.pw[i.val]!) D.p0[i.val]! = true := by
  have h := allLt_spec (restriction_facts hcheck).words i.isLt
  simpa only [Bool.and_eq_true] using h

private theorem p0_lift_coe
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) :
    ((FreeGroup.lift ksIn)
      (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2 D.pw[i.val]!)) :
        Equiv.Perm (Fin 2688)) = p0Perm i := by
  obtain ⟨hletters, heqA⟩ := p0_word_facts hcheck i
  let w := D.pw[i.val]!
  have hksInv := (bridge_checks hcheck).1
  have hksRep : ∀ h < 2, Rep 2688 D.ks[h]! (ksFam h) := by
    intro h hh
    rw [ksFam, dif_pos hh]
    exact (rep_permOfArr (allLt_spec hksInv hh)).1
  have hksInvRep : ∀ h < 2, Rep 2688 KI[h]! (ksFam h)⁻¹ := by
    intro h hh
    rw [ksFam, dif_pos hh]
    exact (rep_permOfArr (allLt_spec hksInv hh)).2
  have hword := rep_wordA (n := 2688) (S := D.ks) (Sinv := KI) (gs := ksFam)
    (j := 2) hksRep hksInvRep w hletters
  have hfun : (fun j : Fin 2 => ksFam j.val) = fun j : Fin 2 => ksPerm j := by
    funext j
    rw [ksFam, dif_pos j.isLt]
  rw [hfun] at hword
  have hp0Rep : Rep 2688 D.p0[i.val]! (p0Perm i) :=
    (rep_permOfArr (allLt_spec ((bridge_checks hcheck).2.1) i.isLt)).1
  have hcoe :
      ((FreeGroup.lift ksIn) (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2 w)) :
        Equiv.Perm (Fin 2688)) =
        Quiver.SchreierGraph.evalWord (fun j : Fin 2 => ksPerm j)
          (CFSG.Monster.B.Co2.toLetters 2 w) :=
    FreeGroup.lift_unique (f := fun j : Fin 2 => ksPerm j)
      (Khat.subtype.comp (FreeGroup.lift ksIn)) (fun j => rfl)
  calc
    ((FreeGroup.lift ksIn) (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2 w)) :
        Equiv.Perm (Fin 2688)) =
        Quiver.SchreierGraph.evalWord (fun j : Fin 2 => ksPerm j)
          (CFSG.Monster.B.Co2.toLetters 2 w) := hcoe
    _ = p0Perm i := (eqA_iff hword hp0Rep).1 heqA

private theorem p0_mem_Khat
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) : p0Perm i ∈ Khat := by
  have h := p0_lift_coe hcheck i
  rw [← h]
  exact (FreeGroup.lift ksIn
    (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2 D.pw[i.val]!))).2

@[expose] def p0In
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) : Khat :=
  ⟨p0Perm i, by exact p0_mem_Khat hcheck i⟩

@[expose] def P0
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) : Subgroup Khat :=
  Subgroup.closure (Set.range (p0In hcheck))

private def originalBase
    (hbound : ∀ i < 3, D.bp[i]! < 448) : List (Fin 448) :=
  List.ofFn fun i : Fin 3 => ⟨D.bp[i.val]!, hbound i.val i.isLt⟩

private theorem originalBase_nodup
    (hbp : D.bp.size = 3)
    (hbound : ∀ i < 3, D.bp[i]! < 448)
    (hdistinct : distinctValues D.bp = true) :
    (originalBase hbound).Nodup := by
  rw [originalBase, List.nodup_ofFn]
  intro i j hij
  have hi : i.val < D.bp.size := by rw [hbp]; exact i.isLt
  have hj : j.val < D.bp.size := by rw [hbp]; exact j.isLt
  have hval : D.bp[i.val]! = D.bp[j.val]! := congrArg Fin.val hij
  have hfin : (⟨i.val, hi⟩ : Fin D.bp.size) = ⟨j.val, hj⟩ :=
    PermutationInputs.distinctValues_injective hdistinct hval
  exact Fin.ext (congrArg Fin.val hfin)

private theorem originalBase_toArray
    (hbp : D.bp.size = 3)
    (hbound : ∀ i < 3, D.bp[i]! < 448) :
    ((originalBase hbound).map Fin.val).toArray = D.bp := by
  have hlist : (originalBase hbound).map Fin.val = D.bp.toList := by
    dsimp only [originalBase]
    rw [List.map_ofFn]
    apply List.ext_getElem
    · rw [List.length_ofFn, Array.length_toList, hbp]
    · intro i h1 h2
      rw [List.getElem_ofFn, Array.getElem_toList]
      change D.bp[i]! = D.bp[i]
      rw [getElem!_pos _ i (by simpa using h2)]
  rw [hlist, Array.toArray_toList]

private theorem p0_raw_chain
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    CFSG.Certificates.Native.rawChainOK 448
      ((PermutationNative.inputs ()).sp.extract 0 9)
      (PermutationNative.inputs ()).sp (PermutationNative.inputs ()).bp
      (PermutationNative.inputs ()).wp 8 = true ∧
    (CFSG.Certificates.Native.rawOrbitSizes 448
      (PermutationNative.inputs ()).sp (PermutationNative.inputs ()).bp).prod = 1024 :=
  ⟨by simpa [D] using (restriction_facts hcheck).chain,
   by simpa [D] using (restriction_facts hcheck).orbit⟩

private theorem card_P0448
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card P0448 = 1024 := by
  have hshape := shape_facts hcheck
  have hbpBound : ∀ i < 3, D.bp[i]! < 448 := fun i hi =>
    of_decide_eq_true (allLt_spec hshape.bpLt hi)
  let base := originalBase hbpBound
  have hb : base.Nodup :=
    originalBase_nodup hshape.bpSize hbpBound hshape.bpDistinct
  have hbaseEq : (base.map Fin.val).toArray = D.bp :=
    originalBase_toArray hshape.bpSize hbpBound
  have hspSize : D.sp.size = 10 := hshape.spSize
  have hk : 9 ≤ D.sp.size := by omega
  let Q : RawSchreierDatum 448 :=
    RawSchreierDatum.ofArrays 448 (by norm_num) D.sp 9 hk base hb D.wp
  have hchain := (p0_raw_chain hcheck).1
  have hchain' : rawChainOK 448 (D.sp.extract 0 9) D.sp
      (base.map Fin.val).toArray D.wp 8 = true := by
    rw [hbaseEq]
    exact hchain
  have hA : ChainArrays Q (D.sp.extract 0 9) D.sp
      (base.map Fin.val).toArray D.wp :=
    chainArrays_ofArrays (n := 448) (hn := by norm_num) (S := D.sp) (k := 9)
      (hk := hk) (base := base) (hb := hb) (W := D.wp)
      (hinv := (chainCheckFacts hchain').strong_inv)
  have hcard := card_originalSubgroup_of_chainOK hA (by norm_num) hchain'
  have hQsub : Q.originalSubgroup = P0448 := by
    rw [RawSchreierDatum.originalSubgroup, P0448]
    have hset : {g | g ∈ Q.original.toList} = Set.range restrictedP0Perm := by
      ext g
      dsimp only [Q]
      rw [Set.mem_setOf_eq, Set.mem_range, RawSchreierDatum.mem_ofArrays_original]
      constructor
      · rintro ⟨i, hi, hg⟩
        exact ⟨⟨i, hi⟩, hg⟩
      · rintro ⟨i, hg⟩
        exact ⟨i.val, i.isLt, hg⟩
    rw [hset]
  rw [hQsub, hbaseEq] at hcard
  exact hcard.trans (p0_raw_chain hcheck).2

private theorem inner_index_lt
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) : (PermutationNative.inputs ()).inn[i.val]! < 256 :=
  of_decide_eq_true (allLt_spec (shape_facts hcheck).innLt i.isLt)

private def innerIndex
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) : Fin 256 :=
  ⟨(PermutationNative.inputs ()).inn[i.val]!, inner_index_lt hcheck i⟩

private theorem sig_get (q : ℕ) (hq : q < 256) (j : ℕ) (hj : j < 2) :
    (sig[q]!)[j]! = compA 2688 (compA 2688 D.lifts[q]! D.ks[j]!) LI[q]! := by
  rw [sig]
  rw [getElem!_pos _ q (by rw [Array.size_ofFn]; exact hq), Array.getElem_ofFn]
  rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn]

private theorem inner_check_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) (j : Fin 2) :
    eqA 2688
      (compA 2688 (compA 2688 D.p0[i.val]! D.ks[j.val]!) PI[i.val]!)
      ((sig[D.inn[i.val]!]!)[j.val]!) = true := by
  have h := (bridge_checks hcheck).2.2.2.2
  unfold innerCheck at h
  exact allLt_spec (allLt_spec h i.isLt) j.isLt

private theorem inner_pair_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) (j : Fin 2) :
    p0Perm i * ksPerm j * (p0Perm i)⁻¹ =
      PermutationActions.liftPerm (innerIndex hcheck i) * ksPerm j *
        (PermutationActions.liftPerm (innerIndex hcheck i))⁻¹ := by
  have hksInv := (bridge_checks hcheck).1
  have hp0Inv := (bridge_checks hcheck).2.1
  have hlInv := (bridge_checks hcheck).2.2.1
  have hrepP0 := (rep_permOfArr (allLt_spec hp0Inv i.isLt)).1
  have hrepP0Inv := (rep_permOfArr (allLt_spec hp0Inv i.isLt)).2
  have hrepKs := (rep_permOfArr (allLt_spec hksInv j.isLt)).1
  have hrepL :=
    (rep_permOfArr (allLt_spec hlInv (innerIndex hcheck i).isLt)).1
  have hrepLInv :=
    (rep_permOfArr (allLt_spec hlInv (innerIndex hcheck i).isLt)).2
  have hL : Rep 2688
      (compA 2688 (compA 2688 D.p0[i.val]! D.ks[j.val]!) PI[i.val]!)
      (p0Perm i * ksPerm j * (p0Perm i)⁻¹) :=
    rep_compA (rep_compA hrepP0 hrepKs) hrepP0Inv
  have hR : Rep 2688 ((sig[D.inn[i.val]!]!)[j.val]!)
      (PermutationActions.liftPerm (innerIndex hcheck i) * ksPerm j *
        (PermutationActions.liftPerm (innerIndex hcheck i))⁻¹) := by
    rw [sig_get D.inn[i.val]! (innerIndex hcheck i).isLt j.val j.isLt]
    exact rep_compA (rep_compA hrepL hrepKs) hrepLInv
  exact (eqA_iff hL hR).1 (inner_check_eq hcheck i j)

private theorem inner_action_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (i : Fin 9) :
    MulAut.conj (p0In hcheck i) =
      PermutationActions.alpha hcheck (innerIndex hcheck i) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  have hEqOn : Set.EqOn (MulAut.conj (p0Perm i)).toMonoidHom
      (MulAut.conj (PermutationActions.liftPerm (innerIndex hcheck i))).toMonoidHom
      (Khat : Set (Equiv.Perm (Fin 2688))) := by
    change Set.EqOn (MulAut.conj (p0Perm i)).toMonoidHom
      (MulAut.conj (PermutationActions.liftPerm (innerIndex hcheck i))).toMonoidHom
      (Subgroup.closure (Set.range ksPerm) : Set (Equiv.Perm (Fin 2688)))
    refine MonoidHom.eqOn_closure (s := Set.range ksPerm) ?_
    rintro y ⟨j, rfl⟩
    simpa [MulAut.conj_apply] using inner_pair_eq hcheck i j
  have hx := hEqOn x.2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx
  have hleft : (MulAut.conj (p0In hcheck i) x : Equiv.Perm (Fin 2688)) =
      p0Perm i * (x : Equiv.Perm (Fin 2688)) * (p0Perm i)⁻¹ := by
    simp [MulAut.conj_apply, p0In]
  have halpha := (PermutationActions.original_actions_spec hcheck).1
    (innerIndex hcheck i) x
  rw [hleft, halpha]
  exact hx

private theorem p0_ambient_map
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (P0 hcheck).map Khat.subtype = Subgroup.closure (Set.range p0Perm) := by
  rw [P0, MonoidHom.map_closure,
    ← Set.range_comp' (g := Khat.subtype) (f := p0In hcheck)]
  rfl

private theorem p0_conj_image_le_T
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (P0 hcheck).map (MulAut.conj : Khat →* MulAut Khat) ≤
      PermutationActions.T hcheck := by
  rw [P0, MonoidHom.map_closure,
    ← Set.range_comp' (g := (MulAut.conj : Khat →* MulAut Khat))
      (f := p0In hcheck)]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨i, rfl⟩
  change MulAut.conj (p0In hcheck i) ∈ PermutationActions.T hcheck
  rw [inner_action_eq hcheck i]
  exact (PermutationActions.original_actions_spec hcheck).2.2.1
    (innerIndex hcheck i)

private theorem sp_extract_get
    (hsp : (PermutationNative.inputs ()).sp.size = 10) {i : ℕ} (hi : i < 9) :
    ((PermutationNative.inputs ()).sp.extract 0 9)[i]! =
      (PermutationNative.inputs ()).sp[i]! := by
  rw [getElem!_pos _ i (by rw [Array.size_extract]; omega),
    getElem!_pos _ i (by omega), Array.getElem_extract]
  simp

private theorem p0_raw_point_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    let D := PermutationNative.inputs ()
    ∀ (i : Fin 9) (x : Fin 448),
      D.pts[(D.sp[i.val]!)[x.val]!]! = (D.p0[i.val]!)[D.pts[x.val]!]! := by
  dsimp only
  intro i x
  have h := allLt_spec
    (allLt_spec (restriction_facts hcheck).p0Point i.isLt) x.isLt
  dsimp only [D] at h
  rw [beq_iff_eq] at h
  rw [sp_extract_get (shape_facts hcheck).spSize i.isLt] at h
  exact h

private theorem p0_pointEmbedding
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ (i : Fin 9) (x : Fin 448),
      pointEmbedding hcheck (restrictedP0Perm i x) =
        p0Perm i (pointEmbedding hcheck x) := by
  intro i x
  let D := PermutationNative.inputs ()
  have hspSize : D.sp.size = 10 := by
    simpa [D] using (shape_facts hcheck).spSize
  have hchain : rawChainOK 448 (D.sp.extract 0 9) D.sp D.bp D.wp 8 = true := by
    simpa [D] using (p0_raw_chain hcheck).1
  have hguard : isInvA 448 D.sp[i.val]! (rawInvs 448 D.sp)[i.val]! = true :=
    (chainCheckFacts hchain).strong_inv i.val (by rw [hspSize]; omega)
  have hrepSP : Rep 448 D.sp[i.val]! (restrictedP0Perm i) := by
    simpa [restrictedP0Perm, D] using (rep_permOfArr hguard).1
  have hrepP0 : Rep 2688 D.p0[i.val]! (p0Perm i) :=
    (rep_permOfArr (allLt_spec ((bridge_checks hcheck).2.1) i.isLt)).1
  have hSPget : (D.sp[i.val]!)[x.val]! = (restrictedP0Perm i x).val := by
    simpa [restrictedP0Perm, D] using hrepSP.apply x.isLt
  have hraw : D.pts[(D.sp[i.val]!)[x.val]!]! =
      (D.p0[i.val]!)[D.pts[x.val]!]! := by
    simpa [D] using p0_raw_point_eq hcheck i x
  have hraw' : D.pts[(restrictedP0Perm i x).val]! =
      (D.p0[i.val]!)[D.pts[x.val]!]! := by
    rw [← hSPget]
    exact hraw
  have hP0get : (D.p0[i.val]!)[(pointEmbedding hcheck x).val]! =
      (p0Perm i (pointEmbedding hcheck x)).val := by
    simpa [p0Perm, D] using hrepP0.apply (pointEmbedding hcheck x).isLt
  dsimp only [D] at hraw' hP0get
  apply Fin.ext
  rw [pointEmbedding_val, hraw', ← pointEmbedding_val]
  exact hP0get

private theorem p0_initial_finite_spec
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (∀ i : Fin 9,
      (FreeGroup.lift ksIn)
        (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2
          (PermutationNative.inputs ()).pw[i.val]!)) = p0In hcheck i) ∧
    (P0 hcheck).map Khat.subtype = Subgroup.closure (Set.range p0Perm) ∧
    Nat.card P0448 = 1024 ∧
    (∀ i : Fin 9, ∃ q : Fin 256,
      q.val = (PermutationNative.inputs ()).inn[i.val]! ∧
      MulAut.conj (p0In hcheck i) = PermutationActions.alpha hcheck q) ∧
    (P0 hcheck).map (MulAut.conj : Khat →* MulAut Khat) ≤ PermutationActions.T hcheck := by
  refine ⟨?_, p0_ambient_map hcheck, card_P0448 hcheck, ?_, p0_conj_image_le_T hcheck⟩
  · intro i
    apply Subtype.ext
    simpa [D, p0In] using p0_lift_coe hcheck i
  · intro i
    exact ⟨innerIndex hcheck i, rfl, inner_action_eq hcheck i⟩

theorem original_p0_finite_spec
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (∀ i : Fin 9,
      (FreeGroup.lift ksIn)
        (FreeGroup.mk (CFSG.Monster.B.Co2.toLetters 2
          (PermutationNative.inputs ()).pw[i.val]!)) = p0In hcheck i) ∧
    (P0 hcheck).map Khat.subtype = Subgroup.closure (Set.range p0Perm) ∧
    (∀ (i : Fin 9) (x : Fin 448),
      pointEmbedding hcheck (restrictedP0Perm i x) =
        p0Perm i (pointEmbedding hcheck x)) ∧
    Nat.card P0448 = 1024 ∧
    (∀ i : Fin 9, ∃ q : Fin 256,
      q.val = (PermutationNative.inputs ()).inn[i.val]! ∧
      MulAut.conj (p0In hcheck i) = PermutationActions.alpha hcheck q) ∧
    (P0 hcheck).map (MulAut.conj : Khat →* MulAut Khat) ≤ PermutationActions.T hcheck := by
  obtain ⟨hmem, hamb, hcard, hinner, hle⟩ := p0_initial_finite_spec hcheck
  exact ⟨hmem, hamb, p0_pointEmbedding hcheck, hcard, hinner, hle⟩

private theorem factorization_two_322560 : (322560 : ℕ).factorization 2 = 10 := by
  rw [show (322560 : ℕ) = 2 ^ 10 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

private theorem factorization_two_241920 : (241920 : ℕ).factorization 2 = 8 := by
  rw [show (241920 : ℕ) = 2 ^ 8 * 945 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

private theorem original_model_counts
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card Khat = 322560 ∧ Nat.card (Subgroup.center Khat) = 16 ∧
      Nat.card (MulAut Khat) ∣ 241920 := by
  obtain ⟨e, -, -, -, -⟩ :=
    PermutationModel.fullTwoCover_equiv_original_model hcheck
  obtain ⟨-, -, -, -, -, hsurjS, -, hkerCenter, hkerCard, hcomm, -, hFcard, -⟩ :=
    (modelStructure : _)
  have hKhatCard : Nat.card Khat = 322560 := by
    rw [← Nat.card_congr e.toEquiv, hFcard]
  have hcenterF : Nat.card (Subgroup.center FullTwoCover) = 16 := by
    rw [← hkerCenter]
    exact hkerCard
  have hcenterKhat : Nat.card (Subgroup.center Khat) = 16 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcenterF]
  have hperfect : Group.IsPerfect FullTwoCover := ⟨hcomm⟩
  have hInjCQ : Function.Injective
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
        FullTwoCover) :=
    @CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective
      FullTwoCover _ hperfect
  have hqbarKer : FullTwoCover ⧸ fullTwoCoverToS.ker ≃*
      CFSG.ComponentClassification.PSL3Four.S :=
    QuotientGroup.quotientKerEquivOfSurjective (φ := fullTwoCoverToS) hsurjS
  let hqbar : FullTwoCover ⧸ Subgroup.center FullTwoCover ≃*
      CFSG.ComponentClassification.PSL3Four.S :=
    (QuotientGroup.quotientMulEquivOfEq hkerCenter).symm.trans hqbarKer
  let autToS : MulAut Khat →* MulAut CFSG.ComponentClassification.PSL3Four.S :=
    (MulAut.congr hqbar).toMonoidHom.comp
      ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
        FullTwoCover).comp (MulAut.congr e.symm).toMonoidHom)
  have hInject : Function.Injective autToS := by
    intro x y hxy
    have h1 : (MulAut.congr hqbar)
        ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
          FullTwoCover) ((MulAut.congr e.symm) x)) =
        (MulAut.congr hqbar)
          ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
            FullTwoCover) ((MulAut.congr e.symm) y)) := by
      simpa [autToS, MonoidHom.comp_apply] using hxy
    have h2 := (MulAut.congr hqbar).injective h1
    have h3 := hInjCQ h2
    exact (MulAut.congr e.symm).injective h3
  have hcardDvd : Nat.card (MulAut Khat) ∣
      Nat.card (MulAut CFSG.ComponentClassification.PSL3Four.S) :=
    Subgroup.card_dvd_of_injective autToS hInject
  have hcardS : Nat.card (MulAut CFSG.ComponentClassification.PSL3Four.S) = 241920 :=
    CFSG.StandardType.PSL3FourThree.card_mulAut_S
  have hAutDvd : Nat.card (MulAut Khat) ∣ 241920 := by
    rw [← hcardS]
    exact hcardDvd
  exact ⟨hKhatCard, hcenterKhat, hAutDvd⟩

private theorem card_P0
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card (P0 hcheck) = 1024 := by
  obtain ⟨-, r, -, -, hact⟩ :=
    PermutationModel.fullTwoCover_equiv_original_model hcheck
  let rho : Khat →* Equiv.Perm (Fin 448) := K448.subtype.comp r.toMonoidHom
  have hrho (i : Fin 9) : rho (p0In hcheck i) = restrictedP0Perm i := by
    apply Equiv.ext
    intro x
    apply (pointEmbedding hcheck).injective
    change pointEmbedding hcheck (((r (p0In hcheck i)) :
      Equiv.Perm (Fin 448)) x) =
      pointEmbedding hcheck (restrictedP0Perm i x)
    rw [hact, p0_pointEmbedding]
    rfl
  have hmap : (P0 hcheck).map rho = P0448 := by
    rw [P0, P0448, MonoidHom.map_closure,
      ← Set.range_comp' (g := rho) (f := p0In hcheck)]
    rw [show (fun i => rho (p0In hcheck i)) = restrictedP0Perm from funext hrho]
  have hinj : Function.Injective rho := by
    intro x y hxy
    apply r.injective
    exact K448.subtype_injective hxy
  have hcard := Subgroup.card_map_of_injective (K := P0 hcheck) (f := rho) hinj
  rw [hmap] at hcard
  exact hcard.symm.trans (card_P0448 hcheck)

private theorem p0_card_eq_prime_part
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card (P0 hcheck) = 2 ^ (Nat.card Khat).factorization 2 := by
  rw [card_P0 hcheck, (original_model_counts hcheck).1,
    factorization_two_322560]
  norm_num

@[expose] def p0Sylow
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) : Sylow 2 Khat :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (P0 hcheck) (by exact p0_card_eq_prime_part hcheck)

private theorem t_card_eq_prime_part
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card (PermutationActions.T hcheck) =
      2 ^ (Nat.card (MulAut Khat)).factorization 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, hTcard⟩ :=
    PermutationActions.original_actions_spec hcheck
  have hAutDvd : Nat.card (MulAut Khat) ∣ 241920 :=
    (original_model_counts hcheck).2.2
  have hAut0 : Nat.card (MulAut Khat) ≠ 0 := Nat.card_pos.ne'
  have h2410 : (241920 : ℕ) ≠ 0 := by norm_num
  have hle : (Nat.card (MulAut Khat)).factorization 2 ≤ 8 := by
    have h := (Nat.factorization_le_iff_dvd hAut0 h2410).mpr hAutDvd 2
    rwa [factorization_two_241920] at h
  have h256 : 2 ^ 8 ∣ Nat.card (MulAut Khat) := by
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num, ← hTcard]
    exact Subgroup.card_subgroup_dvd_card (PermutationActions.T hcheck)
  have hge : 8 ≤ (Nat.card (MulAut Khat)).factorization 2 := by
    rw [← Nat.prime_two.pow_dvd_iff_le_factorization hAut0]
    exact h256
  have hfacAut : (Nat.card (MulAut Khat)).factorization 2 = 8 :=
    le_antisymm hle hge
  rw [hTcard, hfacAut]
  norm_num

@[expose] def tSylow
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) : Sylow 2 (MulAut Khat) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (PermutationActions.T hcheck) (by exact t_card_eq_prime_part hcheck)

private instance factPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem p0_comap_conj
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (PermutationActions.T hcheck).comap (MulAut.conj : Khat →* MulAut Khat) =
      P0 hcheck := by
  let j : Khat →* MulAut Khat := MulAut.conj
  have hcenter : Nat.card (Subgroup.center Khat) = 16 :=
    (original_model_counts hcheck).2.1
  have hkerEq : j.ker = Subgroup.center Khat := by
    simpa [j] using (CFSG.GroupTheory.ker_conj_eq_center (G := Khat))
  have hker : IsPGroup 2 j.ker := by
    rw [hkerEq]
    exact IsPGroup.of_card (n := 4) (by rw [hcenter]; norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, hTcard⟩ :=
    PermutationActions.original_actions_spec hcheck
  have hT : IsPGroup 2 (PermutationActions.T hcheck) :=
    IsPGroup.of_card (n := 8) (by rw [hTcard]; norm_num)
  have hcomap : IsPGroup 2 ((PermutationActions.T hcheck).comap j) :=
    IsPGroup.comap_of_ker_isPGroup hT j hker
  have hle : (p0Sylow hcheck : Subgroup Khat) ≤
      (PermutationActions.T hcheck).comap j := by
    simp only [p0Sylow, Sylow.coe_ofCard]
    exact (Subgroup.map_le_iff_le_comap (f := j)
      (H := PermutationActions.T hcheck)).1 (p0_conj_image_le_T hcheck)
  have hmax := Sylow.is_maximal' (p0Sylow hcheck) hcomap hle
  simp only [p0Sylow, Sylow.coe_ofCard] at hmax
  exact hmax

private theorem p0_map_conj_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    (P0 hcheck).map (MulAut.conj : Khat →* MulAut Khat) =
      (MulAut.conj : Khat →* MulAut Khat).range ⊓ PermutationActions.T hcheck := by
  rw [← p0_comap_conj hcheck]
  exact Subgroup.map_comap_eq (f := (MulAut.conj : Khat →* MulAut Khat))
    (H := PermutationActions.T hcheck)

private theorem p0_map_beta_eq
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true)
    (β : MulAut Khat) (hβ : β ∈ PermutationActions.T hcheck) :
    (P0 hcheck).map β.toMonoidHom = P0 hcheck := by
  let j : Khat →* MulAut Khat := MulAut.conj
  have hpre := p0_comap_conj hcheck
  have hconj : ∀ (γ : MulAut Khat) (p : Khat), j (γ p) = γ * j p * γ⁻¹ := by
    intro γ p
    apply MulEquiv.ext
    intro y
    simp only [j, MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  have hstep : ∀ (γ : MulAut Khat), γ ∈ PermutationActions.T hcheck →
      (P0 hcheck).map γ.toMonoidHom ≤ P0 hcheck := by
    intro γ hγ x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hmem : γ p ∈ (PermutationActions.T hcheck).comap j := by
      rw [Subgroup.mem_comap]
      rw [hconj γ p]
      exact (PermutationActions.T hcheck).mul_mem
        ((PermutationActions.T hcheck).mul_mem hγ
          ((p0_conj_image_le_T hcheck) (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)))
        ((PermutationActions.T hcheck).inv_mem hγ)
    rwa [hpre] at hmem
  apply le_antisymm
  · exact hstep β hβ
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨β⁻¹ x, ?_, ?_⟩
    · exact hstep β⁻¹ ((PermutationActions.T hcheck).inv_mem hβ)
        (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    · simp

private theorem p0_lift_mem_normalizer
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    ∀ i : Fin 256,
      PermutationActions.liftPerm i ∈ Subgroup.normalizer
        ((Subgroup.closure (Set.range p0Perm) :
          Subgroup (Equiv.Perm (Fin 2688))) : Set (Equiv.Perm (Fin 2688))) := by
  intro i
  let H : Subgroup (Equiv.Perm (Fin 2688)) := Subgroup.closure (Set.range p0Perm)
  let g : Equiv.Perm (Fin 2688) := PermutationActions.liftPerm i
  let β : MulAut Khat := PermutationActions.alpha hcheck i
  have hβ : β ∈ PermutationActions.T hcheck :=
    (PermutationActions.original_actions_spec hcheck).2.2.1 i
  have hinv : (P0 hcheck).map β.toMonoidHom = P0 hcheck :=
    p0_map_beta_eq hcheck β hβ
  have hcomp : (MulAut.conj g).toMonoidHom.comp Khat.subtype =
      Khat.subtype.comp β.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply Equiv.ext
    intro y
    change (MulAut.conj g ((x : Khat) : Equiv.Perm (Fin 2688))) y =
      ((β x : Khat) : Equiv.Perm (Fin 2688)) y
    rw [MulAut.conj_apply]
    have hspec := congrArg (fun p : Equiv.Perm (Fin 2688) => p y)
      ((PermutationActions.original_actions_spec hcheck).1 i x)
    simpa [g, β] using hspec.symm
  have hmap : H.map (MulAut.conj g) = H := by
    have hH : H = (P0 hcheck).map Khat.subtype := (p0_ambient_map hcheck).symm
    rw [hH, Subgroup.map_map]
    change Subgroup.map ((MulAut.conj g).toMonoidHom.comp Khat.subtype)
      (P0 hcheck) = Subgroup.map Khat.subtype (P0 hcheck)
    rw [hcomp, ← Subgroup.map_map, hinv]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hmap

theorem original_p0_sylow_preimage_spec
    (hcheck : PermutationNative.bridgeCheck
      (CFSG.LieType.Multipliers.L34.coverWs.map
        (List.map CFSG.Certificates.schreierLetterCode))
      (CFSG.LieType.Multipliers.L34.zThree.map
        CFSG.Certificates.schreierLetterCode) = true) :
    Nat.card Khat = 322560 ∧
    Nat.card (P0 hcheck) = 1024 ∧
    Nat.card (Subgroup.center Khat) = 16 ∧
    Nat.card (MulAut Khat) ∣ 241920 ∧
    (p0Sylow hcheck : Subgroup Khat) = P0 hcheck ∧
    (tSylow hcheck : Subgroup (MulAut Khat)) = PermutationActions.T hcheck ∧
    (PermutationActions.T hcheck).comap (MulAut.conj : Khat →* MulAut Khat) = P0 hcheck ∧
    (P0 hcheck).map (MulAut.conj : Khat →* MulAut Khat) =
      (MulAut.conj : Khat →* MulAut Khat).range ⊓ PermutationActions.T hcheck ∧
    ((PermutationActions.T hcheck).comap (MulAut.conj : Khat →* MulAut Khat)).map
        Khat.subtype = Subgroup.closure (Set.range p0Perm) ∧
    (∀ β : MulAut Khat, β ∈ PermutationActions.T hcheck →
      (P0 hcheck).map β.toMonoidHom = P0 hcheck) ∧
    ∀ i : Fin 256,
      PermutationActions.liftPerm i ∈ Subgroup.normalizer
        ((Subgroup.closure (Set.range p0Perm) :
          Subgroup (Equiv.Perm (Fin 2688))) : Set (Equiv.Perm (Fin 2688))) := by
  obtain ⟨hKhat, hcenter, hAutDvd⟩ := original_model_counts hcheck
  have hP0 : Nat.card (P0 hcheck) = 1024 := card_P0 hcheck
  have hpre := p0_comap_conj hcheck
  have himage := p0_map_conj_eq hcheck
  have hinv := p0_map_beta_eq hcheck
  have hnorm := p0_lift_mem_normalizer hcheck
  refine ⟨hKhat, hP0, hcenter, hAutDvd, ?_, ?_, hpre, himage, ?_, hinv, hnorm⟩
  · simp only [p0Sylow, Sylow.coe_ofCard]
  · simp only [tSylow, Sylow.coe_ofCard]
  · rw [hpre]
    exact p0_ambient_map hcheck

end CFSG.GH74.GLS.NT44.PermutationSylow
