module

public import CFSG.GH74.GLS.NT44.PermutationSylow
public import Certificates.Certificate1212004

public section

namespace CFSG.GH74.GLS.NT44.PermutationCommutator

open CFSG.GH74.GLS.NT44
open CFSG.GH74.GLS.NT44.PermutationInputs
open CFSG.GH74.GLS.NT44.PermutationActions
open CFSG.GH74.GLS.NT44.PermutationSylow
open CFSG.GH74.GLS.NT44.PermutationNative
open CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native
open CFSG.Certificates

abbrev BridgeCheck : Prop :=
  PermutationNative.bridgeCheck
    (CFSG.LieType.Multipliers.L34.coverWs.map
      (List.map CFSG.Certificates.schreierLetterCode))
    (CFSG.LieType.Multipliers.L34.zThree.map
      CFSG.Certificates.schreierLetterCode) = true

theorem positiveWordsOK_spec {ws : Array (List Int)}
    (h : positiveWordsOK ws = true) :
    ∀ i < ws.size, ∀ l ∈ ws[i]!, l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by
  intro i hi l hl
  unfold positiveWordsOK at h
  have h1 := allLt_spec h hi
  have h2 := List.all_eq_true.mp h1 l hl
  simp only [Bool.or_eq_true, beq_iff_eq] at h2
  tauto

theorem toLetters_positive {j : ℕ} {w : List Int}
    (h : ∀ l ∈ w, l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) :
    ∀ a ∈ toLetters j w, a.2 = true := by
  induction w with
  | nil => simp [toLetters]
  | cons z w ih =>
    intro a ha
    rw [toLetters] at ha
    rw [List.mem_filterMap] at ha
    obtain ⟨m, hm, hfm⟩ := ha
    simp only [List.mem_cons] at hm
    rcases hm with hmz | hm
    · rw [hmz] at hfm
      by_cases hz : z ≠ 0 ∧ z.natAbs ≤ j
      · simp only [dif_pos hz] at hfm
        simp only [Option.some.injEq] at hfm
        rw [← hfm]
        rcases h z (by simp) with rfl | rfl | rfl | rfl <;> simp
      · simp only [dif_neg hz] at hfm
        simp at hfm
    · have hm' : a ∈ toLetters j w := by
        rw [toLetters]
        exact List.mem_filterMap.mpr ⟨m, hm, hfm⟩
      exact ih (fun m hm => h m (by simp [hm])) a hm'

theorem step_spec (hcheck : BridgeCheck) (hData : DataOK (PermutationNative.inputs ()))
    (i : Fin 256) (k : Fin 4) :
    alpha hcheck (step (PermutationNative.inputs ()).tr i k) =
      alpha hcheck i * alpha hcheck (selectedLiftIndex k) := by
  obtain ⟨-, -, -, -, -, htr, -⟩ := hData
  have hlt : ((PermutationNative.inputs ()).tr[i.val]!)[k.val]! < 256 := (htr i).2 k
  have hstep : step (PermutationNative.inputs ()).tr i k =
      ⟨((PermutationNative.inputs ()).tr[i.val]!)[k.val]!, hlt⟩ := by
    unfold step
    rw [dif_pos hlt]
  obtain ⟨q, hq, hqalpha⟩ :=
    (original_actions_spec hcheck).2.2.2.2.1 i k
  have hqeq : (⟨((PermutationNative.inputs ()).tr[i.val]!)[k.val]!, hlt⟩ : Fin 256) = q := by
    apply Fin.ext
    exact hq.symm
  rw [hstep, hqeq]
  exact hqalpha

theorem walk_spec (hcheck : BridgeCheck) (hData : DataOK (PermutationNative.inputs ()))
    (i : Fin 256) (w : List (SchreierLetter 4))
    (hpos : ∀ a ∈ w, a.2 = true) :
    alpha hcheck (walk (PermutationNative.inputs ()).tr i w) =
      alpha hcheck i *
        FreeGroup.lift (fun k : Fin 4 => alpha hcheck (selectedLiftIndex k))
          (FreeGroup.mk w) := by
  induction w generalizing i with
  | nil => simp [walk]
  | cons a w ih =>
    obtain ⟨k, sign⟩ := a
    cases sign
    · have hfalse : false = true := hpos (k, false) (by simp)
      simp at hfalse
    · simp only [walk]
      rw [ih (step (PermutationNative.inputs ()).tr i k)
        (fun b hb => hpos b (by simp [hb]))]
      rw [step_spec hcheck hData i k]
      simp only [FreeGroup.lift_mk, List.map_cons, List.prod_cons, cond_true]
      rw [mul_assoc]

theorem mulIndex_spec (hcheck : BridgeCheck) (hData : DataOK (PermutationNative.inputs ()))
    (i j : Fin 256) :
    alpha hcheck (mulIndex (PermutationNative.inputs ()).tr
        (PermutationNative.inputs ()).parent i j) =
      alpha hcheck i * alpha hcheck j := by
  have hData' := hData
  obtain ⟨-, -, -, hpar, -, -, hpos⟩ := hData
  have hj : j.val < (PermutationNative.inputs ()).parent.size := by
    rw [hpar]
    exact j.isLt
  have hparent : ∀ l ∈ (PermutationNative.inputs ()).parent[j.val]!,
      l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 :=
    positiveWordsOK_spec hpos j.val hj
  rw [mulIndex, walk_spec hcheck hData' i _ (toLetters_positive hparent)]
  rw [(original_actions_spec hcheck).2.1 j]

theorem powIndex_spec (hcheck : BridgeCheck) (hData : DataOK (PermutationNative.inputs ()))
    (i : Fin 256) (n : ℕ) :
    alpha hcheck (powIndex (PermutationNative.inputs ()).tr
        (PermutationNative.inputs ()).parent i n) =
      (alpha hcheck i) ^ n := by
  induction n with
  | zero => simp [powIndex, (original_actions_spec hcheck).2.2.2.1]
  | succ n ih =>
    change alpha hcheck (mulIndex (PermutationNative.inputs ()).tr
        (PermutationNative.inputs ()).parent
        (powIndex (PermutationNative.inputs ()).tr
          (PermutationNative.inputs ()).parent i n) i) = (alpha hcheck i) ^ (n + 1)
    rw [mulIndex_spec hcheck hData, ih, pow_succ]


private abbrev G4 : Type := Multiplicative (ZMod 4)

private def e0 : G4 := Multiplicative.ofAdd (1 : ZMod 4)

private theorem orderOf_e0 : orderOf e0 = 4 := by
  rw [e0, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

private theorem orderOf_e0_pair : orderOf (e0, (1 : G4)) = 4 := by
  rw [Prod.orderOf, orderOf_e0, orderOf_one]
  norm_num

private theorem orderOf_pair_one_e0 : orderOf ((1 : G4), e0) = 4 := by
  rw [Prod.orderOf, orderOf_e0, orderOf_one]
  norm_num

private theorem e0_pow (n : ℕ) : e0 ^ n = Multiplicative.ofAdd (n : ZMod 4) := by
  rw [e0, ← ofAdd_nsmul]
  congr 1
  simpa using nsmul_eq_mul n (1 : ZMod 4)

private theorem zmod4_basis {B : Type*} [Group B] (e : B ≃* (G4 × G4))
    (u v : B) (hu : u = e.symm (e0, 1)) (hv : v = e.symm (1, e0)) :
    orderOf u = 4 ∧ orderOf v = 4 ∧ Commute u v ∧
      Function.Injective (fun p : Fin 4 × Fin 4 => u ^ p.1.val * v ^ p.2.val) := by
  have hu4 : orderOf u = 4 := by
    have h := orderOf_injective (e : B →* (G4 × G4)) e.injective u
    have hx : (e : B →* (G4 × G4)) u = (e0, (1 : G4)) := by
      rw [hu]
      exact MulEquiv.apply_symm_apply e (e0, (1 : G4))
    rw [hx] at h
    exact h.symm.trans orderOf_e0_pair
  have hv4 : orderOf v = 4 := by
    have h := orderOf_injective (e : B →* (G4 × G4)) e.injective v
    have hx : (e : B →* (G4 × G4)) v = ((1 : G4), e0) := by
      rw [hv]
      exact MulEquiv.apply_symm_apply e ((1 : G4), e0)
    rw [hx] at h
    exact h.symm.trans orderOf_pair_one_e0
  have huv : Commute u v := by
    apply e.injective
    rw [map_mul, map_mul, hu, hv]
    simp only [MulEquiv.apply_symm_apply, Prod.mk_mul_mk, one_mul, mul_one]
  refine ⟨hu4, hv4, huv, ?_⟩
  intro p q hpq
  have hmap : ∀ r s : Fin 4,
      e (u ^ r.val * v ^ s.val) =
        (Multiplicative.ofAdd (r.val : ZMod 4),
          Multiplicative.ofAdd (s.val : ZMod 4)) := by
    intro r s
    rw [map_mul, map_pow, map_pow, hu, hv]
    simp only [MulEquiv.apply_symm_apply, Prod.pow_mk, Prod.mk_mul_mk,
      one_mul, mul_one, one_pow, e0_pow]
  have heq := congrArg e hpq
  rw [hmap p.1 p.2, hmap q.1 q.2] at heq
  simp only [Prod.mk.injEq] at heq
  have hp1 : p.1 = q.1 := by
    apply Fin.ext
    have h1 : (p.1.val : ZMod 4) = (q.1.val : ZMod 4) :=
      Multiplicative.ofAdd.injective heq.1
    have := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt p.1.isLt,
      ZMod.val_natCast_of_lt q.1.isLt] at this
  have hp2 : p.2 = q.2 := by
    apply Fin.ext
    have h1 : (p.2.val : ZMod 4) = (q.2.val : ZMod 4) :=
      Multiplicative.ofAdd.injective heq.2
    have := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt p.2.isLt,
      ZMod.val_natCast_of_lt q.2.isLt] at this
  exact Prod.ext hp1 hp2



theorem bridge_inverse_checks (hcheck : BridgeCheck) :
    allLt 2 (fun i => isInvA 2688 (PermutationNative.inputs ()).ks[i]!
        ((PermutationNative.inputs ()).ks.map (invCand 2688))[i]!) = true ∧
      allLt 9 (fun i => isInvA 2688 (PermutationNative.inputs ()).p0[i]!
        ((PermutationNative.inputs ()).p0.map (invCand 2688))[i]!) = true ∧
      allLt 256 (fun i => isInvA 2688 (PermutationNative.inputs ()).lifts[i]!
        ((PermutationNative.inputs ()).lifts.map (invCand 2688))[i]!) = true := by
  have h := hcheck
  unfold BridgeCheck at h
  simp only [PermutationNative.bridgeCheck] at h
  split_ifs at h with hs
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hks, hp0, hlifts, -⟩ := h
  exact ⟨hks, hp0, hlifts⟩

theorem mem_pairProducts_iff {tr : Array (Array Nat)} {parent : Array (List Int)}
    {i j x : Fin 256} :
    x ∈ pairProducts tr parent i j ↔
      ∃ p : Fin 4 × Fin 4,
        x = mulIndex tr parent (powIndex tr parent i p.1.val)
          (powIndex tr parent j p.2.val) := by
  unfold pairProducts
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨(finProdFinEquiv (m := 4) (n := 4)).symm q, hq.symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨finProdFinEquiv (m := 4) (n := 4) p, by simp⟩

theorem alpha_mem_of_mem_pairProducts (hcheck : BridgeCheck)
    (hData : DataOK (PermutationNative.inputs ()))
    (B : Subgroup (MulAut Khat)) (u v : B) (i j : Fin 256)
    (hi : alpha hcheck i = (u : MulAut Khat))
    (hj : alpha hcheck j = (v : MulAut Khat))
    {x : Fin 256} (hx : x ∈ pairProducts (PermutationNative.inputs ()).tr
      (PermutationNative.inputs ()).parent i j) :
    alpha hcheck x ∈ B := by
  rw [mem_pairProducts_iff] at hx
  obtain ⟨p, hp⟩ := hx
  rw [hp]
  rw [mulIndex_spec hcheck hData, powIndex_spec hcheck hData,
    powIndex_spec hcheck hData, hi, hj]
  exact B.mul_mem (B.pow_mem u.2 p.1.val) (B.pow_mem v.2 p.2.val)

theorem exists_central_involution_mem_commutator_closure
    (hcheck : BridgeCheck)
    (B : Subgroup (MulAut Khat))
    (hBT : B ≤ T hcheck)
    (hB : Nonempty
      (B ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) :
    ∃ (s : B) (w : Khat),
      orderOf s = 2 ∧ orderOf w = 2 ∧
      w ∈ Subgroup.center Khat ∧
      w ∈ Subgroup.closure
        {d : Khat |
          ∃ (c : Khat) (a : B),
            c ∈ P0 hcheck ∧
            (s : MulAut Khat) c = c ∧
            d = c⁻¹ * (a : MulAut Khat) c} := by
  have hC := commutatorCheck_spec (Certificates.certificate1212004)
  have hData : DataOK (PermutationNative.inputs ()) := hC.1
  have hWit : ∀ a : Fin 3,
      WitnessOK (PermutationNative.inputs ())
        (liftInvArrays (PermutationNative.inputs ()))
        ((actorSets ())[a.val]!) ((witnesses ())[a.val]!) := hC.2.2.2.1
  have hCover : PairActorOK (PermutationNative.inputs ()).tr
      (PermutationNative.inputs ()).parent (actorSets ()) := hC.2.2.2.2
  obtain ⟨e⟩ := hB
  let u : B := e.symm (e0, (1 : G4))
  let v : B := e.symm ((1 : G4), e0)
  obtain ⟨hu4, hv4, huv, hcoord⟩ := zmod4_basis e u v rfl rfl
  obtain ⟨halpha, hparent, hmemT, hzero, htrans, hsep, hinj, hcov, hcardT⟩ :=
    original_actions_spec hcheck
  have huT : (u : MulAut Khat) ∈ T hcheck := hBT u.2
  obtain ⟨i, hi⟩ := (hcov (u : MulAut Khat)).1 huT
  have hvT : (v : MulAut Khat) ∈ T hcheck := hBT v.2
  obtain ⟨j, hj⟩ := (hcov (v : MulAut Khat)).1 hvT
  have hu_pow4 : u ^ 4 = 1 := by
    rw [← hu4]
    exact pow_orderOf_eq_one u
  have hv_pow4 : v ^ 4 = 1 := by
    rw [← hv4]
    exact pow_orderOf_eq_one v
  have hu_pow2 : u ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hu4] at hdvd
    norm_num at hdvd
  have hv_pow2 : v ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf v ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hv4] at hdvd
    norm_num at hdvd
  have hvalid : Valid (PermutationNative.inputs ()).tr
      (PermutationNative.inputs ()).parent i j := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply hinj
      rw [mulIndex_spec hcheck hData, mulIndex_spec hcheck hData, hi, hj]
      exact congrArg Subtype.val huv.eq
    · apply hinj
      rw [powIndex_spec hcheck hData, hzero, hi]
      exact congrArg Subtype.val hu_pow4
    · intro h
      have hh := congrArg (alpha hcheck) h
      rw [powIndex_spec hcheck hData, hzero, hi] at hh
      apply hu_pow2
      apply Subtype.ext
      simpa using hh
    · apply hinj
      rw [powIndex_spec hcheck hData, hzero, hj]
      exact congrArg Subtype.val hv_pow4
    · intro h
      have hh := congrArg (alpha hcheck) h
      rw [powIndex_spec hcheck hData, hzero, hj] at hh
      apply hv_pow2
      apply Subtype.ext
      simpa using hh
    · rw [pairProducts, List.nodup_ofFn]
      intro q q' hqq'
      have hp : (finProdFinEquiv (m := 4) (n := 4)).symm q =
          (finProdFinEquiv (m := 4) (n := 4)).symm q' := by
        apply hcoord
        have hh := congrArg (alpha hcheck) hqq'
        rw [mulIndex_spec hcheck hData, mulIndex_spec hcheck hData] at hh
        simp only [powIndex_spec hcheck hData, hi, hj] at hh
        exact Subtype.ext hh
      exact (finProdFinEquiv (m := 4) (n := 4)).symm.injective hp
  have ks_rows (k : Fin 2) :
      Rep 2688 (PermutationNative.inputs ()).ks[k.val]! (ksPerm k) ∧
      Rep 2688 ((PermutationNative.inputs ()).ks.map (invCand 2688))[k.val]!
        (ksPerm k)⁻¹ := by
    exact rep_permOfArr (allLt_spec (bridge_inverse_checks hcheck).1 k.isLt)

  have p0_rows (k : Fin 9) :
      Rep 2688 (PermutationNative.inputs ()).p0[k.val]! (p0Perm k) ∧
      Rep 2688 (p0InvArrays (PermutationNative.inputs ()))[k.val]! (p0Perm k)⁻¹ := by
    exact rep_permOfArr (allLt_spec (bridge_inverse_checks hcheck).2.1 k.isLt)

  have lift_rows (i : Fin 256) :
      Rep 2688 (PermutationNative.inputs ()).lifts[i.val]! (liftPerm i) ∧
      Rep 2688 ((PermutationNative.inputs ()).lifts.map (invCand 2688))[i.val]!
        (liftPerm i)⁻¹ := by
    exact rep_permOfArr (allLt_spec (bridge_inverse_checks hcheck).2.2 i.isLt)

  have p0_word_coe (w : List ℤ) :
      ((Quiver.SchreierGraph.evalWord (p0In hcheck) (toLetters 9 w) : Khat) :
        Equiv.Perm (Fin 2688)) =
        Quiver.SchreierGraph.evalWord p0Perm (toLetters 9 w) := by
    exact FreeGroup.lift_unique (f := p0Perm)
      (Khat.subtype.comp (FreeGroup.lift (p0In hcheck))) (fun k => rfl)
      (x := FreeGroup.mk (toLetters 9 w))

  have p0_word_rep (w : List ℤ)
      (hw : lettersOK 9 w = true) :
      Rep 2688 (evalP0Word (PermutationNative.inputs ())
        (p0InvArrays (PermutationNative.inputs ())) w)
        ((Quiver.SchreierGraph.evalWord (p0In hcheck) (toLetters 9 w) : Khat) :
          Equiv.Perm (Fin 2688)) := by
    let gs : ℕ → Equiv.Perm (Fin 2688) := fun k =>
      if hk : k < 9 then p0Perm ⟨k, hk⟩ else 1
    have hS : ∀ k < 9, Rep 2688 (PermutationNative.inputs ()).p0[k]! (gs k) := by
      intro k hk
      simpa only [gs, dif_pos hk] using (p0_rows ⟨k, hk⟩).1
    have hI : ∀ k < 9, Rep 2688
        (p0InvArrays (PermutationNative.inputs ()))[k]! (gs k)⁻¹ := by
      intro k hk
      simpa only [gs, dif_pos hk] using (p0_rows ⟨k, hk⟩).2
    have h := rep_wordA (n := 2688) (S := (PermutationNative.inputs ()).p0)
      (Sinv := p0InvArrays (PermutationNative.inputs ())) (gs := gs) (j := 9) hS hI w hw
    have heq : (fun k : Fin 9 => gs k.val) = p0Perm := by
      funext k
      simp only [gs, dif_pos k.isLt]
    rw [heq] at h
    rw [p0_word_coe]
    exact h

  obtain ⟨a, hperm⟩ := hCover i j hvalid
  let A := (actorSets ())[a.val]!
  let W := (witnesses ())[a.val]!
  have hWa : WitnessOK inputs (liftInvArrays inputs) A W := hWit a
  dsimp only [WitnessOK] at hWa
  obtain ⟨hWs_mem, hWa_mem, hWletters, hWsq_s, hWs_ne, hWrest⟩ := hWa
  obtain ⟨hWinv_c, hWinv_t, hWfix, hWsq_w, hWne_w, hWcomm0, hWcomm1⟩ := hWrest

  have hs_mem_pair : W.sIndex ∈ pairProducts inputs.tr inputs.parent i j :=
    hperm.mem_iff.mpr hWs_mem
  have hs_mem_B : alpha hcheck W.sIndex ∈ B :=
    alpha_mem_of_mem_pairProducts hcheck hData B u v i j hi hj hs_mem_pair
  let sK : B := ⟨alpha hcheck W.sIndex, hs_mem_B⟩
  have ha_mem_pair : W.aIndex ∈ pairProducts inputs.tr inputs.parent i j :=
    hperm.mem_iff.mpr hWa_mem
  have ha_mem_B : alpha hcheck W.aIndex ∈ B :=
    alpha_mem_of_mem_pairProducts hcheck hData B u v i j hi hj ha_mem_pair
  let bK : B := ⟨alpha hcheck W.aIndex, ha_mem_B⟩

  let c : Khat := Quiver.SchreierGraph.evalWord (p0In hcheck) (toLetters 9 W.cWord)
  have hc_mem : c ∈ P0 hcheck := by
    simpa [P0] using Quiver.SchreierGraph.evalWord_mem_closure (p0In hcheck) (toLetters 9 W.cWord)
  let term : Khat := c⁻¹ * (bK : MulAut Khat) c

  have hs_sq : sK * sK = 1 := by
    apply Subtype.ext
    change alpha hcheck W.sIndex * alpha hcheck W.sIndex = 1
    have h := congrArg (alpha hcheck) hWsq_s
    rw [mulIndex_spec hcheck hData] at h
    simpa [hzero] using h
  have hs_ne : sK ≠ 1 := by
    intro h
    have hval : alpha hcheck W.sIndex = 1 := congrArg Subtype.val h
    have heq : alpha hcheck W.sIndex = alpha hcheck 0 := by rw [hval, hzero]
    exact hWs_ne (hinj heq)
  have hs_order : orderOf sK = 2 := orderOf_eq_prime hs_sq hs_ne

  let cArr := evalP0Word inputs (p0InvArrays inputs) W.cWord
  let sArr := inputs.lifts[W.sIndex.val]!
  have hRepC : Rep 2688 cArr (c : Equiv.Perm (Fin 2688)) := p0_word_rep W.cWord hWletters
  have hRepS : Rep 2688 sArr (liftPerm W.sIndex) := (lift_rows W.sIndex).1
  have hs_inv_rep : Rep 2688 (invCand 2688 sArr) (liftPerm W.sIndex)⁻¹ := by
    have h := (lift_rows W.sIndex).2
    rw [getElem!_pos (inputs.lifts.map (invCand 2688)) W.sIndex.val
          (by rw [Array.size_map, hData.2.1]; exact W.sIndex.isLt),
        Array.getElem_map] at h
    change Rep 2688 (invCand 2688 (inputs.lifts[W.sIndex.val]!))
      (liftPerm W.sIndex)⁻¹
    rw [getElem!_pos inputs.lifts W.sIndex.val
          (by rw [hData.2.1]; exact W.sIndex.isLt)]
    exact h
  have hs_fix_perm :
      (liftPerm W.sIndex) * (c : Equiv.Perm (Fin 2688)) *
        (liftPerm W.sIndex)⁻¹ = (c : Equiv.Perm (Fin 2688)) := by
    exact (eqA_iff (rep_compA (rep_compA hRepS hRepC) hs_inv_rep) hRepC).1 hWfix
  have hfixed : (sK : MulAut Khat) c = c := by
    apply Subtype.ext
    change ((alpha hcheck W.sIndex) c : Equiv.Perm (Fin 2688)) =
      (c : Equiv.Perm (Fin 2688))
    rw [halpha W.sIndex c]
    exact hs_fix_perm

  have hRepCinv : Rep 2688 (invCand 2688 cArr)
      ((c : Equiv.Perm (Fin 2688))⁻¹) :=
    rep_inv_of_isInvA hRepC hWinv_c
  have hRepA : Rep 2688 inputs.lifts[W.aIndex.val]! (liftPerm W.aIndex) :=
    (lift_rows W.aIndex).1
  have hRepAinv : Rep 2688 (liftInvArrays inputs)[W.aIndex.val]!
      ((liftPerm W.aIndex)⁻¹) := (lift_rows W.aIndex).2
  have hRepAlpha : Rep 2688
      (alphaArray inputs (liftInvArrays inputs) W.aIndex cArr)
      (((bK : MulAut Khat) c : Equiv.Perm (Fin 2688))) := by
    have h := rep_compA (rep_compA hRepA hRepC) hRepAinv
    simpa only [alphaArray, bK, halpha W.aIndex c] using h
  have hRepT : Rep 2688
      (termArray inputs (liftInvArrays inputs) W.aIndex cArr)
      ((term : Equiv.Perm (Fin 2688))) := by
    have h := rep_compA hRepCinv hRepAlpha
    simpa only [termArray, term, Subgroup.coe_mul, Subgroup.coe_inv] using h

  let w : Khat := if W.sign then term else term⁻¹
  have hRepW : Rep 2688 (witnessW inputs (liftInvArrays inputs) W)
      ((w : Equiv.Perm (Fin 2688))) := by
    by_cases hsign : W.sign
    · simp only [w, hsign, if_true, witnessW, if_true]
      exact hRepT
    · simp only [w, hsign, if_false, witnessW, if_false]
      exact rep_inv_of_isInvA hRepT hWinv_t

  have hw_sq : w * w = 1 := by
    apply Subtype.ext
    change (w : Equiv.Perm (Fin 2688)) * (w : Equiv.Perm (Fin 2688)) = 1
    have h := (eqA_iff (rep_compA hRepW hRepW) rep_idA).1 hWsq_w
    simpa using h
  have hw_ne : w ≠ 1 := by
    intro h
    have hval : (w : Equiv.Perm (Fin 2688)) = 1 := congrArg Subtype.val h
    have heq : eqA 2688 (witnessW inputs (liftInvArrays inputs) W) (idA 2688) = true := by
      rw [eqA_iff hRepW rep_idA]
      exact hval
    rw [hWne_w] at heq
    cases heq
  have hw_order : orderOf w = 2 := orderOf_eq_prime hw_sq hw_ne

  have hcomm_ks (j : Fin 2) : w * ksIn j = ksIn j * w := by
    apply Subtype.ext
    change (w : Equiv.Perm (Fin 2688)) * ksPerm j =
      ksPerm j * (w : Equiv.Perm (Fin 2688))
    have hRepKs : Rep 2688 inputs.ks[j.val]! (ksPerm j) := (ks_rows j).1
    have h := (eqA_iff (rep_compA hRepW hRepKs) (rep_compA hRepKs hRepW)).1 ?_
    · exact h
    · fin_cases j
      · exact hWcomm0
      · exact hWcomm1
  have hKhat_le_centralizer :
      Khat ≤ Subgroup.centralizer
        ({(w : Equiv.Perm (Fin 2688))} : Set (Equiv.Perm (Fin 2688))) := by
    apply (Subgroup.closure_le (Subgroup.centralizer
      ({(w : Equiv.Perm (Fin 2688))} : Set (Equiv.Perm (Fin 2688))))).mpr
    rintro x ⟨j, rfl⟩
    change ksPerm j ∈ Subgroup.centralizer
      ({(w : Equiv.Perm (Fin 2688))} : Set (Equiv.Perm (Fin 2688)))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_singleton_iff] at hh
    subst h
    exact congrArg Subtype.val (hcomm_ks j)
  have hw_center : w ∈ Subgroup.center Khat := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hmem : (g : Equiv.Perm (Fin 2688)) ∈ Subgroup.centralizer
        ({(w : Equiv.Perm (Fin 2688))} : Set (Equiv.Perm (Fin 2688))) :=
      hKhat_le_centralizer g.2
    have h := (Subgroup.mem_centralizer_iff).1 hmem
      (w : Equiv.Perm (Fin 2688)) (by simp)
    exact Subtype.ext h.symm

  let S : Set Khat := {d : Khat |
    ∃ (c : Khat) (a : B),
      c ∈ P0 hcheck ∧ (sK : MulAut Khat) c = c ∧
      d = c⁻¹ * (a : MulAut Khat) c}
  have hterm_mem : term ∈ Subgroup.closure S := by
    apply Subgroup.subset_closure
    exact ⟨c, bK, hc_mem, hfixed, rfl⟩
  have hw_closure : w ∈ Subgroup.closure S := by
    by_cases hsign : W.sign
    · simp only [w, hsign, if_true]
      exact hterm_mem
    · simp only [w, hsign, if_false]
      exact Subgroup.inv_mem _ hterm_mem

  exact ⟨sK, w, hs_order, hw_order, hw_center, hw_closure⟩

end CFSG.GH74.GLS.NT44.PermutationCommutator
