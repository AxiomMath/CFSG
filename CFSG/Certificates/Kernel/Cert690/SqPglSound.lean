module

public import CFSG.Certificates.Kernel.Cert690.SqA8Sound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62 CFSG.KC.Enum

structure PglHyp (K K0 : List ℕ) (P P0 : List (ℕ × ℕ)) (T W1 W2 : IT) (M1 M2 : ℕ) : Prop where
  enum : enumData kPGLGens = (K.toArray, P.toArray)
  enum0 : enumData kPGL0Gens = (K0.toArray, P0.toArray)
  invOK : pglInvolutionsOK (pglData ()) = true
  nd : K.Nodup
  ix : ∀ c, T.find c K.length = K.idxOf c
  iso : ∀ x ∈ K, isoQ false x = true
  inv : invOKL K.length K = true
  pass1 : passGo T W1 K.length M1 2166376464 K (invsL K) = true
  pass2 : passGo T W2 K.length M2 1108378656 K (invsL K) = true
  bits : invBitsL (Nat.lor M1 M2) K 0 = true
  top : (Nat.lor M1 M2).testBit K.length = false
  memR : (K.contains 2166376464 && K.contains 1108378656 && K0.contains 2166376464 &&
    !K0.contains 1108378656) = true
  inv1 : isInvCode 2166376464 = true
  inv2 : isInvCode 1108378656 = true
  root1 : (innTab (2 * innW (compTab (liftTab 2166376464 0) (liftTab 2166376464 0))) ==
    compTab (liftTab 2166376464 0) (liftTab 2166376464 0)) = true
  root2 : (innTab (2 * innW (compTab (liftTab 1108378656 0) (liftTab 1108378656 0))) ==
    compTab (liftTab 1108378656 0) (liftTab 1108378656 0)) = true

theorem sq_pgl : (pglSquareData ()).pgl = pglData () := by simp only [pglSquareData]

theorem sq_reps : (pglSquareData ()).reps = #[2166376464, 1108378656] := by
  simp only [pglSquareData, pglReps]

theorem sq_classMap : (pglSquareData ()).classMap =
    classMapOfReps (pglData ()).elems (pglData ()).invs #[2166376464, 1108378656] := by
  simp only [pglSquareData, pglReps]

theorem sq_theta : (pglSquareData ()).theta =
    #[liftTab 2166376464 0, liftTab 1108378656 0] := by
  simp [pglSquareData, pglReps, repThetas]

theorem sq_wits : (pglSquareData ()).wits =
    sqWitData (classMapOfReps (pglData ()).elems (pglData ()).invs #[2166376464, 1108378656])
      #[liftTab 2166376464 0, liftTab 1108378656 0] (pglData ()).involutions := by
  simp [pglSquareData, pglReps, repThetas]

theorem sq_qmulFlat : (pglSquareData ()).qmulFlat = qmulFlat () := by simp only [pglSquareData]

theorem sq_innTabs : (pglSquareData ()).innTabs = innTabs () := by simp only [pglSquareData]

namespace PglHyp

variable {K K0 : List ℕ} {P P0 : List (ℕ × ℕ)} {T W1 W2 : IT} {M1 M2 : ℕ}
  (h : PglHyp K K0 P P0 T W1 W2 M1 M2)
include h

theorem getE {i : ℕ} (hi : i < K.length) : K.toArray[i]! = K[i] := by
  rw [List.getElem!_toArray, getElem!_pos K i hi]

theorem getI {i : ℕ} (hi : i < K.length) :
    (invsL K).toArray[i]! = invGo K[i] K.length K[i] := by
  have hi' : i < (invsL K).length := by simpa [invsL] using hi
  rw [List.getElem!_toArray, getElem!_pos (invsL K) i hi']
  simp [invsL]

theorem mulInv {x : ℕ} (hx : x ∈ K) : Code.mul x (invGo x K.length x) = Code.one := by
  rw [mul_eq_mulF, one_eq_oneF]
  exact invOKL_spec _ _ h.inv x hx

theorem bit {i : ℕ} (hi : i < K.length) :
    isInvF K[i] = (M1.testBit i || M2.testBit i) := by
  have e := invBitsL_spec _ K 0 h.bits i hi
  rw [Nat.zero_add] at e
  rw [e, ← Nat.testBit_or]
  rfl

theorem topBits : M1.testBit K.length = false ∧ M2.testBit K.length = false := by
  have e := h.top
  have e' : (M1 ||| M2).testBit K.length = false := e
  rw [Nat.testBit_or, Bool.or_eq_false_iff] at e'
  exact e'

theorem fc1 (i y : ℕ) : firstConj K.toArray (invsL K).toArray i 2166376464 y =
    if M1.testBit (T.find y K.length) then some (i, K[W1.find (T.find y K.length) K.length]!)
    else none := firstConj_of_passGo h.nd h.ix h.pass1 i y

theorem fc2 (i y : ℕ) : firstConj K.toArray (invsL K).toArray i 1108378656 y =
    if M2.testBit (T.find y K.length) then some (i, K[W2.find (T.find y K.length) K.length]!)
    else none := firstConj_of_passGo h.nd h.ix h.pass2 i y

theorem cm_contains (y : ℕ) :
    (classMapOfReps K.toArray (invsL K).toArray #[2166376464, 1108378656]).contains y =
      (M1.testBit (T.find y K.length) || M2.testBit (T.find y K.length)) := by
  rw [contains_eq_isSome_get?, classMapOfReps_two_get?, h.fc1, h.fc2]
  split <;> split <;> simp_all

omit h in
theorem mem_involL {y : ℕ} : y ∈ involL K ↔ y ∈ K ∧ isInvF y = true := by
  unfold involL
  rw [List.mem_filter]

theorem cm_contains_iff (y : ℕ) :
    (classMapOfReps K.toArray (invsL K).toArray #[2166376464, 1108378656]).contains y = true ↔
      y ∈ involL K := by
  rw [h.cm_contains, h.ix, mem_involL]
  by_cases hy : y ∈ K
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    rw [h.nd.idxOf_getElem i hi, ← h.bit hi]
    exact ⟨fun e => ⟨List.getElem_mem hi, e⟩, fun e => e.2⟩
  · rw [List.idxOf_eq_length hy, h.topBits.1, h.topBits.2]
    simp [hy]

theorem cm_size :
    (classMapOfReps K.toArray (invsL K).toArray #[2166376464, 1108378656]).size =
      (involL K).length := by
  have hnd : (involL K).Nodup := h.nd.filter _
  have hp : (classMapOfReps K.toArray (invsL K).toArray
      #[2166376464, 1108378656]).keys.Perm (involL K) := by
    rw [List.perm_ext_iff_of_nodup Std.HashMap.nodup_keys hnd]
    intro y
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, h.cm_contains_iff]
  rw [← Std.HashMap.length_keys, hp.length_eq]

theorem cm_get {g : ℕ} (hg : g ∈ involL K) : ∃ i k,
    (classMapOfReps K.toArray (invsL K).toArray #[2166376464, 1108378656]).get? g =
      some (i, k) ∧ i < 2 ∧
      ∃ j, ∃ hj : j < K.length, k = K[j] ∧
        Code.mul (Code.mul K[j] ((#[2166376464, 1108378656] : Array ℕ)[i]!))
          (invGo K[j] K.length K[j]) = g := by
  have hc := (h.cm_contains_iff g).2 hg
  rw [contains_eq_isSome_get?] at hc
  obtain ⟨⟨i, k⟩, hik⟩ := Option.isSome_iff_exists.1 hc
  refine ⟨i, k, hik, ?_⟩
  rw [classMapOfReps_two_get?] at hik
  cases h0 : firstConj K.toArray (invsL K).toArray 0 2166376464 g with
  | some p =>
    rw [h0, Option.some_or] at hik
    rw [hik] at h0
    obtain ⟨rfl, j, hj, hk, hcj⟩ := firstConj_some h0
    rw [List.size_toArray] at hj
    rw [h.getE hj] at hk
    rw [h.getE hj, h.getI hj] at hcj
    exact ⟨by norm_num, j, hj, hk, hcj⟩
  | none =>
    rw [h0, Option.none_or] at hik
    obtain ⟨rfl, j, hj, hk, hcj⟩ := firstConj_some hik
    rw [List.size_toArray] at hj
    rw [h.getE hj] at hk
    rw [h.getE hj, h.getI hj] at hcj
    exact ⟨by norm_num, j, hj, hk, hcj⟩

theorem invMap_getD {j : ℕ} (hj : j < K.length) :
    (pglData ()).invMap.getD K[j] 0 = invGo K[j] K.length K[j] := by
  rw [pgl_invMap h.enum h.enum0 h.nd, lookD, lookup_zip_getElem h.nd (by simp [invsL]) hj]
  simp [invsL]

theorem elems : (pglData ()).elems = K.toArray := pgl_elems h.enum h.enum0

theorem invs : (pglData ()).invs = (invsL K).toArray := pgl_invs h.enum h.enum0

theorem involutions : (pglData ()).involutions = (involL K).toArray :=
  pgl_involutions h.enum h.enum0

theorem witOK_ok : witOK (pglData ()).elems (pglData ()).invMap #[2166376464, 1108378656]
    #[liftTab 2166376464 0, liftTab 1108378656 0] (pglData ()).involutions
    (sqWitData (classMapOfReps (pglData ()).elems (pglData ()).invs #[2166376464, 1108378656])
      #[liftTab 2166376464 0, liftTab 1108378656 0] (pglData ()).involutions) = true := by
  have hinvMap : ∀ j (hj : j < K.length),
      (pglData ()).invMap.getD K[j] 0 = invGo K[j] K.length K[j] := fun j hj => h.invMap_getD hj
  generalize (pglData ()).invMap = im at hinvMap
  rw [h.elems, h.invs, h.involutions]
  unfold witOK sqWitData
  rw [Bool.and_eq_true]
  refine ⟨by simp, ?_⟩
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range, List.size_toArray] at hj
  have hg : (involL K)[j] ∈ involL K := List.getElem_mem hj
  obtain ⟨i, k, hik, hi, jj, hjj, hk, hc⟩ := h.cm_get hg
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, List.getElem_toArray, hik]
  have hinv : im.getD k 0 = invGo K[jj] K.length K[jj] := by
    rw [hk]
    exact hinvMap jj hjj
  have hs : i < (#[liftTab 2166376464 0, liftTab 1108378656 0] : Array (Array ℕ)).size := by
    simpa using hi
  have hkE : K.toArray.contains k = true := by
    rw [List.contains_toArray, List.contains_iff_mem, hk]
    exact List.getElem_mem hjj
  have hi' : i < (#[2166376464, 1108378656] : Array ℕ).size := by simpa using hi
  dsimp only
  rw [if_pos hs]
  dsimp only
  simp only [hinv, hkE, decide_eq_true hs, decide_eq_true hi', beq_self_eq_true, Bool.true_and,
    Bool.and_true]
  rw [hk]
  simpa [h.mulInv (List.getElem_mem hjj), List.getElem!_toArray, getElem!_pos (involL K) j hj]
    using hc

theorem wits_isSome : (sqWitData (classMapOfReps K.toArray (invsL K).toArray
    #[2166376464, 1108378656]) #[liftTab 2166376464 0, liftTab 1108378656 0]
    (involL K).toArray).all (fun o => o.isSome) = true := by
  unfold sqWitData
  rw [List.map_toArray, List.all_toArray, List.all_eq_true]
  intro o ho
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ho
  obtain ⟨i, k, hik, hi, _⟩ := h.cm_get hg
  have hs : i < (#[liftTab 2166376464 0, liftTab 1108378656 0] : Array (Array ℕ)).size := by
    simpa using hi
  rw [hik]
  dsimp only
  rw [if_pos hs]
  rfl

theorem memR' : 2166376464 ∈ K ∧ 1108378656 ∈ K ∧ K0.contains 2166376464 = true ∧
    K0.contains 1108378656 = false := by
  have e := h.memR
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at e
  exact ⟨e.1.1.1, e.1.1.2, by simpa using e.1.2, by simpa using e.2⟩

theorem s1 : pglS1Of (pglSquareData ()) = true := by
  unfold pglS1Of
  rw [sq_pgl, sq_reps, sq_classMap, sq_theta, sq_wits]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨h.invOK, rfl, ?_, ?_, ?_, ?_, ?_, ?_, h.witOK_ok⟩
  · rw [h.elems]
    simp [h.inv1, h.inv2, h.memR'.1, h.memR'.2.1]
  · rw [pgl_elems0 h.enum h.enum0]
    simpa using h.memR'.2.2.1
  · rw [pgl_elems0 h.enum h.enum0]
    simpa using h.memR'.2.2.2
  · rw [h.involutions, h.elems, h.invs, List.all_toArray, List.all_eq_true]
    intro g hg
    exact (h.cm_contains_iff g).2 hg
  · rw [h.involutions, h.elems, h.invs, h.cm_size]
    simp
  · rw [h.involutions, h.elems, h.invs]
    exact h.wits_isSome

theorem s2 : pglS2Of (pglSquareData ()) = true := by
  unfold pglS2Of
  rw [sq_theta, sq_qmulFlat, sq_innTabs, rootsOK_of h.root1 h.root2, Bool.and_true]
  simp [isHomTab_liftTab (h.iso _ h.memR'.1), isHomTab_liftTab (h.iso _ h.memR'.2.1)]

theorem s3 : pglS3Of (pglSquareData ()) = true := by
  unfold pglS3Of
  rw [sq_pgl, sq_reps, sq_theta, sq_wits, sq_qmulFlat]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨h.invOK, h.witOK_ok, ?_, ?_⟩
  · rw [h.involutions, Array.all_eq_true']
    intro g hg
    rw [List.all_eq_true]
    intro f _
    apply isHomTab_liftTab
    rw [List.mem_toArray] at hg
    exact h.iso g (mem_involL.1 hg).1
  · rw [h.involutions, h.elems, h.invs]
    unfold sqWitData
    rw [List.map_toArray, List.all_toArray, List.all_eq_true]
    intro o ho
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ho
    obtain ⟨i, k, hik, hi, jj, hjj, hk, _⟩ := h.cm_get hg
    have hs : i < (#[liftTab 2166376464 0, liftTab 1108378656 0] : Array (Array ℕ)).size := by
      simpa using hi
    rw [hik]
    dsimp only
    rw [if_pos hs]
    dsimp only
    exact isHomTab_liftTab (h.iso k (hk ▸ List.getElem_mem hjj)) 0

end PglHyp

end CFSG.KC.C690

end
