module

public import Certificates.Data.Kernel.Cert690.SqA8
public import CFSG.Certificates.Kernel.Cert690.SqPassSound
public import CFSG.Certificates.Kernel.Cert690.PglSound
public import CFSG.Certificates.Kernel.Cert690.EnumSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62 CFSG.KC.Enum

theorem eqK_eq (a b : Bool) : eqK a b = (a == b) := by cases a <;> cases b <;> rfl

theorem invOKL_spec (n : ℕ) : ∀ (E : List ℕ), invOKL n E = true →
    ∀ x ∈ E, mulF x (invGo x n x) = oneF
  | [], _ => by simp
  | x :: E, h => by
    have h' : andK (Nat.beq (mulF x (invGo x n x)) oneF) (invOKL n E) = true := h
    rw [andK_eq, Bool.and_eq_true, Nat.beq_eq] at h'
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h'.1
    · exact invOKL_spec n E h'.2 y hy

theorem invBitsL_spec (M : ℕ) : ∀ (E : List ℕ) (j : ℕ), invBitsL M E j = true →
    ∀ i (hi : i < E.length), isInvF E[i] = M.testBit (j + i)
  | [], _, _ => by simp
  | x :: E, j, h => by
    have h' : andK (eqK (isInvF x) (bitK M j)) (invBitsL M E (j + 1)) = true := by
      rw [← strictB_eq j (fun j => andK (eqK (isInvF x) (bitK M j)) (invBitsL M E (j + 1)))]
      exact h
    rw [andK_eq, Bool.and_eq_true, eqK_eq, beq_iff_eq, bitK_eq] at h'
    intro i hi
    cases i with
    | zero => exact h'.1
    | succ i =>
      rw [List.getElem_cons_succ, invBitsL_spec M E (j + 1) h'.2 i (by simpa using hi)]
      congr 1
      omega

theorem act_mul (a b v : ℕ) : Code.act (Code.mul a b) v = Code.act a (Code.act b v) := by
  apply eq_of_testBit_lt' (n := 6) (lt_of_lt_of_eq (Code.act_lt _ _) (by norm_num))
    (lt_of_lt_of_eq (Code.act_lt _ _) (by norm_num))
  intro k hk
  apply Code.testBit_eq_of_bitZ_eq
  have h : Code.vec (Code.act (Code.mul a b) v) = Code.vec (Code.act a (Code.act b v)) := by
    rw [Code.vec_act, Code.vec_act, Code.vec_act, Code.mat_mul, Matrix.mulVec_mulVec]
  exact congrFun h ⟨k, hk⟩

theorem isoQ_mul {a b : ℕ} (ha : isoQ false a = true) (hb : isoQ false b = true) :
    isoQ false (Code.mul a b) = true := by
  unfold isoQ at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro v hv
  have h1 := hb v hv
  have h2 := ha (Code.act b v) (List.mem_range.2 (Code.act_lt b v))
  simp only [beq_iff_eq] at h1 h2 ⊢
  rw [act_mul, h2, h1]

theorem isoQ_of_enumPar {gs E : List ℕ} {P : List (ℕ × ℕ)} (hlen : E.length ≤ 65535)
    (h0 : E[0]? = some oneF) (hone : isoQ false oneF = true)
    (hpar : enumParK (fun i => (posT E).find i 0) gs E P 0 = true)
    (hg : gs.all (isoQ false) = true) : ∀ x ∈ E, isoQ false x = true := by
  obtain ⟨hPl, hP⟩ := enumParK_spec _ gs E P 0 hpar
  rw [List.all_eq_true] at hg
  suffices key : ∀ i (hi : i < E.length), isoQ false E[i] = true by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact key i hi
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hP i hi (by omega) with h | ⟨⟨hp, hq⟩, he⟩
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h0
      rw [h0]
      exact hone
    · rw [he, find_posT hlen, List.getD_eq_getElem _ _ (by omega), mulF_eq,
        List.getD_eq_getElem _ _ hq]
      exact isoQ_mul (ih _ (by omega) (by omega)) (hg _ (List.getElem_mem hq))

set_option maxRecDepth 100000 in
theorem filter_half : ∀ w < 64, (List.range 128).filter (fun e => e / 2 == w) = [2 * w, 2 * w + 1] := by
  decide +kernel

theorem innRoots_eq (t : Array ℕ) : innRoots (innTabs ()) t =
    if innTab (2 * innW t) == t then [2 * innW t, 2 * innW t + 1] else [] := by
  unfold innRoots
  rw [innTabs_size]
  have key : ∀ e ∈ List.range 128,
      ((innTabs ())[e]! == t) = ((innTab (2 * innW t) == t) && (e / 2 == innW t)) := by
    intro e he
    have he' := List.mem_range.1 he
    rw [innTabs_getElem! he']
    have hiff : innTab e = t ↔ (innTab (2 * innW t) = t ∧ e / 2 = innW t) := by
      constructor
      · intro h
        have hw : innW t = e / 2 := by rw [← h, innW_innTab he']
        exact ⟨by rw [hw, innTab_even he', h], hw.symm⟩
      · rintro ⟨h2, hw⟩
        rw [← innTab_even he', hw, h2]
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, Bool.and_eq_true]
    exact hiff
  rw [List.filter_congr key]
  by_cases hc : innTab (2 * innW t) = t
  · rw [if_pos (by simpa using hc)]
    simp only [hc, beq_self_eq_true, Bool.true_and]
    exact filter_half _ (innW_lt t)
  · rw [if_neg (by simpa using hc)]
    simp [hc]

theorem qmulN_two_mul_z0 (w : ℕ) : qmulN (2 * w) z0N = 2 * w + 1 := by
  unfold qmulN z0N
  simp only [show 2 * w % 2 = 0 by omega, show 2 * w / 2 = w by omega, Nat.reduceMod,
    Nat.reduceDiv, b0n_zero_right, Nat.zero_xor, Nat.xor_zero, Bool.false_eq_true, if_false]
  omega

theorem roots_pair (w : ℕ) : ([2 * w, 2 * w + 1].length == 2 &&
    [2 * w, 2 * w + 1].contains ([2 * w, 2 * w + 1].head?.getD 0) &&
    [2 * w, 2 * w + 1].filter (fun e => e != [2 * w, 2 * w + 1].head?.getD 0) ==
      [qmulN ([2 * w, 2 * w + 1].head?.getD 0) z0N]) = true := by
  simp only [List.head?_cons, Option.getD_some, qmulN_two_mul_z0]
  simp

theorem rootsOK_of {θ₁ θ₂ : Array ℕ}
    (h1 : (innTab (2 * innW (compTab θ₁ θ₁)) == compTab θ₁ θ₁) = true)
    (h2 : (innTab (2 * innW (compTab θ₂ θ₂)) == compTab θ₂ θ₂) = true) :
    rootsOK (innTabs ()) #[θ₁, θ₂] = true := by
  unfold rootsOK repRoot
  rw [Array.all_eq_true']
  intro i hi
  rw [Array.mem_range] at hi
  have hi' : i < (#[θ₁, θ₂] : Array (Array ℕ)).size := hi
  have hmap : ((#[θ₁, θ₂] : Array (Array ℕ)).map
      (fun t => (innRoots (innTabs ()) (compTab t t)).head?.getD 0))[i]! =
      (innRoots (innTabs ()) (compTab (#[θ₁, θ₂][i]!) (#[θ₁, θ₂][i]!))).head?.getD 0 := by
    rw [getElem!_pos _ i (by simpa using hi'), Array.getElem_map, getElem!_pos _ i hi']
  have hθ : (innTab (2 * innW (compTab (#[θ₁, θ₂][i]!) (#[θ₁, θ₂][i]!))) ==
      compTab (#[θ₁, θ₂][i]!) (#[θ₁, θ₂][i]!)) = true := by
    have hi2 : i < 2 := by simpa using hi'
    interval_cases i
    · exact h1
    · exact h2
  rw [hmap]
  generalize #[θ₁, θ₂][i]! = θ at hθ ⊢
  dsimp only
  rw [innRoots_eq, if_pos hθ]
  exact roots_pair _

theorem find?_range_one {n : ℕ} (hn : 2 ≤ n) {p : ℕ → Bool} (h0 : p 0 = false)
    (h1 : p 1 = true) : (List.range n).find? p = some 1 := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨h1, 1, by rw [List.length_range]; omega, List.getElem_range _, fun j hj => ?_⟩
  obtain rfl : j = 0 := by omega
  rw [List.getElem_range, h0]
  rfl

theorem find?_range_two {n : ℕ} (hn : 3 ≤ n) {p : ℕ → Bool} (h0 : p 0 = false)
    (h1 : p 1 = false) (h2 : p 2 = true) : (List.range n).find? p = some 2 := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨h2, 2, by rw [List.length_range]; omega, List.getElem_range _, fun j hj => ?_⟩
  rw [List.getElem_range]
  interval_cases j
  · rw [h0]
    rfl
  · rw [h1]
    rfl

theorem firstConj_some {E invE : Array ℕ} {i r y i' k : ℕ}
    (h : firstConj E invE i r y = some (i', k)) :
    i' = i ∧ ∃ j < E.size, k = E[j]! ∧ Code.mul (Code.mul (E[j]!) r) (invE[j]!) = y := by
  unfold firstConj at h
  cases hf : (List.range E.size).find? (fun j => Code.mul (Code.mul (E[j]!) r) (invE[j]!) == y)
    with
  | none =>
    rw [hf] at h
    exact absurd h (by simp)
  | some j =>
    rw [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hm := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    have hp := List.find?_some hf
    exact ⟨rfl, j, hm, rfl, by simpa using hp⟩

theorem contains_eq_isSome_get? {β : Type} (m : Std.HashMap ℕ β) (y : ℕ) :
    m.contains y = (m.get? y).isSome := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.get?_eq_getElem?]

section

variable {L : List ℕ} {P : List (ℕ × ℕ)} (hE : enumData a8Gens = (L.toArray, P.toArray))
include hE

theorem a8_elems : (a8Data ()).elems = L.toArray := by simp only [a8Data, hE]

theorem a8_par : (a8Data ()).par = P.toArray := by simp only [a8Data, hE]

theorem a8_inverses : (a8Data ()).inverses = (invsL L).toArray := by
  simp only [a8Data, hE, invArr_eq]

theorem a8_invMap (hnd : L.Nodup) (g d : ℕ) :
    (a8Data ()).invMap.getD g d = lookD L (invsL L) g d := by
  have e : (a8Data ()).invMap = invMapOf L.toArray (invsL L).toArray := by
    simp only [a8Data, hE, invArr_eq]
  rw [e, invMapOf_getD hnd (by simp [invsL])]

theorem a8_involutions : (a8Data ()).involutions = (involL L).toArray := by
  simp only [a8Data, hE, invsOf, involL, List.filter_toArray, isInvCode_eq]

theorem a8_reps : (a8Data ()).reps = twoClassReps L.toArray (invsL L).toArray := by
  simp only [a8Data, hE, invArr_eq]

theorem a8_classMap : (a8Data ()).classMap =
    classMapOfReps L.toArray (invsL L).toArray (twoClassReps L.toArray (invsL L).toArray) := by
  simp only [a8Data, hE, invArr_eq]

theorem a8_theta : (a8Data ()).theta = repThetas (twoClassReps L.toArray (invsL L).toArray) := by
  simp only [a8Data, hE, invArr_eq]

theorem a8_wits : (a8Data ()).wits =
    sqWitData (classMapOfReps L.toArray (invsL L).toArray (twoClassReps L.toArray (invsL L).toArray))
      (repThetas (twoClassReps L.toArray (invsL L).toArray)) (involL L).toArray := by
  simp only [a8Data, hE, invArr_eq, invsOf, involL, List.filter_toArray, isInvCode_eq]

theorem a8_qmulFlat : (a8Data ()).qmulFlat = qmulFlat () := by simp only [a8Data, hE]

theorem a8_innTabs : (a8Data ()).innTabs = innTabs () := by simp only [a8Data, hE]

theorem a8_invMap' : (a8Data ()).invMap = invMapOf L.toArray (invsL L).toArray := by
  simp only [a8Data, hE, invArr_eq]

end

theorem twoClassReps_eq {E invE : Array ℕ} {r1 r2 : ℕ} (h1 : firstInvIdx E = some 1)
    (he1 : E[1]! = r1)
    (h2 : (List.range E.size).find? (fun j => isInvCode (E[j]!) &&
      !(classMapOfReps E invE #[r1]).contains (E[j]!)) = some 2)
    (he2 : E[2]! = r2) : twoClassReps E invE = #[r1, r2] := by
  unfold twoClassReps
  simp only [h1, he1]
  rw [h2]
  simp only [he2]

structure A8Hyp (L : List ℕ) (P : List (ℕ × ℕ)) (T W1 W2 : IT) (M1 M2 r1 r2 : ℕ) : Prop where
  enum : enumData a8Gens = (L.toArray, P.toArray)
  nd : L.Nodup
  ix : ∀ c, T.find c L.length = L.idxOf c
  len : L.length = 20160
  eok : enumOK a8Gens L.toArray P.toArray = true
  iso : ∀ x ∈ L, isoQ false x = true
  gens : a8Gens.all (isoQ false) = true
  isoOne : isoQ false Code.one = true
  inv : invOKL L.length L = true
  pass1 : passGo T W1 L.length M1 r1 L (invsL L) = true
  pass2 : passGo T W2 L.length M2 r2 L (invsL L) = true
  bits : invBitsL (Nat.lor M1 M2) L 0 = true
  top : (Nat.lor M1 M2).testBit L.length = false
  l0 : L[0]? = some oneF
  l1 : L[1]? = some r1
  l2 : L[2]? = some r2
  inv1 : isInvCode r1 = true
  inv2 : isInvCode r2 = true
  one : isInvCode Code.one = false
  m11 : M1.testBit 1 = true
  m12 : M1.testBit 2 = false
  root1 : (innTab (2 * innW (compTab (liftTab r1 0) (liftTab r1 0))) ==
    compTab (liftTab r1 0) (liftTab r1 0)) = true
  root2 : (innTab (2 * innW (compTab (liftTab r2 0) (liftTab r2 0))) ==
    compTab (liftTab r2 0) (liftTab r2 0)) = true

namespace A8Hyp

variable {L : List ℕ} {P : List (ℕ × ℕ)} {T W1 W2 : IT} {M1 M2 r1 r2 : ℕ}
  (h : A8Hyp L P T W1 W2 M1 M2 r1 r2)
include h

theorem getE {i : ℕ} (hi : i < L.length) : L.toArray[i]! = L[i] := by
  rw [List.getElem!_toArray, getElem!_pos L i hi]

theorem getE_of {i x : ℕ} (hx : L[i]? = some x) : L.toArray[i]! = x := by
  have hi : i < L.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hx
    exact absurd hx (by simp)
  rw [h.getE hi]
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hx
  exact hx

theorem e0 : L.toArray[0]! = Code.one := by rw [h.getE_of h.l0, oneF_eq]

theorem e1 : L.toArray[1]! = r1 := h.getE_of h.l1

theorem e2 : L.toArray[2]! = r2 := h.getE_of h.l2

theorem getI {i : ℕ} (hi : i < L.length) :
    (invsL L).toArray[i]! = invGo L[i] L.length L[i] := by
  have hi' : i < (invsL L).length := by simpa [invsL] using hi
  rw [List.getElem!_toArray, getElem!_pos (invsL L) i hi']
  simp [invsL]

theorem mulInv {x : ℕ} (hx : x ∈ L) : Code.mul x (invGo x L.length x) = Code.one := by
  rw [mul_eq_mulF, one_eq_oneF]
  exact invOKL_spec _ _ h.inv x hx

theorem bit {i : ℕ} (hi : i < L.length) :
    isInvF L[i] = (M1.testBit i || M2.testBit i) := by
  have e := invBitsL_spec _ L 0 h.bits i hi
  rw [Nat.zero_add] at e
  rw [e, ← Nat.testBit_or]
  rfl

theorem topBits : M1.testBit L.length = false ∧ M2.testBit L.length = false := by
  have e := h.top
  have e' : (M1 ||| M2).testBit L.length = false := e
  rw [Nat.testBit_or, Bool.or_eq_false_iff] at e'
  exact e'

theorem fc1 (i y : ℕ) : firstConj L.toArray (invsL L).toArray i r1 y =
    if M1.testBit (T.find y L.length) then some (i, L[W1.find (T.find y L.length) L.length]!)
    else none := firstConj_of_passGo h.nd h.ix h.pass1 i y

theorem fc2 (i y : ℕ) : firstConj L.toArray (invsL L).toArray i r2 y =
    if M2.testBit (T.find y L.length) then some (i, L[W2.find (T.find y L.length) L.length]!)
    else none := firstConj_of_passGo h.nd h.ix h.pass2 i y

theorem idx1 : T.find r1 L.length = 1 := by
  have hi : 1 < L.length := by rw [h.len]; norm_num
  rw [h.ix, ← h.e1, h.getE hi, h.nd.idxOf_getElem 1 hi]

theorem idx2 : T.find r2 L.length = 2 := by
  have hi : 2 < L.length := by rw [h.len]; norm_num
  rw [h.ix, ← h.e2, h.getE hi, h.nd.idxOf_getElem 2 hi]

theorem m1_contains (y : ℕ) : (classMapOfReps L.toArray (invsL L).toArray #[r1]).contains y =
    M1.testBit (T.find y L.length) := by
  rw [contains_eq_isSome_get?, classMapOfReps_one_get?, h.fc1]
  split <;> simp_all

theorem firstInv : firstInvIdx L.toArray = some 1 := by
  unfold firstInvIdx
  apply find?_range_one (by simp [h.len])
  · rw [h.e0]
    exact h.one
  · rw [h.e1]
    exact h.inv1

theorem findTwo : (List.range L.toArray.size).find? (fun j => isInvCode (L.toArray[j]!) &&
    !(classMapOfReps L.toArray (invsL L).toArray #[r1]).contains (L.toArray[j]!)) = some 2 := by
  apply find?_range_two (by simp [h.len])
  · rw [h.e0, h.one, Bool.false_and]
  · rw [h.e1, h.m1_contains, h.idx1, h.m11, Bool.not_true, Bool.and_false]
  · rw [h.e2, h.m1_contains, h.idx2, h.m12, h.inv2]
    rfl

theorem reps : twoClassReps L.toArray (invsL L).toArray = #[r1, r2] :=
  twoClassReps_eq h.firstInv h.e1 h.findTwo h.e2

theorem cm_contains (y : ℕ) :
    (classMapOfReps L.toArray (invsL L).toArray #[r1, r2]).contains y =
      (M1.testBit (T.find y L.length) || M2.testBit (T.find y L.length)) := by
  rw [contains_eq_isSome_get?, classMapOfReps_two_get?, h.fc1, h.fc2]
  split <;> split <;> simp_all

theorem mem_involL {y : ℕ} : y ∈ involL L ↔ y ∈ L ∧ isInvF y = true := by
  unfold involL
  rw [List.mem_filter]

theorem cm_contains_iff (y : ℕ) :
    (classMapOfReps L.toArray (invsL L).toArray #[r1, r2]).contains y = true ↔ y ∈ involL L := by
  rw [h.cm_contains, h.ix, h.mem_involL]
  by_cases hy : y ∈ L
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    rw [h.nd.idxOf_getElem i hi, ← h.bit hi]
    exact ⟨fun e => ⟨List.getElem_mem hi, e⟩, fun e => e.2⟩
  · rw [List.idxOf_eq_length hy, h.topBits.1, h.topBits.2]
    simp [hy]

theorem cm_size : (classMapOfReps L.toArray (invsL L).toArray #[r1, r2]).size =
    (involL L).length := by
  have hnd : (involL L).Nodup := h.nd.filter _
  have hp : (classMapOfReps L.toArray (invsL L).toArray #[r1, r2]).keys.Perm (involL L) := by
    rw [List.perm_ext_iff_of_nodup Std.HashMap.nodup_keys hnd]
    intro y
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, h.cm_contains_iff]
  rw [← Std.HashMap.length_keys, hp.length_eq]

theorem cm_get {g : ℕ} (hg : g ∈ involL L) : ∃ i k,
    (classMapOfReps L.toArray (invsL L).toArray #[r1, r2]).get? g = some (i, k) ∧ i < 2 ∧
      ∃ j, ∃ hj : j < L.length, k = L[j] ∧
        Code.mul (Code.mul L[j] (#[r1, r2][i]!)) (invGo L[j] L.length L[j]) = g := by
  have hc := (h.cm_contains_iff g).2 hg
  rw [contains_eq_isSome_get?] at hc
  obtain ⟨⟨i, k⟩, hik⟩ := Option.isSome_iff_exists.1 hc
  refine ⟨i, k, hik, ?_⟩
  rw [classMapOfReps_two_get?] at hik
  cases h0 : firstConj L.toArray (invsL L).toArray 0 r1 g with
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

theorem invOK : a8InvolutionsOK (a8Data ()) = true := by
  unfold a8InvolutionsOK
  rw [a8_elems h.enum, a8_involutions h.enum, Bool.and_eq_true, List.all_toArray,
    List.all_toArray, List.all_eq_true, List.all_eq_true]
  constructor
  · intro x hx
    rw [beq_iff_eq, isInvCode_eq, List.contains_toArray]
    cases hc : isInvF x
    · symm
      rw [Bool.eq_false_iff]
      intro hm
      rw [List.contains_iff_mem, h.mem_involL, hc] at hm
      exact absurd hm.2 (by simp)
    · symm
      rw [List.contains_iff_mem, h.mem_involL]
      exact ⟨hx, hc⟩
  · intro x hx
    rw [List.contains_toArray, List.contains_iff_mem]
    exact (h.mem_involL.1 hx).1

theorem s1 : a8S1Of (a8Data ()) = true := by
  have hall : (List.range L.toArray.size).all
      (fun i => Code.mul (L.toArray[i]!) ((invsL L).toArray[i]!) == Code.one) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, List.size_toArray] at hi
    rw [h.getE hi, h.getI hi, beq_iff_eq]
    exact h.mulInv (List.getElem_mem hi)
  unfold a8S1Of
  rw [a8_elems h.enum, a8_par h.enum, a8_inverses h.enum, h.eok, h.gens, hall]
  simp [invsL, h.len]

theorem theta_eq : repThetas #[r1, r2] = #[liftTab r1 0, liftTab r2 0] := by
  simp [repThetas]

theorem invMap_getD {j : ℕ} (hj : j < L.length) :
    (invMapOf L.toArray (invsL L).toArray).getD L[j] 0 = invGo L[j] L.length L[j] := by
  rw [invMapOf_getD h.nd (by simp [invsL]), lookD, lookup_zip_getElem h.nd (by simp [invsL]) hj]
  simp [invsL]

theorem witOK_ok : witOK (a8Data ()).elems (a8Data ()).invMap (a8Data ()).reps
    (a8Data ()).theta (a8Data ()).involutions (a8Data ()).wits = true := by
  rw [a8_elems h.enum, a8_invMap' h.enum, a8_reps h.enum, a8_theta h.enum,
    a8_involutions h.enum, a8_wits h.enum, h.reps]
  unfold witOK sqWitData
  rw [Bool.and_eq_true]
  refine ⟨by simp, ?_⟩
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range, List.size_toArray] at hj
  have hg : (involL L)[j] ∈ involL L := List.getElem_mem hj
  obtain ⟨i, k, hik, hi, jj, hjj, hk, hc⟩ := h.cm_get hg
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, List.getElem_toArray, hik]
  have hinv : (invMapOf L.toArray (invsL L).toArray).getD k 0 = invGo L[jj] L.length L[jj] := by
    rw [hk]
    exact h.invMap_getD hjj
  have hs : i < (repThetas #[r1, r2]).size := by simpa [repThetas] using hi
  have hkE : L.toArray.contains k = true := by
    rw [List.contains_toArray, List.contains_iff_mem, hk]
    exact List.getElem_mem hjj
  have hi' : i < (#[r1, r2] : Array ℕ).size := by simpa using hi
  dsimp only
  rw [if_pos hs]
  dsimp only
  simp only [hinv, hkE, decide_eq_true hs, decide_eq_true hi', beq_self_eq_true, Bool.true_and,
    Bool.and_true]
  rw [hk]
  simpa [h.mulInv (List.getElem_mem hjj), List.getElem!_toArray, getElem!_pos (involL L) j hj]
    using hc

theorem mem1 : r1 ∈ L := List.mem_of_getElem? h.l1

theorem mem2 : r2 ∈ L := List.mem_of_getElem? h.l2

theorem wits_isSome : (sqWitData (classMapOfReps L.toArray (invsL L).toArray #[r1, r2])
    (repThetas #[r1, r2]) (involL L).toArray).all (fun o => o.isSome) = true := by
  unfold sqWitData
  rw [List.map_toArray, List.all_toArray, List.all_eq_true]
  intro o ho
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ho
  obtain ⟨i, k, hik, hi, _⟩ := h.cm_get hg
  have hs : i < (repThetas #[r1, r2]).size := by simpa [repThetas] using hi
  rw [hik]
  dsimp only
  rw [if_pos hs]
  rfl

theorem s2 : a8S2Of (a8Data ()) = true := by
  have g0 : (#[r1, r2] : Array ℕ)[0]! = r1 := rfl
  have g1 : (#[r1, r2] : Array ℕ)[1]! = r2 := rfl
  unfold a8S2Of
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨h.invOK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.witOK_ok⟩
  · rw [a8_reps h.enum, h.reps]
    rfl
  · rw [a8_reps h.enum, h.reps, a8_elems h.enum]
    simp [h.inv1, h.inv2, h.mem1, h.mem2]
  · rw [a8_reps h.enum, h.reps, a8_elems h.enum, h.firstInv, g0]
    simp [h.e1, h.l1]
  · rw [a8_reps h.enum, h.reps, a8_elems h.enum, a8_inverses h.enum, g0, g1, h.findTwo]
    simp [h.e2, h.l2]
  · rw [a8_reps h.enum, h.reps, a8_elems h.enum, a8_inverses h.enum, g0, g1, h.m1_contains,
      h.idx2, h.m12]
    rfl
  · rw [a8_involutions h.enum, a8_classMap h.enum, h.reps, List.all_toArray, List.all_eq_true]
    intro g hg
    exact (h.cm_contains_iff g).2 hg
  · rw [a8_involutions h.enum, a8_classMap h.enum, h.reps, h.cm_size]
    simp
  · rw [a8_wits h.enum, h.reps]
    exact h.wits_isSome

theorem s3 : a8S3Of (a8Data ()) = true := by
  unfold a8S3Of
  rw [a8_theta h.enum, a8_qmulFlat h.enum, a8_innTabs h.enum, h.reps, h.theta_eq,
    rootsOK_of h.root1 h.root2, Bool.and_true]
  simp [isHomTab_liftTab (h.iso r1 h.mem1), isHomTab_liftTab (h.iso r2 h.mem2)]

theorem s4 : a8S4Of (a8Data ()) = true := by
  unfold a8S4Of
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨h.invOK, h.witOK_ok, ?_, ?_⟩
  · rw [a8_involutions h.enum, a8_qmulFlat h.enum, Array.all_eq_true']
    intro g hg
    rw [List.all_eq_true]
    intro f _
    apply isHomTab_liftTab
    rw [Array.mem_append] at hg
    rcases hg with hg | hg
    · rw [List.mem_toArray, List.mem_singleton] at hg
      rw [hg]
      exact h.isoOne
    · rw [List.mem_toArray] at hg
      exact h.iso g (h.mem_involL.1 hg).1
  · rw [a8_wits h.enum, a8_qmulFlat h.enum, h.reps]
    unfold sqWitData
    rw [List.map_toArray, List.all_toArray, List.all_eq_true]
    intro o ho
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ho
    obtain ⟨i, k, hik, hi, jj, hjj, hk, _⟩ := h.cm_get hg
    have hs : i < (repThetas #[r1, r2]).size := by simpa [repThetas] using hi
    rw [hik]
    dsimp only
    rw [if_pos hs]
    dsimp only
    exact isHomTab_liftTab (h.iso k (hk ▸ List.getElem_mem hjj)) 0

end A8Hyp

end CFSG.KC.C690

end
