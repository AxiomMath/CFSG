module

public import Certificates.Data.A6CMatK
public import CFSG.Certificates.Kernel.A6CK.Walk
public import CFSG.Certificates.Kernel.A6CK.Keys
import Mathlib.Tactic.Choose
public import CFSG.Certificates.Kernel.A6CK.Sort

public section

namespace CFSG.KC.A6CK

open Certificates.A6C

theorem eqP_self (X : Mat) : eqP X X = true := by simp [eqP]

theorem get!_map_toArray (E : List Nat) {i : Nat} (hi : i < E.length) :
    (E.map decM).toArray[i]! = decM (E.getD i 0) := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem get!_range_toArray (f : Nat → Nat) {N i : Nat} (hi : i < N) :
    ((List.range N).map f).toArray[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem rec_of_walk {stepK : Nat → Nat → Nat} {stepM : Nat → Mat → Mat} {K x0 N : Nat}
    {E : List Nat} {C : List (List Nat)} (hw : walkK stepK K x0 N E C = true)
    (hd : nodupK E = true) (hN : N ≤ 2 ^ 14) (hN0 : 0 < N) (hv0 : validK x0 = true)
    (hstep : ∀ l < K, ∀ x, validK x = true →
      validK (stepK l x) = true ∧ decM (stepK l x) = stepM l (decM x)) :
    ∃ r : Rec, derivOK stepM K (decM x0) r N = true ∧ keysNodup r.L = true ∧
      r.L = (E.map decM).toArray ∧ ∀ x ∈ E, validK x = true := by
  obtain ⟨hl, h0, hpar⟩ := walkK_spec hw
  have H : ∀ q, ∃ pr lb : Nat, 1 ≤ q → q < N →
      pr < q ∧ lb < K ∧ E.getD q 0 = stepK lb (E.getD pr 0) := by
    intro q
    by_cases h : 1 ≤ q ∧ q < N
    · obtain ⟨pr, lb, h1, h2, h3⟩ := hpar q h.1 h.2
      exact ⟨pr, lb, fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose pr lb hH using H
  have hval : ∀ q, q < N → validK (E.getD q 0) = true := by
    intro q
    induction q using Nat.strongRecOn with
    | _ q ih =>
      intro hq
      by_cases hq0 : q = 0
      · rw [hq0, h0]
        exact hv0
      · obtain ⟨h1, h2, h3⟩ := hH q (by omega) hq
        rw [h3]
        exact (hstep _ h2 _ (ih _ h1 (by omega))).1
  have hE : ∀ x ∈ E, validK x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have h1 := hval i (by omega)
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h1
  refine ⟨⟨(E.map decM).toArray, ((List.range N).map pr).toArray, ((List.range N).map lb).toArray⟩,
    ?_, keysNodup_of hE (nodupK_spec hd (by omega)), rfl, hE⟩
  unfold derivOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [hl]
  · simp
  · simp
  · rw [get!_map_toArray E (by omega), h0]
    exact eqP_self _
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · obtain ⟨h1, h2, h3⟩ := hH i (by omega) hi
      rw [get!_range_toArray pr hi, get!_range_toArray lb hi, get!_map_toArray E (by omega),
        get!_map_toArray E (by omega), h3, (hstep _ h2 _ (hval _ (by omega))).2]
      simp [h1, h2, eqP_self]

theorem gensK_spec : ∀ (G GT : List Nat), gensK G GT = true →
    GT = G.map trK ∧ ∀ g ∈ G, validK g = true ∧ simOK 6 (decM g) = true
  | [], [], _ => ⟨rfl, by simp⟩
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | g :: G, gt :: GT, h => by
    change andB (simTK g gt) (gensK G GT) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    obtain ⟨hv, ht, hs⟩ := simTK_eq h.1
    obtain ⟨ih1, ih2⟩ := gensK_spec G GT h.2
    refine ⟨by rw [ht, ih1, List.map_cons], ?_⟩
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact ⟨hv, hs⟩
    · exact ih2 g' hg'

theorem centGensK_spec {E : List Nat} {x0 : Nat} (h : centGensK E x0 = true)
    (hx0 : validK x0 = true) : ∀ e ∈ E, validK e = true ∧ simOK 6 (decM e) = true ∧
      commP 6 (decM e) (decM x0) = true := by
  unfold centGensK at h
  rw [allK_eq, List.all_eq_true] at h
  intro e he
  have h1 := h e he
  rw [andB_eq, Bool.and_eq_true] at h1
  obtain ⟨hv, _, hs⟩ := simTK_eq h1.1
  exact ⟨hv, hs, by rw [← commK_eq hv hx0]; exact h1.2⟩

theorem constK_spec {a0 g0 tau n0 r0 : Nat} (h : constK a0 g0 tau n0 r0 = true) :
    (validK a0 = true ∧ simOK 6 (decM a0) = true) ∧
    (validK g0 = true ∧ simOK 6 (decM g0) = true ∧ eqP (decM g0) (idN 6) = false ∧
      powM 6 (decM g0) 5 = idN 6) ∧
    (validK tau = true ∧ simOK 6 (decM tau) = true ∧
      eqP (mulN 6 (decM tau) (decM tau)) (idN 6) = true ∧ decM tau = tauM 6 (decM g0)) ∧
    (validK n0 = true ∧ simOK 6 (decM n0) = true ∧
      eqP (mulN 6 (decM n0) (decM g0)) (mulN 6 (mulN 6 (decM g0) (decM g0)) (decM n0)) = true) ∧
    (validK r0 = true ∧ simOK 6 (decM r0) = true) := by
  unfold constK at h
  simp only [andB_eq, notB_eq, strictB_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  obtain ⟨⟨⟨ha0, hg0⟩, hng, hp5⟩, ⟨⟨htau, htt⟩, hteq⟩, ⟨hn0, hcm⟩, hr0⟩ := h
  obtain ⟨va0, _, sa0⟩ := simTK_eq ha0
  obtain ⟨vg0, _, sg0⟩ := simTK_eq hg0
  obtain ⟨vt, _, st⟩ := simTK_eq htau
  obtain ⟨vn, _, sn⟩ := simTK_eq hn0
  obtain ⟨vr, _, sr⟩ := simTK_eq hr0
  have v2 := (decM_mulK vg0 vg0).1
  have v3 := (decM_mulK vg0 v2).1
  have v4 := (decM_mulK vg0 v3).1
  refine ⟨⟨va0, sa0⟩, ⟨vg0, sg0, ?_, ?_⟩, ⟨vt, st, ?_, ?_⟩, ⟨vn, sn, ?_⟩, ⟨vr, sr⟩⟩
  · rw [eqPK_eq vg0 validK_IDK, decM_IDK] at hng
    exact hng
  · rw [← (decM_pow5K vg0).2, hp5, decM_IDK]
  · rw [← (decM_mulK vt vt).2, ← decM_IDK, ← eqPK_eq (decM_mulK vt vt).1 validK_IDK]
    exact htt
  · rw [hteq, (decM_negK ((decM_addK ((decM_addK vg0 v2).1)
      ((decM_addK v3 v4).1))).1).2, (decM_addK (decM_addK vg0 v2).1 (decM_addK v3 v4).1).2,
      (decM_addK vg0 v2).2, (decM_addK v3 v4).2, (decM_mulK vg0 v3).2, (decM_mulK vg0 v2).2,
      (decM_mulK vg0 vg0).2]
    unfold tauM
    simp only [powM, mulN_id vg0]
  · rw [← (decM_mulK vn vg0).2, ← (decM_mulK vg0 vg0).2, ← (decM_mulK v2 vn).2,
      ← eqPK_eq (decM_mulK vn vg0).1 (decM_mulK v2 vn).1]
    exact hcm

theorem pairsAK_spec (g0 : Nat) (K0 F : List Nat) : ∀ (A : List Nat) (KA : List (List Nat)),
    pairsAK g0 K0 F A KA = true → ∀ a ∈ A, ∃ Ka, pairAK g0 K0 F a Ka = true
  | [], _, _ => by simp
  | _ :: _, [], h => nomatch h
  | a :: A, Ka :: KA, h => by
    change andB (pairAK g0 K0 F a Ka) (pairsAK g0 K0 F A KA) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact ⟨Ka, h.1⟩
    · exact pairsAK_spec g0 K0 F A KA h.2 a' ha'

theorem getD_mem {E : List Nat} {l : Nat} (hl : l < E.length) : E.getD l 0 ∈ E := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.getElem_mem hl

theorem filter_decM {L : List Nat} {a : Nat} (hL : ∀ c ∈ L, validK c = true)
    (ha : validK a = true) :
    (L.map decM).filter (fun c => commP 6 c (decM a)) = (L.filter fun c => commK c a).map decM := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    have hc := hL c List.mem_cons_self
    rw [List.map_cons, List.filter_cons, List.filter_cons, ← commK_eq hc ha,
      ih (fun c' h' => hL c' (List.mem_cons_of_mem _ h'))]
    cases commK c a
    · rfl
    · rfl

theorem inRefl_decM {FE : List Nat} {rF : Rec} (hL : rF.L = (FE.map decM).toArray)
    (hv : ∀ z ∈ FE, validK z = true) {y : Nat} (hy : validK y = true) :
    inRefl rF (decM y) = inReflK FE y := by
  unfold inRefl inReflK
  rw [hL, List.toList_toArray, anyK_eq]
  clear hL
  induction FE with
  | nil => rfl
  | cons z FE ih =>
    rw [List.map_cons, List.any_cons, List.any_cons, eqPK_eq (hv z List.mem_cons_self) hy,
      ih (fun c' h' => hv c' (List.mem_cons_of_mem _ h'))]

theorem pair_facts {g0 a : Nat} {K0 FE Ka : List Nat} {rF : Rec}
    (hLF : rF.L = (FE.map decM).toArray) (vF : ∀ z ∈ FE, validK z = true)
    (vK0 : ∀ c ∈ K0, validK c = true) (va : validK a = true) (vg0 : validK g0 = true)
    (h : pairAK g0 K0 FE a Ka = true) :
    (!(relP 6 (decM a) (decM g0)) ||
      (decide (((K0.map decM).filter fun c => commP 6 c (decM a)).length ≤ 4) &&
        ((K0.map decM).filter fun c => commP 6 c (decM a)).all
          fun c => eqP (mulN 6 c c) (idN 6))) = true ∧
    (!(relP 6 (decM a) (decM g0)) ||
      (((K0.map decM).filter fun c => commP 6 c (decM a)).all fun y1 =>
        ((K0.map decM).filter fun c => commP 6 c (decM a)).all fun y2 =>
          eqP y1 (idN 6) || eqP y2 (idN 6) || eqP y1 y2 || inRefl rF y1 || inRefl rF y2 ||
            inRefl rF (mulN 6 y1 y2))) = true := by
  rw [← relK_eq va vg0, filter_decM vK0 va]
  unfold pairAK at h
  rw [orB_eq, notB_eq] at h
  cases hr : relK a g0
  · simp
  · rw [hr] at h
    simp only [Bool.not_true, Bool.false_or, andB_eq, Bool.and_eq_true, Nat.ble_eq, lenK_eq,
      allK_eq, filtK_eq, beqLK_eq] at h
    obtain ⟨⟨hKa, hl4⟩, hsq, hpk⟩ := h
    rw [hKa]
    have vKa : ∀ c ∈ Ka, validK c = true := fun c hc =>
      vK0 c (by rw [← hKa] at hc; exact (List.mem_filter.1 hc).1)
    refine ⟨?_, ?_⟩
    · simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
        List.length_map, List.all_map, List.all_eq_true, Function.comp_apply]
      refine ⟨hl4, ?_⟩
      intro c hc
      rw [List.all_eq_true] at hsq
      have h1 := hsq c hc
      rw [eqPK_eq (decM_mulK (vKa c hc) (vKa c hc)).1 validK_IDK,
        (decM_mulK (vKa c hc) (vKa c hc)).2, decM_IDK] at h1
      exact h1
    · unfold pairsK at hpk
      rw [allK_eq, List.all_eq_true] at hpk
      simp only [Bool.not_true, Bool.false_or, List.all_map, List.all_eq_true,
        Function.comp_apply]
      intro y1 h1 y2 h2
      have h3 := hpk y1 h1
      rw [allK_eq, List.all_eq_true] at h3
      have h4 := h3 y2 h2
      have v1 := vKa y1 h1
      have v2 := vKa y2 h2
      have v12 := (decM_mulK v1 v2).1
      simp only [orB_eq] at h4
      rw [eqPK_eq v1 validK_IDK, eqPK_eq v2 validK_IDK, eqPK_eq v1 v2,
        ← inRefl_decM hLF vF v1, ← inRefl_decM hLF vF v2, ← inRefl_decM hLF vF v12,
        (decM_mulK v1 v2).2, decM_IDK] at h4
      simp only [Function.comp_apply, Bool.or_assoc] at h4 ⊢
      exact h4

theorem a6ck_sound {G GT EA ET : List Nat} {a0 g0 n0 tau r0 : Nat}
    {AE CAE TE CTE FE K0 : List Nat} {AC CAC TC CTC FC KA : List (List Nat)}
    (hG : G.map decM = (gens6 ()).toList) (hEA : EA.map decM = (eaM6 ()).toList)
    (hET : ET.map decM = (etM6 ()).toList) (ha0 : decM a0 = a0M6 ()) (hg0 : decM g0 = g0M6 ())
    (hn0 : decM n0 = nM6 ()) (hr0 : decM r0 = refl0M6 ())
    (hc : constK a0 g0 tau n0 r0 = true) (hg : gensK G GT = true)
    (hea : centGensK EA a0 = true) (het : centGensK ET tau = true)
    (hA : walkK (conjStepK G GT) 8 a0 2835 AE AC = true) (hAd : nodupK AE = true)
    (hCA : walkK (leftStepK EA) 6 IDK 9216 CAE CAC = true) (hCAd : nodupK CAE = true)
    (hT : walkK (conjStepK G GT) 8 tau 4536 TE TC = true) (hTd : nodupK TE = true)
    (hCT : walkK (leftStepK ET) 6 IDK 5760 CTE CTC = true) (hCTd : nodupK CTE = true)
    (hF : walkK (conjStepK G GT) 8 r0 252 FE FC = true) (hFd : nodupK FE = true)
    (hk0 : k0K g0 CTE K0 = true) (hp : pairsAK g0 K0 FE AE KA = true) :
    ∃ rA rCA rT rCT rF : Rec, part61 rA rCA = true ∧ part62 rT rCT = true ∧ part63 () = true ∧
      part64 rA rCT = true ∧ partK1 rF = true ∧ partK2 rA rCT rF = true := by
  obtain ⟨⟨va0, sa0⟩, ⟨vg0, sg0, ng0, pg0⟩, ⟨vt, st, ttau, dtau⟩, ⟨vn, sn, cn⟩, ⟨vr, sr⟩⟩ :=
    constK_spec hc
  obtain ⟨hGT, hGv⟩ := gensK_spec G GT hg
  have hEAv := centGensK_spec hea va0
  have hETv := centGensK_spec het vt
  have hGl : G.length = 8 := by
    have h1 := congrArg List.length hG
    rw [List.length_map, Array.length_toList] at h1
    exact h1
  have hEAl : EA.length = 6 := by
    have h1 := congrArg List.length hEA
    rw [List.length_map, Array.length_toList] at h1
    exact h1
  have hETl : ET.length = 6 := by
    have h1 := congrArg List.length hET
    rw [List.length_map, Array.length_toList] at h1
    exact h1
  have hG' : gens6 () = (G.map decM).toArray := by rw [hG, Array.toArray_toList]
  have hEA' : eaM6 () = (EA.map decM).toArray := by rw [hEA, Array.toArray_toList]
  have hET' : etM6 () = (ET.map decM).toArray := by rw [hET, Array.toArray_toList]
  have h8 : (gens6 ()).size = 8 := by rw [hG', List.size_toArray, List.length_map, hGl]
  have h6A : (eaM6 ()).size = 6 := by rw [hEA', List.size_toArray, List.length_map, hEAl]
  have h6T : (etM6 ()).size = 6 := by rw [hET', List.size_toArray, List.length_map, hETl]
  have hconj : ∀ l < 8, ∀ x, validK x = true → validK (conjStepK G GT l x) = true ∧
      decM (conjStepK G GT l x) = conjStep 6 (gens6 ()) l (decM x) := by
    intro l hl x hx
    have hl' : l < G.length := by omega
    have vg := (hGv _ (getD_mem hl')).1
    have e : (G.map trK).getD l 0 = trK (G.getD l 0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hl']
      rfl
    unfold conjStepK
    rw [getK_eq, getK_eq, hGT, e]
    have v1 := (decM_mulK vg hx).1
    refine ⟨(decM_mulK v1 (decM_trK vg).1).1, ?_⟩
    rw [(decM_mulK v1 (decM_trK vg).1).2, (decM_mulK vg hx).2, (decM_trK vg).2]
    unfold conjStep conjN
    rw [hG', get!_map_toArray G hl']
  have hleft : ∀ (E : List Nat) (A : Array Mat), A = (E.map decM).toArray →
      (∀ e ∈ E, validK e = true) → ∀ l < E.length, ∀ x, validK x = true →
      validK (leftStepK E l x) = true ∧ decM (leftStepK E l x) = leftStep 6 A l (decM x) := by
    intro E A hA hEv l hl x hx
    have vg := hEv _ (getD_mem hl)
    unfold leftStepK
    rw [getK_eq]
    refine ⟨(decM_mulK vg hx).1, ?_⟩
    rw [(decM_mulK vg hx).2]
    unfold leftStep
    rw [hA, get!_map_toArray E hl]
  obtain ⟨rA, dA, kA, LA, vA⟩ := rec_of_walk hA hAd (by decide) (by decide) va0 hconj
  obtain ⟨rCA, dCA, kCA, _, _⟩ := rec_of_walk hCA hCAd (by decide) (by decide) validK_IDK
    (fun l hl => hleft EA (eaM6 ()) hEA' (fun e he => (hEAv e he).1) l (by omega))
  obtain ⟨rT, dT, kT, _, _⟩ := rec_of_walk hT hTd (by decide) (by decide) vt hconj
  obtain ⟨rCT, dCT, kCT, LCT, vCT⟩ := rec_of_walk hCT hCTd (by decide) (by decide) validK_IDK
    (fun l hl => hleft ET (etM6 ()) hET' (fun e he => (hETv e he).1) l (by omega))
  obtain ⟨rF, dF, kF, LF, vF⟩ := rec_of_walk hF hFd (by decide) (by decide) vr hconj
  unfold k0K at hk0
  rw [andB_eq, Bool.and_eq_true, beqLK_eq, filtK_eq, Nat.beq_eq, lenK_eq] at hk0
  obtain ⟨hK0, hK0l⟩ := hk0
  have vK0 : ∀ c ∈ K0, validK c = true := fun c hc =>
    vCT c (by rw [← hK0] at hc; exact (List.mem_filter.1 hc).1)
  have hk0of : k0Of 6 (g0M6 ()) rCT = K0.map decM := by
    unfold k0Of
    rw [← hg0, LCT, List.toList_toArray, filter_decM vCT vg0, hK0]
  have pall : ∀ (A : Array Mat) (E : List Nat) (P : Mat → Bool), E.map decM = A.toList →
      (∀ e ∈ E, P (decM e) = true) → A.all P = true := by
    intro A E P hA hP
    rw [← Array.all_toList, ← hA, List.all_map, List.all_eq_true]
    intro e he
    rw [Function.comp_apply]
    exact hP e he
  have htau : decM tau = tauM 6 (g0M6 ()) := by rw [dtau, hg0]
  have pG : (gens6 ()).all (simOK 6) = true := pall _ G _ hG (fun e he => (hGv e he).2)
  have pEA : (eaM6 ()).all (fun e => simOK 6 e && commP 6 e (a0M6 ())) = true :=
    pall _ EA _ hEA (fun e he => by simp only [← ha0, (hEAv e he).2.1, (hEAv e he).2.2,
      Bool.and_self])
  have pET : (etM6 ()).all (fun e => simOK 6 e && commP 6 e (tauM 6 (g0M6 ()))) = true :=
    pall _ ET _ hET (fun e he => by simp only [← htau, (hETv e he).2.1, (hETv e he).2.2,
      Bool.and_self])
  have sa0' : simOK 6 (a0M6 ()) = true := by rw [← ha0]; exact sa0
  have sg0' : simOK 6 (g0M6 ()) = true := by rw [← hg0]; exact sg0
  have ng0' : eqP (g0M6 ()) (idN 6) = false := by rw [← hg0]; exact ng0
  have pg0' : powM 6 (g0M6 ()) 5 = idN 6 := by rw [← hg0]; exact pg0
  have st' : simOK 6 (tauM 6 (g0M6 ())) = true := by rw [← htau]; exact st
  have ttau' : eqP (mulN 6 (tauM 6 (g0M6 ())) (tauM 6 (g0M6 ()))) (idN 6) = true := by
    rw [← htau]; exact ttau
  have sn' : simOK 6 (nM6 ()) = true := by rw [← hn0]; exact sn
  have cn' : eqP (mulN 6 (nM6 ()) (g0M6 ())) (mulN 6 (mulN 6 (g0M6 ()) (g0M6 ())) (nM6 ())) =
      true := by rw [← hn0, ← hg0]; exact cn
  have sr' : simOK 6 (refl0M6 ()) = true := by rw [← hr0]; exact sr
  have dA' : derivOK (conjStep 6 (gens6 ())) (gens6 ()).size (a0M6 ()) rA 2835 = true := by
    rw [h8, ← ha0]; exact dA
  have dCA' : derivOK (leftStep 6 (eaM6 ())) (eaM6 ()).size (idN 6) rCA 9216 = true := by
    rw [h6A, ← decM_IDK]; exact dCA
  have dT' : derivOK (conjStep 6 (gens6 ())) (gens6 ()).size (tauM 6 (g0M6 ())) rT 4536 =
      true := by
    rw [h8, ← htau]; exact dT
  have dCT' : derivOK (leftStep 6 (etM6 ())) (etM6 ()).size (idN 6) rCT 5760 = true := by
    rw [h6T, ← decM_IDK]; exact dCT
  have dF' : derivOK (conjStep 6 (gens6 ())) (gens6 ()).size (refl0M6 ()) rF 252 = true := by
    rw [h8, ← hr0]; exact dF
  have hpa := pairsAK_spec g0 K0 FE AE KA hp
  refine ⟨rA, rCA, rT, rCT, rF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [part61, classOK, centOK, pG, pEA, sa0', dA', kA, dCA', kCA, Bool.and_self]
  · simp only [part62, classOK, centOK, pG, pET, sg0', ng0', pg0', st', ttau', dT', kT,
      dCT', kCT, hk0of, List.length_map, hK0l, Bool.and_self, Bool.not_false, beq_self_eq_true]
  · simp only [part63, sn', cn', Bool.and_self]
  · simp only [part64, hk0of, LA, List.toList_toArray, List.all_map, List.all_eq_true,
      Function.comp_apply]
    intro a ha
    obtain ⟨Ka, hKa⟩ := hpa a ha
    have h1 := (pair_facts LF vF vK0 (vA a ha) vg0 hKa).1
    rw [hg0] at h1
    exact h1
  · simp only [partK1, classOK, pG, sr', dF', kF, Bool.and_self]
  · simp only [partK2, hk0of, LA, List.toList_toArray, List.all_map, List.all_eq_true,
      Function.comp_apply]
    intro a ha
    obtain ⟨Ka, hKa⟩ := hpa a ha
    have h1 := (pair_facts LF vF vK0 (vA a ha) vg0 hKa).2
    rw [hg0] at h1
    exact h1

end CFSG.KC.A6CK
