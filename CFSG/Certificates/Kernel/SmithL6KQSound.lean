module

public import CFSG.GF2Type.SmithTypeE.LMod.Basic
public import CFSG.Certificates.Kernel.SmithL6KWSound
public import Certificates.Data.Kernel.SmithL6KQ

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V bit decode decode_xor decode_zero decode_two_pow
  eq_of_decode_eq)

theorem zipAllK_get {f : Nat → Nat → Bool} : ∀ {A B : List Nat}, zipAllK f A B = true →
    A.length = B.length ∧ ∀ j < A.length, f (A.getD j 0) (B.getD j 0) = true
  | a :: A, b :: B, h => by
    simp only [zipAllK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := zipAllK_get h.2
    refine ⟨by simp [h1], fun j hj => ?_⟩
    cases j with
    | zero => simpa using h.1
    | succ j => simpa using h2 j (by simpa using hj)
  | [], [], _ => ⟨rfl, fun j hj => by simp at hj⟩
  | [], _ :: _, h => by simp [zipAllK] at h
  | _ :: _, [], h => by simp [zipAllK] at h

theorem getDQ_eq {l : List Nat} {n : Nat} (h : n < l.length) : l.getD n 0 = l[n] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getDQ_mem {l : List Nat} {n : Nat} (h : n < l.length) : l.getD n 0 ∈ l := by
  rw [getDQ_eq h]
  exact List.getElem_mem h

theorem qbit_smul (b : Bool) (v : V) : bit b • v = if b then v else 0 := by
  cases b <;> simp [bit]

theorem decode_foldl_xorQ (p : Nat → Bool) (f : Nat → Nat) (n : Nat) :
    decode ((List.range n).foldl (fun acc t => if p t then acc ^^^ f t else acc) 0) =
      ∑ t ∈ Finset.range n, bit (p t) • decode (f t) := by
  induction n with
  | zero => simp [decode_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil, qbit_smul]
    split_ifs
    · rw [decode_xor]
    · rw [add_zero]

theorem foldl_xor_ltQ {p : Nat → Bool} {f : Nat → Nat} {n : Nat} (hf : ∀ t < n, f t < 2 ^ 20) :
    (List.range n).foldl (fun acc t => if p t then acc ^^^ f t else acc) 0 < 2 ^ 20 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h := ih fun t ht => hf t (by omega)
    split_ifs
    · exact Nat.xor_lt_two_pow h (hf n (by omega))
    · exact h

theorem decode_projL (Vs U : List Nat) (w : Nat) :
    decode (projL Vs U w) = ∑ t ∈ Finset.range Vs.length,
      fModel (decode w) (decode (U.getD t 0)) • decode (Vs.getD t 0) := by
  rw [projL, decode_foldl_xorQ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [fModel_decode]

theorem fModel_commQ (v w : V) : fModel v w = fModel w v := by
  rw [fModel_apply, fModel_apply, fVal, fVal,
    ← Equiv.sum_comp Fin.revPerm (fun t => v t * w (Fin.rev t))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Fin.revPerm_apply, mul_comm]

theorem proj_eq_of_memQ {A D : Fin 10 → V}
    (hAD : ∀ s t : Fin 10, fModel (A s) (D t) = if s = t then 1 else 0)
    {w : V} (hw : w ∈ Submodule.span (ZMod 2) (Set.range A)) :
    ∑ t : Fin 10, fModel w (D t) • A t = w := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hw
  have key : ∀ t : Fin 10, fModel (∑ s : Fin 10, c s • A s) (D t) = c t := by
    intro t
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hAD,
      mul_ite, mul_one, mul_zero]
    simp
  simp only [key]

section Model

variable {C : List (List Nat)} (hC : ∀ p < 1953, ∀ x, apK (C.getD p []) x = applyCols (tvCols p) x)
include hC

theorem decode_apKQ {p : Nat} (hp : p < 1953) (c : Nat) :
    decode (apK (C.getD p []) c) = tvLin p (decode c) := by
  rw [hC p hp, tvLin_decode]

theorem apKQ_lt {p : Nat} (hp : p < 1953) (c : Nat) : apK (C.getD p []) c < 2 ^ 20 := by
  rw [hC p hp]
  exact applyCols_tvCols_lt p c

end Model

theorem mem_P {P : List Nat} (hP : planePts 0 = P.toArray) {p : Nat} (h : p ∈ P) :
    p < 1953 ∧ inPlane 0 p = true := by
  have : p ∈ planePts 0 := by
    rw [hP]
    simpa using h
  exact mem_planePts.1 this

theorem mem_P_of_planeSet {P : List Nat} (hP : planePts 0 = P.toArray) {p : Fin 1953}
    (hp : p ∈ planeSet 0) : p.val ∈ P := by
  have : p.val ∈ planePts 0 := mem_planePts.2 ⟨p.2, mem_planeSet.1 hp⟩
  rw [hP] at this
  simpa using this

theorem qa_sound {W Ms P U : List Nat} {C : List (List Nat)}
    {G : List (Nat × Nat)} (hW : ∀ j < 1395, W.getD j 0 = wt j) (hWl : W.length = 1395)
    (hM : ∀ j < 1395, Ms.getD j 0 = wMask j)
    (hC : ∀ p < 1953, ∀ x, apK (C.getD p []) x = applyCols (tvCols p) x)
    (hP : planePts 0 = P.toArray) (h : qaChkK W Ms C P G U = true) :
    ∃ v : Fin 10 → V, LinearIndependent (ZMod 2) v ∧
      (∀ s, ∃ p : Fin 1953, p ∈ planeSet 0 ∧ ∃ k : Fin 1395, ¬ Opp 0 k ∧
        v s = tvLin p.val (wtV k) + wtV k) ∧
      ∀ j : Fin 1395, wtV j ∈ Submodule.span (ZMod 2) (Set.range v) ↔ adjW 0 j = true := by
  unfold qaChkK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hGl, -⟩, hG⟩, hD⟩, hZ⟩ := h
  have hVl : (qaVecsK W C G).length = 10 := by simp [qaVecsK, hGl]
  have hgen : ∀ s < 10, ∃ p k : Nat, p < 1953 ∧ inPlane 0 p = true ∧ k < 1395 ∧
      fB (wt 0) (wt k) = false ∧
      (qaVecsK W C G).getD s 0 = apK (C.getD p []) (wt k) ^^^ wt k := by
    intro s hs
    have hs' : s < G.length := by omega
    rw [List.all_eq_true] at hG
    have h1 := hG _ (List.getElem_mem hs')
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_iff_mem]
      at h1
    obtain ⟨⟨hc, hk⟩, hf⟩ := h1
    obtain ⟨hp, hpi⟩ := mem_P hP hc
    refine ⟨_, _, hp, hpi, hk, by rwa [hW 0 (by decide), hW _ hk] at hf, ?_⟩
    have e : (qaVecsK W C G).getD s 0 =
        apK (C.getD G[s].1 []) (W.getD G[s].2 0) ^^^ W.getD G[s].2 0 := by
      simp [qaVecsK, List.getD_eq_getElem?_getD, hs']
    rw [e, hW _ hk]
  have hlt : ∀ s < 10, (qaVecsK W C G).getD s 0 < 2 ^ 20 := by
    intro s hs
    obtain ⟨p, k, hp, -, -, -, he⟩ := hgen s hs
    rw [he]
    exact Nat.xor_lt_two_pow (apKQ_lt hC hp _) (wt_lt20K k)
  set A : Fin 10 → V := fun s => decode ((qaVecsK W C G).getD s.val 0) with hA
  set D : Fin 10 → V := fun t => decode (U.getD t.val 0) with hDd
  have hdual : ∀ s t : Fin 10, fModel (A s) (D t) = if s = t then 1 else 0 := by
    intro s t
    unfold dualL at hD
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hD
    rw [hA, hDd]
    simp only
    rw [fModel_decode, hD s s.2 t t.2]
    by_cases hst : s = t
    · subst hst
      simp [bit]
    · have h' : (s.val == t.val) = false := by simpa [Fin.ext_iff] using hst
      simp [h', hst, bit]
  have hli : LinearIndependent (ZMod 2) A := by
    refine Fintype.linearIndependent_iffₛ.2 fun f g hfg t => ?_
    have h := congrArg (fun w => fModel w (D t)) hfg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply, hdual, mul_ite, mul_one, mul_zero] at h
    simpa using h
  refine ⟨A, hli, fun s => ?_, fun j => ?_⟩
  · obtain ⟨p, k, hp, hpi, hk, hok, he⟩ := hgen s s.2
    refine ⟨⟨p, hp⟩, mem_planeSet.2 hpi, ⟨k, hk⟩, fun ho => ?_, ?_⟩
    · have h1 := (pairs_parts (by decide : 0 < 1395) hk).2.2.1
      rw [wtArr_get (by decide), wtArr_get hk, hok,
        (opp_iff_meetCard (by decide) hk).1 ho] at h1
      exact absurd h1 (by decide)
    · rw [hA]
      simp only
      rw [he, decode_xor, decode_apKQ hC hp]
      rfl
  · obtain ⟨-, hZ⟩ := zipAllK_get hZ
    have hj := hZ j.val (by rw [hWl]; exact j.2)
    rw [hM 0 (by decide), hM _ j.2, hW _ j.2, beq_iff_eq] at hj
    have hadj : adjW 0 j = atLeast4 (wMask 0 &&& wMask j) := rfl
    rw [hadj, hj, beq_iff_eq]
    have hsum : decode (projL (qaVecsK W C G) U (wt j)) =
        ∑ t : Fin 10, fModel (wtV j) (D t) • A t := by
      rw [decode_projL, hVl,
        ← Fin.sum_univ_eq_sum_range (fun t => fModel (decode (wt j)) (decode (U.getD t 0)) •
          decode ((qaVecsK W C G).getD t 0)) 10]
      rfl
    constructor
    · intro hmem
      have hplt : projL (qaVecsK W C G) U (wt j) < 2 ^ 20 := by
        unfold projL
        exact foldl_xor_ltQ fun t ht => hlt t (by rwa [hVl] at ht)
      refine eq_of_decode_eq hplt (wt_lt20K j) ?_
      rw [hsum]
      exact proj_eq_of_memQ hdual hmem
    · intro he
      rw [wtV, ← he, hsum]
      exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem cv_sound {W P U : List Nat} {C : List (List Nat)}
    {G : List (Nat × Nat)} (hW0 : W.getD 0 0 = wt 0)
    (hC : ∀ p < 1953, ∀ x, apK (C.getD p []) x = applyCols (tvCols p) x)
    (hP : planePts 0 = P.toArray) (h : cvChkK W C P G U = true) (v : V) :
    (∀ p ∈ planeSet 0, tvLin p.val v = v) ↔ v = 0 ∨ v = wtV 0 := by
  unfold cvChkK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    Bool.or_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hGl, hUl⟩, hfix⟩, hG⟩, hres⟩ := h
  have hgen : ∀ t < 19, ∃ p m : Nat, p < 1953 ∧ inPlane 0 p = true ∧
      (cvVecsK C G).getD t 0 = apK (C.getD p []) (2 ^ m) ^^^ 2 ^ m := by
    intro t ht
    have ht' : t < G.length := by omega
    obtain ⟨hc, -⟩ := hG _ (List.getElem_mem ht')
    obtain ⟨hp, hpi⟩ := mem_P hP hc
    refine ⟨_, G[t].2, hp, hpi, ?_⟩
    rw [getDQ_eq (by simp [cvVecsK]; omega)]
    simp [cvVecsK]
  constructor
  · intro hv
    have hw : ∀ t < 19, fModel (decode ((cvVecsK C G).getD t 0)) v = 0 := by
      intro t ht
      obtain ⟨p, m, hp, hpi, he⟩ := hgen t ht
      have hfix' := hv ⟨p, hp⟩ (mem_planeSet.2 hpi)
      have h1 : fModel (tvLin p (decode (2 ^ m))) v = fModel (decode (2 ^ m)) v := by
        calc fModel (tvLin p (decode (2 ^ m))) v =
            fModel (tvLin p (decode (2 ^ m))) (tvLin p v) := by rw [hfix']
          _ = fModel (decode (2 ^ m)) v := by
            rw [← tvEquiv_apply hp, ← tvEquiv_apply hp]
            exact fModel_tvEquiv hp _ _
      rw [he, decode_xor, decode_apKQ hC hp, map_add, LinearMap.add_apply, h1]
      exact CharTwo.add_self_eq_zero _
    have hres' : ∀ m : Fin 20, Pi.single m (1 : ZMod 2) + ∑ t ∈ Finset.range 19,
        fModel (Pi.single m 1) (decode ((cvVecsK C G).getD t 0)) • decode (U.getD t 0) ∈
          Submodule.span (ZMod 2) {wtV 0} := by
      intro m
      have e : decode (2 ^ m.val ^^^ projL U (cvVecsK C G) (2 ^ m.val)) =
          Pi.single m (1 : ZMod 2) + ∑ t ∈ Finset.range 19,
            fModel (Pi.single m 1) (decode ((cvVecsK C G).getD t 0)) • decode (U.getD t 0) := by
        rw [decode_xor, decode_projL, hUl, decode_two_pow]
      rw [← e]
      rcases hres m m.2 with h | h
      · rw [h, decode_zero]
        exact Submodule.zero_mem _
      · rw [h, hW0]
        exact Submodule.mem_span_singleton_self _
    have hsum : v = ∑ m : Fin 20, v m • Pi.single m (1 : ZMod 2) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    have h0 : ∑ m : Fin 20, v m • ∑ t ∈ Finset.range 19,
        fModel (Pi.single m 1) (decode ((cvVecsK C G).getD t 0)) • decode (U.getD t 0) = 0 := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [← Finset.sum_smul]
      have e : ∑ m : Fin 20, v m * fModel (Pi.single m 1) (decode ((cvVecsK C G).getD t 0)) =
          fModel v (decode ((cvVecsK C G).getD t 0)) := by
        conv_rhs => rw [hsum]
        simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [e, fModel_commQ, hw t (Finset.mem_range.1 ht), zero_smul]
    have hv' : v = ∑ m : Fin 20, v m • (Pi.single m (1 : ZMod 2) + ∑ t ∈ Finset.range 19,
        fModel (Pi.single m 1) (decode ((cvVecsK C G).getD t 0)) • decode (U.getD t 0)) := by
      simp only [smul_add, Finset.sum_add_distrib]
      rw [h0, add_zero]
      exact hsum
    have hmem : v ∈ Submodule.span (ZMod 2) {wtV 0} := by
      rw [hv']
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hres' m)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · left
      rw [← ha, zero_smul]
    · right
      rw [← ha, one_smul]
  · rintro (rfl | rfl)
    · intro p _
      exact map_zero _
    · intro p hp
      have h1 := hfix _ (mem_P_of_planeSet hP hp)
      rw [hW0] at h1
      rw [wtV, ← decode_apKQ hC p.2, h1]

end CFSG.SmithL6.K
