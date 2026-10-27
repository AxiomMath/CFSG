module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import Certificates.Data.Kernel.Sp62X1
public import Certificates.Data.Kernel.Sp6TwoT
public import Certificates.Data.Sp62.Involutions

public section

namespace CFSG.KC.Sp62X1

open CFSG.KD.Sp62 CFSG.KD.Sp62X1 CFSG.KD.Sp6Two CFSG.KC.Sp62 CFSG.Quasithin.H13.U3
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

theorem commutes_pk {a b : List ℕ} (ha : canon6 a = true) (hb : canon6 b = true) :
    commutes6 a b = commN (pk a) (pk b) := by
  unfold commutes6 commN
  rw [beq_pk (mulE ⟨ha, rfl⟩ ⟨hb, rfl⟩).1 (mulE ⟨hb, rfl⟩ ⟨ha, rfl⟩).1,
    (mulE ⟨ha, rfl⟩ ⟨hb, rfl⟩).2, (mulE ⟨hb, rfl⟩ ⟨ha, rfl⟩).2]

theorem contains_pk {v : List ℕ} (hv : canon6 v = true) :
    ∀ {R : List (List ℕ)}, (∀ c ∈ R, canon6 c = true) → R.contains v = memN (pk v) (R.map pk)
  | [], _ => rfl
  | a :: R, hR => by
    rw [List.contains_cons, List.map_cons, beq_pk hv (hR a List.mem_cons_self),
      contains_pk hv (fun c hc => hR c (List.mem_cons_of_mem a hc))]
    rfl

theorem erase_pk {v : List ℕ} (hv : canon6 v = true) :
    ∀ {R : List (List ℕ)}, (∀ c ∈ R, canon6 c = true) →
      (R.erase v).map pk = eraseN (pk v) (R.map pk)
  | [], _ => rfl
  | a :: R, hR => by
    have ih := erase_pk hv (fun c hc => hR c (List.mem_cons_of_mem a hc))
    have e : eraseN (pk v) ((a :: R).map pk) = Bool.rec (motive := fun _ => List ℕ)
        (pk a :: eraseN (pk v) (R.map pk)) (R.map pk) (Nat.beq (pk a) (pk v)) := rfl
    rw [List.erase_cons, e, ← beq_pk (hR a List.mem_cons_self) hv]
    cases h : (a == v)
    · simp only [Bool.false_eq_true, if_false, List.map_cons, ih]
    · simp only [if_true]

theorem cnt_pk {v : List ℕ} (hv : canon6 v = true) :
    ∀ {R : List (List ℕ)}, (∀ c ∈ R, canon6 c = true) →
      (R.filter fun w => !(w == v) && commutes6 v w).length = cntN (pk v) (R.map pk)
  | [], _ => rfl
  | a :: R, hR => by
    have ha := hR a List.mem_cons_self
    have ih := cnt_pk hv (fun c hc => hR c (List.mem_cons_of_mem a hc))
    have e : cntN (pk v) ((a :: R).map pk) = Bool.rec (motive := fun _ => ℕ)
        (cntN (pk v) (R.map pk)) (Nat.succ (cntN (pk v) (R.map pk)))
        (!Nat.beq (pk a) (pk v) && commN (pk v) (pk a)) := rfl
    rw [List.filter_cons, e, beq_pk ha hv, commutes_pk hv ha]
    cases (!Nat.beq (pk a) (pk v) && commN (pk v) (pk a))
    · simp only [Bool.false_eq_true, if_false, ih]
    · simp only [if_true, List.length_cons, ih]

theorem decide_lt (a b : ℕ) : decide (a < b) = Nat.blt a b := by
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, Nat.blt_eq]

theorem peel_pk (d : ℕ) : ∀ (P : List (List ℕ)) {R : List (List ℕ)},
    (∀ c ∈ P, canon6 c = true) → (∀ c ∈ R, canon6 c = true) →
      sp62PeelOK d R P = peelN d (R.map pk) (P.map pk)
  | [], R, _, _ => by
    rw [sp62PeelOK]
    rfl
  | v :: P, R, hP, hR => by
    have hv := hP v List.mem_cons_self
    have hR' : ∀ c ∈ R.erase v, canon6 c = true := fun c hc => hR c (List.mem_of_mem_erase hc)
    have e : peelN d (R.map pk) ((v :: P).map pk) = (memN (pk v) (R.map pk) &&
        Nat.blt (cntN (pk v) (R.map pk)) d && peelN d (eraseN (pk v) (R.map pk)) (P.map pk)) := rfl
    rw [sp62PeelOK, e, contains_pk hv hR, cnt_pk hv hR, decide_lt,
      peel_pk d P (fun c hc => hP c (List.mem_cons_of_mem v hc)) hR', erase_pk hv hR]

theorem res_pk : ∀ (P : List (List ℕ)) {R : List (List ℕ)},
    (∀ c ∈ P, canon6 c = true) → (∀ c ∈ R, canon6 c = true) →
      (sp62PeelRes R P).map pk = resN (R.map pk) (P.map pk) ∧
        ∀ c ∈ sp62PeelRes R P, canon6 c = true
  | [], R, _, hR => by
    rw [sp62PeelRes]
    exact ⟨rfl, hR⟩
  | v :: P, R, hP, hR => by
    have hv := hP v List.mem_cons_self
    have hR' : ∀ c ∈ R.erase v, canon6 c = true := fun c hc => hR c (List.mem_of_mem_erase hc)
    obtain ⟨e, c⟩ := res_pk P (fun c hc => hP c (List.mem_cons_of_mem v hc)) hR'
    have e' : resN (R.map pk) ((v :: P).map pk) = resN (eraseN (pk v) (R.map pk)) (P.map pk) :=
      rfl
    rw [sp62PeelRes, e', ← erase_pk hv hR]
    exact ⟨e, c⟩

theorem all_pk {y : List ℕ} (hy : canon6 y = true) : ∀ {L : List (List ℕ)},
    (∀ c ∈ L, canon6 c = true) →
      L.all (fun w => commutes6 w y) = allL (fun w => commN w (pk y)) (L.map pk)
  | [], _ => rfl
  | a :: L, hL => by
    rw [List.all_cons, commutes_pk (hL a List.mem_cons_self) hy,
      all_pk hy (fun c hc => hL c (List.mem_cons_of_mem a hc))]
    rfl

theorem toList_eq {α : Type} (A : Array α) (d : α) :
    A.toList = (List.range A.size).map (A.getD · d) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Array.length_toList] at h1
  simp [Array.getD_eq_getD_getElem?, h1]

theorem invs_pk {S : Array (List ℕ)} {R : ℕ → ℕ} {o n : ℕ} (hs : S.size = n)
    (hr : ∀ t < n, canon6 (S.getD t []) = true ∧ pk (S.getD t []) = recX R o t) :
    (S.toList.filter fun c => mul6 c c == one6 && !(c == one6)).map pk =
        ((List.range n).map (recX R o)).filter invN ∧
      ∀ c ∈ S.toList.filter (fun c => mul6 c c == one6 && !(c == one6)), canon6 c = true := by
  have hL : S.toList = (List.range n).map (S.getD · []) := by
    rw [toList_eq S [], hs]
  have hc : ∀ c ∈ S.toList, canon6 c = true := by
    intro c h
    rw [hL] at h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    exact (hr t (List.mem_range.1 ht)).1
  have hm : S.toList.map pk = (List.range n).map (recX R o) := by
    rw [hL, List.map_map]
    exact List.map_congr_left fun t ht => (hr t (List.mem_range.1 ht)).2
  refine ⟨?_, fun c h => hc c (List.mem_of_mem_filter h)⟩
  rw [← hm, List.filter_map]
  congr 1
  apply List.filter_congr
  intro c h
  have cc := hc c h
  have m := mulE ⟨cc, rfl⟩ ⟨cc, rfl⟩
  simp only [Function.comp, invN]
  rw [beq_pk m.1 canon6_one6, m.2, pk_one6, beq_pk cc canon6_one6, pk_one6]

theorem all_tab {E : Array (List ℕ)} {R : ℕ → ℕ} {o n hi : ℕ} (hE : E.size = n)
    (hr : ∀ t < n, canon6 (E.getD t []) = true ∧ pk (E.getD t []) = recX R o t)
    (h : CFSG.KC.Loop.allBelow n hi (fun i => Nat.beq (MULF (recX R o i) (recX R o i)) ONE &&
      CFSG.KC.Loop.allBelow n hi (fun j => commN (recX R o i) (recX R o j))) = true)
    (hm : n ≤ 64 * hi) :
    E.all (fun c => mul6 c c == one6 && E.all fun c' => commutes6 c c') = true := by
  have get : ∀ i (h : i < E.size), E[i] = E.getD i [] := fun i h => by
    simp [Array.getD_eq_getD_getElem?, h]
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < n := hE ▸ hi
  have hb := CFSG.KC.G2Three.allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true] at hb
  obtain ⟨cx, px⟩ := hr i hi'
  have m := mulE ⟨cx, px⟩ ⟨cx, px⟩
  rw [get i hi, beq_pk m.1 canon6_one6, m.2, pk_one6, hb.1, Bool.true_and, Array.all_eq_true]
  intro j hj
  have hj' : j < n := hE ▸ hj
  obtain ⟨cy, py⟩ := hr j hj'
  rw [get j hj, commutes_pk cx cy, px, py]
  exact CFSG.KC.G2Three.allBelow_g2 hb.2 hm j hj'

theorem contains_of_inTab {O : Array (List ℕ)} {R : ℕ → ℕ} {o n i : ℕ} {u : List ℕ}
    (hO : O.size = n) (hr : ∀ t < n, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R o t)
    (hu : canon6 u = true) (h : inTab R o n i (pk u) = true) : O.contains u = true := by
  simp only [inTab, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hi, he⟩ := h
  obtain ⟨c, p⟩ := hr i hi
  have e : O.getD i [] = u := pk_inj c hu (by rw [p, he])
  rw [Array.contains_iff_mem, ← e, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem (by omega)]
  exact Array.getElem_mem _

end CFSG.KC.Sp62X1

end
