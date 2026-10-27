module

public import CFSG.Certificates.Kernel.Cert690.MulSound
public import CFSG.Certificates.Kernel.Cert690.HashSound
import CFSG.Certificates.Kernel.Cert690.TreeSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

private def ksBFstep (G : Array ℕ) (v i : ℕ)
    (st : Array ℕ × Array (ℕ × ℕ) × Std.HashSet ℕ) (j : ℕ) :
    Array ℕ × Array (ℕ × ℕ) × Std.HashSet ℕ :=
  let y := Code.mul v (G[j]!)
  if st.2.2.contains y then st else (st.1.push y, st.2.1.push (i, j), st.2.2.insert y)

private theorem ksBFgo_succ (G A : Array ℕ) (v i f : ℕ) (par : Array (ℕ × ℕ))
    (seen : Std.HashSet ℕ) (hv : A[i]! = v) :
    enumData.go G (f + 1) A par seen i =
      (if i < A.size then
        let st : Array ℕ × Array (ℕ × ℕ) × Std.HashSet ℕ :=
          (List.range G.size).foldl (ksBFstep G v i) (A, par, seen)
        enumData.go G f st.1 st.2.1 st.2.2 (i + 1)
      else (A, par)) := by
  rw [enumData.go.eq_2, hv]
  rfl

private theorem ksBFgo_idle (G A : Array ℕ) (par : Array (ℕ × ℕ)) (seen : Std.HashSet ℕ)
    (i : ℕ) (h : A.size ≤ i) : ∀ fuel, enumData.go G fuel A par seen i = (A, par)
  | 0 => rfl
  | f + 1 => by
    rw [enumData.go.eq_2, if_neg (by omega)]

private theorem ksBFtake_push {α : Type} [Inhabited α] {l : List α} {c : ℕ} {y : α}
    (hc : c < l.length) (h : l[c]'hc = y) :
    (l.take c).toArray.push y = (l.take (c + 1)).toArray := by
  rw [Array.push_eq_append, Array.toArray_append, List.take_succ, List.getElem?_eq_getElem hc,
    Option.toList_some, ← h]

private theorem ksBFseen_insert {E : List ℕ} {c : ℕ} {y : ℕ} {seen : Std.HashSet ℕ}
    (hc : c < E.length) (hE : E[c]'hc = y)
    (h : ∀ z, seen.contains z = true ↔ z ∈ E.take c) :
    ∀ z, (seen.insert y).contains z = true ↔ z ∈ E.take (c + 1) := by
  intro z
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, h z, List.take_succ,
    List.getElem?_eq_getElem hc, Option.toList_some, List.mem_append, List.mem_singleton, hE]
  tauto

private theorem ksBFdrop_succ {α : Type} {l : List α} {c : ℕ} {a : α} {l' : List α}
    (h : l.drop c = a :: l') : ∃ (hc : c < l.length), l[c]'hc = a ∧ l' = l.drop (c + 1) := by
  have hc : c < l.length := by
    have h2 := congrArg List.length h
    rw [List.length_drop, List.length_cons] at h2
    omega
  rw [List.drop_eq_getElem_cons hc] at h
  obtain ⟨h1, h2⟩ := List.cons.inj h
  exact ⟨hc, h1, h2.symm⟩

private theorem ksBFdrop_cons {gs L' : List ℕ} {g j : ℕ} (h : g :: L' = gs.drop j) :
    ∃ (hj : j < gs.length), gs[j]'hj = g ∧ L' = gs.drop (j + 1) ∧ gs.toArray[j]! = g := by
  have hj : j < gs.length := by
    have h2 := congrArg List.length h
    simp only [List.length_cons, List.length_drop] at h2
    omega
  rw [List.drop_eq_getElem_cons hj] at h
  obtain ⟨h1, h2⟩ := List.cons.inj h
  exact ⟨hj, h1.symm, h2, by rw [List.getElem!_toArray, getElem!_pos gs j hj, h1.symm]⟩

private theorem ksBFgen_cons {ix : ℕ → ℕ} {x i : ℕ} {k : ℕ → List ℕ → List (ℕ × ℕ) → Bool}
    {g : ℕ} {L' : List ℕ} {j c : ℕ} {Er : List ℕ} {Pr : List (ℕ × ℕ)}
    (h : bfsGen ix x i k (g :: L') j c Er Pr = true) :
    (ix (mulF x g) < c ∧ bfsGen ix x i k L' (j + 1) c Er Pr = true) ∨
      (ix (mulF x g) = c ∧ ∃ (e : ℕ) (Er' : List ℕ) (p : ℕ × ℕ) (Pr' : List (ℕ × ℕ)),
        Er = e :: Er' ∧ Pr = p :: Pr' ∧ e = mulF x g ∧ p.1 = i ∧ p.2 = j ∧
          bfsGen ix x i k L' (j + 1) (c + 1) Er' Pr' = true) := by
  simp only [bfsGen, strictB_eq] at h ⊢
  cases hb : Nat.blt (ix (mulF x g)) c with
  | true =>
    rw [hb] at h
    exact Or.inl ⟨by simpa only [Nat.blt_eq] using hb, h⟩
  | false =>
    rw [hb] at h
    cases hb2 : Nat.beq (ix (mulF x g)) c with
    | false => rw [hb2] at h; dsimp only [] at h; simp at h
    | true =>
      rw [hb2] at h
      refine Or.inr ⟨by simpa only [Nat.beq_eq] using hb2, ?_⟩
      cases Er with
      | nil => simp at h
      | cons e Er' =>
        cases Pr with
        | nil => simp at h
        | cons p Pr' =>
          dsimp only [] at h
          simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
          obtain ⟨⟨hey, hpi, hpj⟩, hrun⟩ := h
          exact ⟨e, Er', p, Pr', rfl, rfl, hey, hpi, hpj, hrun⟩

private theorem ksBFstep_lt (G : Array ℕ) (x i : ℕ) (B : Array ℕ) (par : Array (ℕ × ℕ))
    (seen : Std.HashSet ℕ) (j : ℕ) (h : seen.contains (Code.mul x (G[j]!)) = true) :
    ksBFstep G x i (B, par, seen) j = (B, par, seen) := by
  simp only [ksBFstep]
  rw [if_pos h]

private theorem ksBFstep_push (G : Array ℕ) (x i : ℕ) (B : Array ℕ) (par : Array (ℕ × ℕ))
    (seen : Std.HashSet ℕ) (j : ℕ) (h : seen.contains (Code.mul x (G[j]!)) = false) :
    ksBFstep G x i (B, par, seen) j =
      (B.push (Code.mul x (G[j]!)), par.push (i, j), seen.insert (Code.mul x (G[j]!))) := by
  simp only [ksBFstep]
  rw [if_neg (by simpa using h)]

private theorem ksBFfold_succ (G : Array ℕ) (x i j : ℕ) (B : Array ℕ) (par : Array (ℕ × ℕ))
    (seen : Std.HashSet ℕ) (L' : List ℕ) :
    (List.range' j (L'.length + 1)).foldl (ksBFstep G x i) (B, par, seen) =
      (List.range' (j + 1) L'.length).foldl (ksBFstep G x i)
        (ksBFstep G x i (B, par, seen) j) := by
  rw [List.range'_succ, List.foldl_cons]

private def ksBFOut (G : Array ℕ) (E : List ℕ) (P : List (ℕ × ℕ)) (x i j c : ℕ)
    (st : Array ℕ × Array (ℕ × ℕ) × Std.HashSet ℕ) (L : List ℕ) (c' : ℕ)
    (seen' : Std.HashSet ℕ) : Prop :=
  c ≤ c' ∧ c' ≤ E.length ∧ i < c' ∧
    (∀ y, seen'.contains y = true ↔ y ∈ E.take c') ∧
    (List.range' j L.length).foldl (ksBFstep G x i) st =
      ((E.take c').toArray, (P.take c').toArray, seen')

private theorem ksBFpost_push {ix : ℕ → ℕ} {gs E : List ℕ} {P : List (ℕ × ℕ)} {x i : ℕ}
    {g : ℕ} {L' : List ℕ} {j c : ℕ} {B : Array ℕ} {par : Array (ℕ × ℕ)}
    {seen : Std.HashSet ℕ} {Er : List ℕ} {Pr : List (ℕ × ℕ)} {e : ℕ} {Er' : List ℕ}
    {p : ℕ × ℕ} {Pr' : List (ℕ × ℕ)} (hix : ∀ y, ix y = E.idxOf y)
    (hL : g :: L' = gs.drop j) (hB : B = (E.take c).toArray)
    (hpar : par = (P.take c).toArray) (hEr : Er = E.drop c) (hPr : Pr = P.drop c)
    (hErB : Er = e :: Er') (hPrB : Pr = p :: Pr') (htc : ix (mulF x g) = c)
    (hey : e = mulF x g) (hp1 : p.1 = i) (hp2 : p.2 = j) (hi : i < c)
    (hseen : ∀ y, seen.contains y = true ↔ y ∈ E.take c) :
    (List.range' j (L'.length + 1)).foldl (ksBFstep gs.toArray x i) (B, par, seen) =
        (List.range' (j + 1) L'.length).foldl (ksBFstep gs.toArray x i)
          ((E.take (c + 1)).toArray, (P.take (c + 1)).toArray,
            seen.insert (Code.mul x (gs.toArray[j]!))) ∧
      (∀ y, (seen.insert (Code.mul x (gs.toArray[j]!))).contains y = true ↔ y ∈ E.take (c + 1)) ∧
      c + 1 ≤ E.length ∧ i < c + 1 := by
  obtain ⟨hj, hgj, hL', hGj⟩ := ksBFdrop_cons hL
  obtain ⟨hclen, hEc, hEr'⟩ := ksBFdrop_succ (hEr.symm.trans hErB)
  obtain ⟨hPlen, hPc, hPr'⟩ := ksBFdrop_succ (hPr.symm.trans hPrB)
  have hp : p = (i, j) := Prod.ext hp1 hp2
  have hyE : mulF x g ∈ E := by
    simpa only [← hey, hEc] using List.getElem_mem hclen
  have hidx : E.idxOf (mulF x g) = c := by rw [← hix (mulF x g), htc]
  have hnotmem : mulF x g ∉ E.take c := by
    intro hm
    have := (List.mem_take_iff_idxOf_lt hyE).1 hm
    omega
  have hs : seen.contains (Code.mul x (gs.toArray[j]!)) = false := by
    cases hh : seen.contains (Code.mul x (gs.toArray[j]!)) with
    | false => rfl
    | true =>
      rw [hGj, ← mulF_eq] at hh
      exact absurd ((hseen _).1 hh) hnotmem
  have hEc' : E[c]'hclen = Code.mul x (gs.toArray[j]!) := by rw [hEc, hey, mulF_eq, hGj]
  have hB' : B.push (Code.mul x (gs.toArray[j]!)) = (E.take (c + 1)).toArray := by
    rw [hB]
    exact ksBFtake_push hclen hEc'
  have hpar' : par.push (i, j) = (P.take (c + 1)).toArray := by
    rw [hpar]
    exact ksBFtake_push hPlen (hPc.trans hp)
  refine ⟨?_, ksBFseen_insert hclen hEc' hseen, by omega, by omega⟩
  rw [ksBFfold_succ, ksBFstep_push _ _ _ _ _ _ _ hs, hB', hpar']

private theorem ksBFgen_fold {ix : ℕ → ℕ} {gs E : List ℕ} {P : List (ℕ × ℕ)}
    {x i : ℕ} {k : ℕ → List ℕ → List (ℕ × ℕ) → Bool} (hix : ∀ y, ix y = E.idxOf y) :
    ∀ (L : List ℕ) (j c : ℕ) (B : Array ℕ) (par : Array (ℕ × ℕ)) (seen : Std.HashSet ℕ)
      (Er : List ℕ) (Pr : List (ℕ × ℕ)),
      L = gs.drop j → B = (E.take c).toArray → par = (P.take c).toArray →
      Er = E.drop c → Pr = P.drop c → c ≤ E.length → i < c →
      (∀ y, seen.contains y = true ↔ y ∈ E.take c) →
      bfsGen ix x i k L j c Er Pr = true →
      ∃ (c' : ℕ) (seen' : Std.HashSet ℕ),
        ksBFOut gs.toArray E P x i j c (B, par, seen) L c' seen' ∧
          k c' (E.drop c') (P.drop c') = true := by
  intro L
  induction L with
  | nil =>
    intro j c B par seen Er Pr hL hB hpar hEr hPr hc hi hseen hgen
    refine ⟨c, seen, ⟨le_rfl, hc, hi, hseen, ?_⟩, ?_⟩
    · simp only [List.length_nil, List.range'_zero, List.foldl_nil, hB, hpar]
    · rw [← hEr, ← hPr]
      exact hgen
  | cons g L' ih =>
    intro j c B par seen Er Pr hL hB hpar hEr hPr hc hi hseen hgen
    obtain ⟨hj, hgj, hL', hGj⟩ := ksBFdrop_cons hL
    obtain ⟨hlt, hrun⟩ | ⟨htc, e, Er', p, Pr', hErB, hPrB, hey, hp1, hp2, hrun⟩ :=
      ksBFgen_cons hgen
    · have hidx : E.idxOf (mulF x g) < c := by
        rw [hix] at hlt
        exact hlt
      have hyE : mulF x g ∈ E := List.idxOf_lt_length_iff.mp (by omega)
      have hmem : mulF x g ∈ E.take c := (List.mem_take_iff_idxOf_lt hyE).2 hidx
      have hs : seen.contains (Code.mul x (gs.toArray[j]!)) = true := by
        rw [hGj, ← mulF_eq]
        exact (hseen _).2 hmem
      obtain ⟨c', seen', ⟨hcc, hcE, hic, hseen', hfold⟩, hk⟩ :=
        ih (j + 1) c B par seen Er Pr hL' hB hpar hEr hPr hc hi hseen hrun
      refine ⟨c', seen', ⟨hcc, hcE, hic, hseen', ?_⟩, hk⟩
      rw [show (g :: L').length = L'.length + 1 from rfl, ksBFfold_succ,
        ksBFstep_lt _ _ _ _ _ _ _ hs]
      exact hfold
    · obtain ⟨hclen, hEc, hEr'⟩ := ksBFdrop_succ (hEr.symm.trans hErB)
      obtain ⟨hPlen, hPc, hPr'⟩ := ksBFdrop_succ (hPr.symm.trans hPrB)
      obtain ⟨hfold, hseen', hcE, hic⟩ :=
        ksBFpost_push hix hL hB hpar hEr hPr hErB hPrB htc hey hp1 hp2 hi hseen
      obtain ⟨c', seen', ⟨hcc, hcE', hic', hseen'', hfold'⟩, hk⟩ :=
        ih (j + 1) (c + 1) (E.take (c + 1)).toArray (P.take (c + 1)).toArray
          (seen.insert (Code.mul x (gs.toArray[j]!))) Er' Pr' hL' rfl rfl hEr' hPr' hcE hic hseen'
          hrun
      exact ⟨c', seen', ⟨by omega, hcE', hic', hseen'', by
        rw [show (g :: L').length = L'.length + 1 from rfl, hfold, hfold']⟩, hk⟩

private theorem ksBFrange_zero (n : ℕ) : List.range' 0 n = List.range n := by
  rw [List.range'_eq_map_range]
  simp

private theorem ksBFrun_nil {ix : ℕ → ℕ} {gs : List ℕ} {n : ℕ} {i c : ℕ} {Er : List ℕ}
    {Pr : List (ℕ × ℕ)} : bfsRun ix gs n [] i c Er Pr = true ↔ c = n := by
  rw [bfsRun, Nat.beq_eq]

private theorem ksBFrun_cons {ix : ℕ → ℕ} {gs : List ℕ} {n : ℕ} {x : ℕ} {xs : List ℕ}
    {i c : ℕ} {Er : List ℕ} {Pr : List (ℕ × ℕ)} :
    bfsRun ix gs n (x :: xs) i c Er Pr = true ↔
      (i < c ∧ bfsGen ix x i (fun c Er Pr => bfsRun ix gs n xs (i + 1) c Er Pr) gs 0 c Er Pr =
        true) := by
  simp only [bfsRun, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq]

private theorem ksBFgo_run {ix : ℕ → ℕ} {gs E : List ℕ} {P : List (ℕ × ℕ)}
    (hix : ∀ y, ix y = E.idxOf y) (hPlen : P.length = E.length) :
    ∀ (xs : List ℕ) (i c : ℕ) (Er : List ℕ) (Pr : List (ℕ × ℕ)) (fuel : ℕ)
      (seen : Std.HashSet ℕ),
      xs = E.drop i → Er = E.drop c → Pr = P.drop c → i ≤ c → c ≤ E.length →
      (∀ y, seen.contains y = true ↔ y ∈ E.take c) →
      xs.length ≤ fuel →
      bfsRun ix gs E.length xs i c Er Pr = true →
      enumData.go gs.toArray fuel (E.take c).toArray (P.take c).toArray seen i =
        (E.toArray, P.toArray) := by
  intro xs
  induction xs with
  | nil =>
    intro i c Er Pr fuel seen hxs hEr hPr hic hcE hseen hfuel hrun
    rw [ksBFrun_nil] at hrun
    have hlen : E.length ≤ i := by
      have h := congrArg List.length hxs
      rw [List.length_nil, List.length_drop] at h
      omega
    have hc : E.take c = E := by rw [hrun, List.take_length]
    have hP : P.take c = P := by rw [hrun, ← hPlen, List.take_length]
    rw [hc, hP]
    exact ksBFgo_idle gs.toArray E.toArray P.toArray seen i (by rw [List.size_toArray]; omega) fuel
  | cons x xs ih =>
    intro i c Er Pr fuel seen hxs hEr hPr hic hcE hseen hfuel hrun
    obtain ⟨hic', hgen⟩ := (ksBFrun_cons (n := E.length)).1 hrun
    have hilen : i < E.length := by omega
    have hcons : x :: xs = E[i] :: E.drop (i + 1) := by rw [hxs, List.drop_eq_getElem_cons hilen]
    obtain ⟨hx, hxs'⟩ := List.cons.inj hcons
    have hsize : (E.take c).toArray.size = c := by rw [List.size_toArray, List.length_take]; omega
    have hAi : (E.take c).toArray[i]! = x := by
      rw [List.getElem!_toArray, getElem!_pos _ _ (by rw [List.length_take]; omega),
        List.getElem_take, ← hx]
    obtain ⟨c', seen', hcell, hk⟩ :=
      ksBFgen_fold (gs := gs) (E := E) (P := P) (x := x) (i := i)
        (k := fun c Er Pr => bfsRun ix gs E.length xs (i + 1) c Er Pr) hix
        gs 0 c (E.take c).toArray (P.take c).toArray seen Er Pr (by simp) rfl rfl hEr hPr hcE hic'
        hseen hgen
    obtain ⟨hcc, hcE', hic2, hseen', hfold⟩ := hcell
    cases fuel with
    | zero => simp only [List.length_cons] at hfuel; omega
    | succ f =>
      rw [ksBFgo_succ gs.toArray (E.take c).toArray x i f (P.take c).toArray seen hAi]
      dsimp only []
      rw [if_pos (by rw [hsize]; omega)]
      rw [List.size_toArray, ← ksBFrange_zero gs.length, hfold]
      refine ih (i + 1) c' (E.drop c') (P.drop c') f seen' hxs' rfl rfl (by omega) hcE' hseen'
        ?_ hk
      simp only [List.length_cons] at hfuel
      omega

theorem enumData_of_bfsOK {ix : ℕ → ℕ} {gs E : List ℕ} {P : List (ℕ × ℕ)}
    (hix : ∀ y, ix y = E.idxOf y) (h : bfsOK ix gs E P = true) {fuel : ℕ}
    (hf : E.length ≤ fuel) : enumData gs fuel = (E.toArray, P.toArray) := by
  rw [bfsOK] at h
  cases E with
  | nil => simp at h
  | cons e Er =>
    cases P with
    | nil => simp at h
    | cons p Pr =>
      simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨⟨he, hp1, hp2⟩, hPlen, hrun⟩ := h
      have hec : e = Code.one := he.trans oneF_eq
      have hp : p = (0, 0) := Prod.ext hp1 hp2
      have hA : #[Code.one] = ((e :: Er).take 1).toArray := by
        rw [show (e :: Er).take 1 = [e] from rfl, ← hec]
      have hB : #[(0, 0)] = ((p :: Pr).take 1).toArray := by
        rw [show (p :: Pr).take 1 = [p] from rfl, ← hp]
      have hseen : ∀ y, ((∅ : Std.HashSet ℕ).insert Code.one).contains y = true ↔
          y ∈ (e :: Er).take 1 := by
        intro y
        rw [Std.HashSet.contains_insert, show (e :: Er).take 1 = [e] from rfl, List.mem_singleton,
          Std.HashSet.contains_empty, Bool.or_eq_true, beq_iff_eq, hec, Bool.false_eq_true]
        rw [or_false]
        exact eq_comm
      rw [enumData, hA, hB]
      exact ksBFgo_run hix hPlen (e :: Er) 0 1 Er Pr fuel ((∅ : Std.HashSet ℕ).insert Code.one)
        (by simp) rfl rfl (Nat.zero_le 1) (by simp) hseen hf hrun

theorem ifN_eq (c : Bool) (t e : ℕ) : ifN c t e = if c then t else e := by cases c <;> rfl

theorem invStep_eq (x : ℕ) (k : ℕ → ℕ) (y : ℕ) :
    invStep x k y = if Code.mul y x = Code.one then y else k (Code.mul y x) := by
  unfold invStep
  rw [ifN_eq, mulF_eq, oneF_eq]
  by_cases h : Code.mul y x = Code.one
  · rw [if_pos h, if_pos (by simpa using h)]
  · rw [if_neg h, if_neg (by simpa using h)]

theorem invGo_succ (x f y : ℕ) :
    invGo x (f + 1) y = if Code.mul y x = Code.one then y else invGo x f (Code.mul y x) :=
  invStep_eq x (invGo x f) y

theorem codeInv_go_eq (x : ℕ) : ∀ fuel y, codeInv.go x fuel y = invGo x fuel y
  | 0, _ => rfl
  | f + 1, y => by
    rw [codeInv.go, invGo_succ]
    by_cases h : Code.mul y x = Code.one
    · simp [h]
    · simp only [h, beq_iff_eq, if_false]
      exact codeInv_go_eq x f _

theorem codeInv_eq (bound x : ℕ) : codeInv bound x = invGo x bound x := codeInv_go_eq x bound x

theorem andK_eq (a b : Bool) : andK a b = (a && b) := by cases a <;> rfl

theorem invK_spec (T : IT) (n : ℕ) :
    ∀ (E inv : List ℕ), invK T n E inv = true → inv = E.map fun x => T.find (invGo x n x) n
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [invK])
  | _ :: _, [], h => absurd h (by simp [invK])
  | x :: E, j :: inv, h => by
    have h' : andK (Nat.beq (T.find (invGo x n x) n) j) (invK T n E inv) = true := h
    rw [andK_eq, Bool.and_eq_true, Nat.beq_eq] at h'
    rw [List.map_cons, invK_spec T n E inv h'.2, h'.1]

theorem invI_of {E inv : List ℕ} {T : IT} (hnd : E.Nodup)
    (hT : ∀ c, T.find c E.length = E.idxOf c) (h : invK T E.length E inv = true) :
    (invArr E.toArray).map (fun c => (idxMapOf E.toArray).getD c E.toArray.size) =
      inv.toArray := by
  rw [invK_spec T E.length E inv h]
  unfold invArr
  rw [List.map_toArray, List.map_toArray, List.size_toArray, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, codeInv_eq, idxMapOf_getD hnd, hT]

end CFSG.KC.C690

end
