module

public import CFSG.Certificates.Kernel.A6CK.Bridge

public section

namespace CFSG.KC.A6CK

theorem lenK_go (L : List Nat) : ∀ n, List.rec (motive := fun _ => Nat → Nat) (fun n => n)
    (fun _ _ ih n => strictN (Nat.succ n) ih) L n = n + L.length := by
  induction L with
  | nil => intro n; rfl
  | cons x L ih =>
    intro n
    change strictN (Nat.succ n) _ = _
    rw [strictN_eq, ih, List.length_cons]
    omega

theorem lenK_eq (L : List Nat) : lenK L = L.length := by
  unfold lenK
  rw [lenK_go]
  omega

theorem getK_eq (L : List Nat) : ∀ i, getK L i = L.getD i 0 := by
  induction L with
  | nil => intro i; rfl
  | cons x L ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      change getK L i = _
      rw [ih]
      rfl

theorem allK_eq (p : Nat → Bool) (L : List Nat) : allK p L = L.all p := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change andB (p x) (allK p L) = _
    rw [andB_eq, ih, List.all_cons]

theorem anyK_eq (p : Nat → Bool) (L : List Nat) : anyK p L = L.any p := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change orB (p x) (anyK p L) = _
    rw [orB_eq, ih, List.any_cons]

theorem filtK_eq (p : Nat → Bool) (L : List Nat) : filtK p L = L.filter p := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Bool.rec (motive := fun _ => List Nat) (filtK p L) (x :: filtK p L) (p x) = _
    rw [ih, List.filter_cons]
    cases p x <;> rfl

theorem beqLK_eq (L : List Nat) : ∀ M, beqLK L M = true ↔ L = M := by
  induction L with
  | nil =>
    intro M
    cases M with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons y M => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | cons x L ih =>
    intro M
    cases M with
    | nil => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | cons y M =>
      change andB (Nat.beq x y) (beqLK L M) = true ↔ _
      rw [andB_eq, Bool.and_eq_true, Nat.beq_eq, ih, List.cons.injEq]

theorem getD_drop (F : List Nat) (p j : Nat) : (F.drop p).getD j 0 = F.getD (p + j) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem drop_succ_of {F E' : List Nat} {i x : Nat} (h : F.drop i = x :: E') :
    F.drop (i + 1) = E' ∧ F.getD i 0 = x := by
  constructor
  · rw [← List.drop_drop, h]
    rfl
  · have h1 := getD_drop F i 0
    rw [h, Nat.add_zero] at h1
    exact h1.symm

theorem kidsK_spec (step : Nat → Nat → Nat) (K x i : Nat) (k : List Nat → Nat → Bool) :
    ∀ (g cs : List Nat) (p : Nat), kidsK step K x i k g cs p = true →
      ∃ cs', cs = g.map (fun l => step l x) ++ cs' ∧ (∀ l ∈ g, l < K) ∧ (g ≠ [] → i < p) ∧
        k cs' (p + g.length) = true
  | [], cs, p, h => ⟨cs, rfl, by simp, by simp, by rw [List.length_nil, Nat.add_zero]; exact h⟩
  | l :: g, [], p, h => nomatch h
  | l :: g, y :: cs, p, h => by
    have e : kidsK step K x i k (l :: g) (y :: cs) p = andB (andB (Nat.blt l K) (Nat.blt i p))
        (andB (Nat.beq y (step l x)) (strictB (Nat.succ p) fun p' => kidsK step K x i k g cs p')) :=
      rfl
    rw [e, andB_eq, andB_eq, andB_eq, strictB_eq] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hl, hi⟩, hy, hrest⟩ := h
    obtain ⟨cs', hcs, hg, _, hk⟩ := kidsK_spec step K x i k g cs (p + 1) hrest
    refine ⟨cs', ?_, ?_, fun _ => hi, ?_⟩
    · rw [hcs, hy]
      rfl
    · intro l' hl'
      rcases List.mem_cons.1 hl' with h' | h'
      · rw [h']
        exact hl
      · exact hg _ h'
    · have e2 : p + (l :: g).length = p + 1 + g.length := by
        rw [List.length_cons]
        omega
      rw [e2]
      exact hk

theorem runK_spec (step : Nat → Nat → Nat) (K : Nat) (F : List Nat) :
    ∀ (E : List Nat) (Cs : List (List Nat)) (cs : List Nat) (i p : Nat),
      F.drop i = E → F.drop p = cs → runK step K E Cs cs i p = true →
      ∀ q, p ≤ q → q < F.length →
        ∃ pr lb, i ≤ pr ∧ pr < q ∧ lb < K ∧ F.getD q 0 = step lb (F.getD pr 0)
  | [], Cs, cs, i, p, _, hcs, h, q, hq1, hq2 => by
    have e : runK step K [] Cs cs i p = andB (List.rec (motive := fun _ => Bool) true
        (fun _ _ _ => false) Cs) (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs) :=
      rfl
    rw [e, andB_eq, Bool.and_eq_true] at h
    cases cs with
    | nil =>
      have h1 := congrArg List.length hcs
      rw [List.length_drop, List.length_nil] at h1
      omega
    | cons _ _ => exact nomatch h.2
  | x :: E', [], cs, i, p, _, _, h, _, _, _ => nomatch h
  | x :: E', g :: Cs', cs, i, p, hE, hcs, h, q, hq1, hq2 => by
    have e : runK step K (x :: E') (g :: Cs') cs i p = kidsK step K x i (fun cs' p' =>
        strictB (Nat.succ i) fun i' => runK step K E' Cs' cs' i' p') g cs p := rfl
    rw [e] at h
    obtain ⟨cs', hc, hl, hip, hk⟩ := kidsK_spec step K x i _ g cs p h
    rw [strictB_eq] at hk
    obtain ⟨hE', hx⟩ := drop_succ_of hE
    by_cases hq : q < p + g.length
    · have hj : q - p < g.length := by omega
      refine ⟨i, g[q - p], Nat.le_refl _, ?_, hl _ (List.getElem_mem hj), ?_⟩
      · have := hip (List.ne_nil_of_length_pos (by omega))
        omega
      · rw [hx]
        have h1 := getD_drop F p (q - p)
        rw [hcs, hc, Nat.add_sub_cancel' hq1] at h1
        rw [← h1, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by rw [List.length_map]; exact hj), List.getElem?_map,
          List.getElem?_eq_getElem hj]
        rfl
    · have hcs' : F.drop (p + g.length) = cs' := by
        rw [← List.drop_drop, hcs, hc]
        exact List.drop_left' (List.length_map _)
      obtain ⟨pr, lb, h1, h2, h3, h4⟩ :=
        runK_spec step K F E' Cs' cs' (i + 1) (p + g.length) hE' hcs' hk q (by omega) hq2
      exact ⟨pr, lb, by omega, h2, h3, h4⟩

theorem walkK_spec {step : Nat → Nat → Nat} {K x0 N : Nat} {E : List Nat} {C : List (List Nat)}
    (h : walkK step K x0 N E C = true) :
    E.length = N ∧ E.getD 0 0 = x0 ∧
      ∀ q, 1 ≤ q → q < N → ∃ pr lb, pr < q ∧ lb < K ∧ E.getD q 0 = step lb (E.getD pr 0) := by
  unfold walkK at h
  rw [andB_eq, andB_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hl, h0⟩, hr⟩ := h
  rw [lenK_eq] at hl
  rw [getK_eq] at h0
  refine ⟨hl, h0, ?_⟩
  cases E with
  | nil => exact nomatch hr
  | cons e0 cs =>
    intro q hq1 hq2
    obtain ⟨pr, lb, _, h2, h3, h4⟩ :=
      runK_spec step K (e0 :: cs) (e0 :: cs) C cs 0 1 rfl rfl hr q hq1 (by omega)
    exact ⟨pr, lb, h2, h3, h4⟩

end CFSG.KC.A6CK
