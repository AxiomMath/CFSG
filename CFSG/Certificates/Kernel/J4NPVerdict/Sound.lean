module

public import Certificates.Data.Kernel.J4NPVerdict
public import CFSG.Certificates.Kernel.J4Q.RepQT

public section

namespace CFSG.KC.J4NPV

open CFSG.KC.Loop CFSG.KC.J4Q

theorem vj_andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem vj_orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem vj_strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem vj_strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem vj_nilB {l : List Nat} (h : nilB l = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons x l =>
    change false = true at h
    exact absurd h Bool.false_ne_true

theorem prodFrom_eq (c rm : Nat) : ∀ (l : List Nat) (a : Nat),
    prodFrom c rm l a = l.foldl (fun acc x => mulJ c rm acc x) a
  | [], _ => rfl
  | x :: l, a => by
    change strictN (mulJ c rm a x) (prodFrom c rm l) = _
    rw [vj_strictN_eq, prodFrom_eq c rm l]
    rfl

theorem prodK_cons (c rm one x : Nat) (l : List Nat) :
    prodK c rm one (x :: l) = l.foldl (fun acc y => mulJ c rm acc y) x :=
  prodFrom_eq c rm l x

theorem pcSeqGo_eq (e : Nat) : ∀ (L : List (List Nat)) (j : Nat),
    List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
      (fun s _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ j))
        (List.append s (ih (Nat.succ j))) (bitB e j)) L j =
      (List.range L.length).flatMap fun i => if e.testBit (j + i) then L.getD i [] else []
  | [], _ => rfl
  | s :: L, j => by
    change Bool.rec (motive := fun _ => List Nat) _ (List.append s _) (bitB e j) = _
    rw [pcSeqGo_eq e L (j + 1), List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, bitB_eq]
    have hL : ∀ i, (if e.testBit (j + 1 + i) then L.getD i [] else []) =
        (if e.testBit (j + (i + 1)) then (s :: L).getD (i + 1) [] else []) := by
      intro i
      rw [List.getD_cons_succ, show j + 1 + i = j + (i + 1) by omega]
    simp only [Nat.add_zero, List.getD_cons_zero, hL]
    cases e.testBit j <;> rfl

theorem pcSeqK_eq (e : Nat) : pcSeqK e = CFSG.J4Tree.Native.pcSeqT e := by
  unfold pcSeqK CFSG.J4Tree.Native.pcSeqT
  rw [pcSeqGo_eq]
  simp only [Nat.zero_add]
  rfl

theorem coordsC_eq (T : Tabs) : ∀ (ps : List (Nat × Nat)) (k : List Nat → Bool),
    coordsC T ps k = k (ps.map (coordK T))
  | [], _ => rfl
  | p :: ps, k => by
    change strictB (coordK T p) (fun v => coordsC T ps fun vs => k (v :: vs)) = _
    rw [vj_strictB_eq, coordsC_eq T ps]
    rfl

theorem coordOK_spec : ∀ {ps : List (Nat × Nat)}, coordOK ps = true → ∀ p ∈ ps, p.2 < 1024
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: ps, h, p, hp => by
    change andB (Nat.blt q.2 1024) (coordOK ps) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [Nat.blt_eq] at h1
      exact h1
    · exact coordOK_spec h2 p hp

theorem inE_spec : ∀ {ps : List (Nat × Nat)}, inE ps = true → ∀ p ∈ ps, p.2 = 0
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: ps, h, p, hp => by
    change andB (Nat.beq q.2 0) (inE ps) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Nat.eq_of_beq_eq_true h1
    · exact inE_spec h2 p hp

theorem zipPre_spec {f : Nat → Nat → Bool} : ∀ {xs ms : List Nat} {k : List Nat → Bool},
    zipPre f xs ms k = true → xs.length ≤ ms.length ∧
      (∀ i < xs.length, f (xs.getD i 0) (ms.getD i 0) = true) ∧ k (ms.drop xs.length) = true
  | [], ms, k, h => ⟨Nat.zero_le _, fun _ hi => absurd hi (Nat.not_lt_zero _), h⟩
  | x :: xs, [], k, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | x :: xs, m :: ms, k, h => by
    change andB (f x m) (zipPre f xs ms k) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    obtain ⟨a, b, c⟩ := zipPre_spec h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_, by simpa using c⟩
    cases i with
    | zero => simpa using h1
    | succ i =>
      simp only [List.getD_cons_succ]
      exact b i (by simp only [List.length_cons] at hi; omega)

theorem zipChk_spec {f : Nat → Nat → Bool} {xs ms : List Nat} (h : zipPre f xs ms nilB = true) :
    xs.length = ms.length ∧ ∀ i < xs.length, f (xs.getD i 0) (ms.getD i 0) = true := by
  obtain ⟨a, b, c⟩ := zipPre_spec h
  have := List.drop_eq_nil_iff.1 (vj_nilB c)
  exact ⟨by omega, b⟩

theorem getD_drop (l : List Nat) (n i : Nat) : (l.drop n).getD i 0 = l.getD (n + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem normGo_spec {T : Tabs} {Vs : List Nat} {skip : Bool} :
    ∀ {S ms : List Nat} {k : List Nat → Bool}, normGo T Vs skip S k ms = true →
      (∀ s < S.length, ∀ i < Vs.length, skip = true ∨
        normEq T Vs (S.getD s 0) (Vs.getD i 0) (ms.getD (s * Vs.length + i) 0) = true) ∧
      k (ms.drop (S.length * Vs.length)) = true
  | [], ms, k, h => by
    change k ms = true at h
    exact ⟨fun _ hs => absurd hs (Nat.not_lt_zero _), by simpa using h⟩
  | s :: S, ms, k, h => by
    change zipPre (fun v m => orB skip (normEq T Vs s v m)) Vs ms (normGo T Vs skip S k) = true at h
    obtain ⟨_, h2, h3⟩ := zipPre_spec h
    obtain ⟨g2, g3⟩ := normGo_spec h3
    refine ⟨fun t ht i hi => ?_, ?_⟩
    · cases t with
      | zero =>
        have := h2 i hi
        rw [vj_orB_iff] at this
        simpa using this
      | succ t =>
        have := g2 t (by simp only [List.length_cons] at ht; omega) i hi
        rw [getD_drop] at this
        simp only [List.getD_cons_succ]
        have e : Vs.length + (t * Vs.length + i) = (t + 1) * Vs.length + i := by
          rw [Nat.succ_mul]; omega
        rwa [e] at this
    · rw [List.drop_drop] at g3
      have e : Vs.length + S.length * Vs.length = (s :: S).length * Vs.length := by
        simp only [List.length_cons, Nat.succ_mul]; omega
      rwa [e] at g3

theorem npB_spec {T : Tabs} {d : CFSG.J4Tree.VerdictJ.NPData} (h : npB T d = true) :
    (∀ p ∈ CFSG.J4Tree.Native.treeWv d.node, p.2 < 1024) ∧ (∀ p ∈ d.V, p.2 < 1024) ∧
      (CFSG.J4Tree.Native.treeWv d.node).length = d.V.length ∧
      (∀ i < d.V.length,
        mulJ T.c T.rm (((CFSG.J4Tree.Native.treeWv d.node).map (coordK T)).getD i 0) (eltK T d.g) =
          mulJ T.c T.rm (eltK T d.g) ((d.V.map (coordK T)).getD i 0)) ∧
      (∀ s < T.us.length, ∀ i < d.V.length, (∀ p ∈ d.V, p.2 = 0) ∨
        normEq T (d.V.map (coordK T)) (T.us.getD s 0) ((d.V.map (coordK T)).getD i 0)
          (d.masks.getD (s * d.V.length + i) 0) = true) ∧
      (∀ s < T.km.length, ∀ i < d.V.length,
        normEq T (d.V.map (coordK T)) (T.km.getD s 0) ((d.V.map (coordK T)).getD i 0)
          ((d.masks.drop (T.us.length * d.V.length)).getD (s * d.V.length + i) 0) = true) := by
  unfold npB at h
  simp only [vj_strictB_eq, coordsC_eq] at h
  obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
  obtain ⟨h3, h4⟩ := vj_andB_iff.1 h2
  obtain ⟨h5, h6⟩ := vj_andB_iff.1 h4
  obtain ⟨c1, c2⟩ := zipChk_spec h5
  obtain ⟨n1, n2⟩ := normGo_spec h6
  obtain ⟨m1, _⟩ := normGo_spec n2
  simp only [List.length_map] at c1 c2 n1 m1
  refine ⟨coordOK_spec h1, coordOK_spec h3, c1, fun i hi => ?_, fun s hs i hi => ?_,
    fun s hs i hi => (m1 s hs i hi).resolve_left Bool.false_ne_true⟩
  · exact Nat.eq_of_beq_eq_true (c2 i (by omega))
  · rcases n1 s hs i hi with he | he
    · exact Or.inl (inE_spec he)
    · exact Or.inr he

theorem fB_spec {T : Tabs} {d : CFSG.J4Tree.VerdictJ.FData} (h : fB T d = true) :
    (∀ p ∈ CFSG.J4Tree.Native.treeWv d.node, p.2 < 1024) ∧ T.fm.length = d.masks.length ∧
      ∀ j < T.fm.length, normEq T ((CFSG.J4Tree.Native.treeWv d.node).map (coordK T)) (eltK T d.d)
        (T.fm.getD j 0) (d.masks.getD j 0) = true := by
  unfold fB at h
  simp only [vj_strictB_eq, coordsC_eq] at h
  obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
  obtain ⟨c1, c2⟩ := zipChk_spec h2
  exact ⟨coordOK_spec h1, c1, c2⟩

theorem conjB_spec {T : Tabs} {src : List (Nat × Nat)} {d : CFSG.J4Tree.M4.ConjD}
    (h : conjB T src d = true) :
    (∀ p ∈ src, p.2 < 1024) ∧ (∀ p ∈ d.tgt, p.2 < 1024) ∧ src.length = d.fwd.length ∧
      d.tgt.length = d.bwd.length ∧
      (∀ i < src.length, normEq T (d.tgt.map (coordK T)) (wordJ T.c T.rm T.one T.ge T.gei d.word)
        ((src.map (coordK T)).getD i 0) (d.fwd.getD i 0) = true) ∧
      ∀ j < d.tgt.length,
        mulJ T.c T.rm ((d.tgt.map (coordK T)).getD j 0) (wordJ T.c T.rm T.one T.ge T.gei d.word) =
          mulJ T.c T.rm (wordJ T.c T.rm T.one T.ge T.gei d.word)
            (maskK T (src.map (coordK T)) (d.bwd.getD j 0)) := by
  unfold conjB at h
  simp only [vj_strictB_eq, coordsC_eq] at h
  obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
  obtain ⟨h3, h4⟩ := vj_andB_iff.1 h2
  obtain ⟨h5, h6⟩ := vj_andB_iff.1 h4
  obtain ⟨f1, f2⟩ := zipChk_spec h5
  obtain ⟨b1, b2⟩ := zipChk_spec h6
  simp only [List.length_map] at f1 f2 b1 b2
  refine ⟨coordOK_spec h1, coordOK_spec h3, f1, b1, fun i hi => f2 i hi, fun j hj => ?_⟩
  exact Nat.eq_of_beq_eq_true (b2 j hj)

theorem invsK_spec {c rm one pad : Nat} {gs hs : List Nat} (h : invsK c rm one pad gs hs = true) :
    gs.length = hs.length ∧ ∀ i < gs.length,
      canonJ pad (hs.getD i 0) = true ∧ mulJ c rm (gs.getD i 0) (hs.getD i 0) = one := by
  obtain ⟨h1, h2⟩ := zipChk_spec h
  refine ⟨h1, fun i hi => ?_⟩
  obtain ⟨a, b⟩ := vj_andB_iff.1 (h2 i hi)
  exact ⟨a, Nat.eq_of_beq_eq_true b⟩

theorem commK_spec {c rm : Nat} : ∀ {l : List Nat}, commK c rm l = true →
    ∀ x ∈ l, ∀ y ∈ l, mulJ c rm x y = mulJ c rm y x
  | [], _, x, hx, _, _ => absurd hx List.not_mem_nil
  | z :: l, h, x, hx, y, hy => by
    change andB (List.rec (motive := fun _ => Bool) true
      (fun y _ ih' => andB (Nat.beq (mulJ c rm z y) (mulJ c rm y z)) ih') l) (commK c rm l) = true
      at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    have hz : ∀ y ∈ l, mulJ c rm z y = mulJ c rm y z := by
      clear hx hy h h2
      induction l with
      | nil => exact fun y hy => absurd hy List.not_mem_nil
      | cons w l ih =>
        change andB (Nat.beq (mulJ c rm z w) (mulJ c rm w z)) (List.rec (motive := fun _ => Bool)
          true (fun y _ ih' => andB (Nat.beq (mulJ c rm z y) (mulJ c rm y z)) ih') l) = true at h1
        obtain ⟨a, b⟩ := vj_andB_iff.1 h1
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.eq_of_beq_eq_true a
        · exact ih b y hy
    rcases List.mem_cons.1 hx with hx' | hx'
    · rcases List.mem_cons.1 hy with hy' | hy'
      · rw [hx', hy']
      · rw [hx']
        exact hz y hy'
    · rcases List.mem_cons.1 hy with hy' | hy'
      · rw [hy']
        exact (hz x hx').symm
      · exact commK_spec h2 x hx' y hy'

theorem wordsK_spec {c rm one : Nat} {mats invs : List Nat} :
    ∀ {Ms : List Nat} {ws : List (List Int)}, wordsK c rm one mats invs Ms ws = true →
      Ms.length = ws.length ∧ ∀ i < Ms.length, Ms.getD i 0 = wordJ c rm one mats invs (ws.getD i [])
  | [], [], _ => ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h Bool.false_ne_true
  | M :: Ms, w :: ws, h => by
    change andB (Nat.beq M (wordJ c rm one mats invs w)) (wordsK c rm one mats invs Ms ws) = true
      at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    obtain ⟨a, b⟩ := wordsK_spec h2
    refine ⟨by simp [a], fun i hi => ?_⟩
    cases i with
    | zero => exact Nat.eq_of_beq_eq_true h1
    | succ i =>
      simp only [List.getD_cons_succ]
      exact b i (by simp only [List.length_cons] at hi; omega)

end CFSG.KC.J4NPV

end
