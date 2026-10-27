module

public import Certificates.Data.Kernel.J4Row.Chk
public import CFSG.Certificates.Kernel.J4NPVerdict.Rep
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Facts

public section

namespace CFSG.KC.J4Row

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KC.Loop CFSG.KC.J4NPV
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4 (RowFactsJ)

theorem neN_ne {a b : Nat} (h : neN a b = true) : a ≠ b := by
  rintro rfl
  unfold neN notB at h
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem allR_mem {α : Type} {f : α → Bool} : ∀ {l : List α}, allR f l = true → ∀ x ∈ l, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    change andB (f y) (allR f l) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allR_mem h2 x hx

theorem memR_iff (x : Nat) : ∀ l : List Nat, memR x l = true ↔ x ∈ l
  | [] => by
    change false = true ↔ _
    simp
  | y :: l => by
    change orB (Nat.beq x y) (memR x l) = true ↔ _
    rw [vj_orB_iff, memR_iff x l, List.mem_cons, Nat.beq_eq]

theorem lenR_eq {α : Type} : ∀ l : List α, lenR l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenR l) = _
    rw [lenR_eq l]
    rfl

theorem getN_getD (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_getD d l i

theorem getLR_eq : ∀ (l : List (List Nat)) (i : Nat), getLR l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getLR_eq l i

theorem allBelowR_lt {f : Nat → Bool} : ∀ {n : Nat}, allBelowR n f = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    change andB (f n) (allBelowR n f) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact allBelowR_lt h2 i hi
    · exact h1

theorem allNeK_not_mem {x : Nat} : ∀ {l : List Nat}, allNeK x l = true → x ∉ l
  | [], _ => List.not_mem_nil
  | y :: l, h => by
    change andB (neN x y) (allNeK x l) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    rw [List.mem_cons, not_or]
    exact ⟨neN_ne h1, allNeK_not_mem h2⟩

theorem distinctK_nodup : ∀ {l : List Nat}, distinctK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    change andB (allNeK x l) (distinctK l) = true at h
    obtain ⟨h1, h2⟩ := vj_andB_iff.1 h
    exact List.nodup_cons.2 ⟨allNeK_not_mem h1, distinctK_nodup h2⟩

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem vjRep_unique {M M' : Nat} {x : J} (h : VjRep M x) (h' : VjRep M' x) : M = M' := by
  obtain ⟨X, hX, rfl, eX⟩ := h
  obtain ⟨Y, hY, rfl, eY⟩ := h'
  have hm : rowsMatrix X = rowsMatrix Y := eX.trans eY.symm
  have e : X = Y := by
    refine Array.ext (by rw [hX.1, hY.1]) fun i h1 h2 => ?_
    have hi : i < 112 := by rw [← hX.1]; exact h1
    have wx : X[i].wf = true := Array.all_eq_true.mp hX.2 i h1
    have wy : Y[i].wf = true := Array.all_eq_true.mp hY.2 i h2
    apply (V2.toVec_inj wx wy).1
    funext j
    have := congrFun (congrFun hm ⟨i, hi⟩) j
    rwa [rowsMatrix_apply, rowsMatrix_apply, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this
  rw [e]

theorem ne_of_vjRep {M M' : Nat} {x y : J} (h : VjRep M x) (h' : VjRep M' y) (hne : neN M M' = true) :
    x ≠ y := by
  rintro rfl
  exact neN_ne hne (vjRep_unique h h')

theorem eq_of_vjRep {M M' : Nat} {x y : J} (h : VjRep M x) (h' : VjRep M' y)
    (he : Nat.beq M M' = true) : x = y :=
  vjRep_eq_of_eq h h' (Nat.eq_of_beq_eq_true he)

theorem vjRep_powJ (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Nat} {x : J}
    (h : VjRep M x) : ∀ e, VjRep (powJ c rm one M e) (x ^ e)
  | 0 => by
    rw [pow_zero]
    exact vjRep_one hK
  | e + 1 => by
    change VjRep (strictN (powJ c rm one M e) fun a => mulJ c rm a M) _
    rw [vj_strictN_eq, pow_succ]
    exact vjRep_mul hK (vjRep_powJ hK h e) h

@[expose] def RegOK (R : List (Nat × Nat)) : Prop := ∀ q ∈ R, ∃ x : J, VjRep q.1 x ∧ VjRep q.2 x⁻¹

theorem getP_mem (one : Nat) :
    ∀ (R : List (Nat × Nat)) (d : Nat), getP one R d = (one, one) ∨ getP one R d ∈ R
  | [], _ => Or.inl rfl
  | _ :: _, 0 => Or.inr List.mem_cons_self
  | [_], _ + 1 => Or.inr List.mem_cons_self
  | p :: q :: qs, d + 1 => by
    change getP one (q :: qs) d = (one, one) ∨ getP one (q :: qs) d ∈ p :: q :: qs
    rcases getP_mem one (q :: qs) d with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem regP_ok (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {R : List (Nat × Nat)}
    (hR : RegOK R) (L i : Nat) :
    ∃ x : J, VjRep (regP one R L i).1 x ∧ VjRep (regP one R L i).2 x⁻¹ := by
  unfold regP
  rcases getP_mem one R (Nat.sub (Nat.sub L (nat_lit 1)) i) with h | h
  · rw [h]
    exact ⟨1, vjRep_one hK, by rw [inv_one]; exact vjRep_one hK⟩
  · exact hR _ h

theorem pushK_ok {x y : Nat} {R : List (Nat × Nat)} {k : List (Nat × Nat) → Bool} {g : J}
    (hR : RegOK R) (hx : VjRep x g) (hy : VjRep y g⁻¹) (h : pushK x y R k = true) :
    ∃ R', RegOK R' ∧ k R' = true := by
  unfold pushK at h
  rw [vj_strictB_eq, vj_strictB_eq] at h
  refine ⟨_, fun q hq => ?_, h⟩
  rcases List.mem_cons.1 hq with rfl | hq
  · exact ⟨g, hx, hy⟩
  · exact hR q hq

theorem stepK_eq (t i j : Nat) (R : List (Nat × Nat)) (L : Nat) (k : List (Nat × Nat) → Bool) :
    stepK c rm one (t, i, j) R L k = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (pushK (powJ c rm one (regP one R L i).1 j) (powJ c rm one (regP one R L i).2 j) R k)
        (pushK (regP one R L i).2 (regP one R L i).1 R k)
        (Nat.beq t (nat_lit 1)))
      (strictB (regP one R L i).1 fun x => strictB (regP one R L i).2 fun xi =>
        strictB (regP one R L j).1 fun y => strictB (regP one R L j).2 fun yi =>
          pushK (mulJ c rm x y) (mulJ c rm yi xi) R k)
      (Nat.beq t (nat_lit 0)) := rfl

theorem stepK_ok (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {ins : Nat × Nat × Nat}
    {R : List (Nat × Nat)} {L : Nat} {k : List (Nat × Nat) → Bool} (hR : RegOK R)
    (h : stepK c rm one ins R L k = true) : ∃ R', RegOK R' ∧ k R' = true := by
  obtain ⟨t, i, j⟩ := ins
  rw [stepK_eq] at h
  obtain ⟨x, hx, hxi⟩ := regP_ok hK hR L i
  generalize Nat.beq t (nat_lit 0) = b0 at h
  generalize Nat.beq t (nat_lit 1) = b1 at h
  cases b0
  · cases b1
    · refine pushK_ok hR (vjRep_powJ hK hx j) ?_ h
      rw [← inv_pow]
      exact vjRep_powJ hK hxi j
    · exact pushK_ok hR hxi (by rw [inv_inv]; exact hx) h
  · obtain ⟨y, hy, hyi⟩ := regP_ok hK hR L j
    simp only [vj_strictB_eq] at h
    refine pushK_ok hR (vjRep_mul hK hx hy) ?_ h
    rw [mul_inv_rev]
    exact vjRep_mul hK hyi hxi

theorem runK_ok (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    {fin : List (Nat × Nat) → Nat → Bool} :
    ∀ (prog : List (Nat × Nat × Nat)) (R : List (Nat × Nat)) (L : Nat), RegOK R →
      runK c rm one fin prog R L = true → ∃ R' L', RegOK R' ∧ fin R' L' = true
  | [], R, L, hR, h => ⟨R, L, hR, h⟩
  | ins :: prog, R, L, hR, h => by
    have h' : stepK c rm one ins R L (fun R' => runK c rm one fin prog R' (Nat.succ L)) = true := h
    obtain ⟨R1, hR1, h1⟩ := stepK_ok hK hR h'
    exact runK_ok hK prog R1 (Nat.succ L) hR1 h1

theorem gensK_ok {R : List (Nat × Nat)} (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    (hR : RegOK R) (L : Nat) :
    ∀ (rs : List Nat) (k : List Nat → Bool), gensK one R L rs k = true →
      ∃ G : List Nat, ∃ gs : List J, List.Forall₂ VjRep G gs ∧ k G = true
  | [], _, h => ⟨[], [], List.Forall₂.nil, h⟩
  | r :: rs, k, h => by
    have h' : strictB (regP one R L r).1 (fun v => gensK one R L rs fun l => k (v :: l)) = true := h
    rw [vj_strictB_eq] at h'
    obtain ⟨G, gs, hG, hk⟩ := gensK_ok hK hR L rs _ h'
    obtain ⟨x, hx, -⟩ := regP_ok hK hR L r
    exact ⟨_, x :: gs, List.Forall₂.cons hx hG, hk⟩

theorem getN_ok (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    ∀ {l : List Nat} {xs : List J}, List.Forall₂ VjRep l xs → ∀ d, ∃ x : J, VjRep (getN one l d) x
  | [], _, _, _ => ⟨1, vjRep_one hK⟩
  | _ :: _, _, List.Forall₂.cons h _, 0 => ⟨_, h⟩
  | _ :: _, _, List.Forall₂.cons _ h, d + 1 => getN_ok hK h d

theorem bfsGo_ok (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {G : List Nat} {gs : List J}
    (hG : List.Forall₂ VjRep G gs) {k : List Nat → Bool} :
    ∀ (bfs : List (Nat × Nat)) (acc : List Nat) (accJ : List J) (L : Nat),
      List.Forall₂ VjRep acc accJ → bfsGo c rm one G bfs k acc L = true →
      ∃ E : List Nat, ∃ EJ : List J, List.Forall₂ VjRep E EJ ∧ k E = true
  | [], acc, accJ, _, hacc, h => ⟨acc, accJ, hacc, h⟩
  | (pa, ge) :: bfs, acc, accJ, L, hacc, h => by
    have h' : strictB (mulJ c rm (getN one acc (Nat.sub (Nat.sub L (nat_lit 1)) pa)) (getN one G ge))
        (fun v => bfsGo c rm one G bfs k (v :: acc) (Nat.succ L)) = true := h
    rw [vj_strictB_eq] at h'
    obtain ⟨x, hx⟩ := getN_ok hK hacc (Nat.sub (Nat.sub L (nat_lit 1)) pa)
    obtain ⟨y, hy⟩ := getN_ok hK hG ge
    exact bfsGo_ok hK hG bfs _ (x * y :: accJ) (Nat.succ L)
      (List.Forall₂.cons (vjRep_mul hK hx hy) hacc) h'

theorem exists_rep_of_mem {E : List Nat} {EJ : List J} (h : List.Forall₂ VjRep E EJ) {e : J}
    (he : e ∈ EJ) : ∃ M ∈ E, VjRep M e := by
  induction h with
  | nil => exact absurd he List.not_mem_nil
  | cons hab _ ih =>
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨M, hM, hMe⟩ := ih he
      exact ⟨M, List.mem_cons_of_mem _ hM, hMe⟩

theorem nodup_of_rep {E : List Nat} {EJ : List J} (h : List.Forall₂ VjRep E EJ) (hE : E.Nodup) :
    EJ.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons M x E' EJ' hMx hrest ih =>
    obtain ⟨hM, hE'⟩ := List.nodup_cons.1 hE
    refine List.nodup_cons.2 ⟨fun hx => ?_, ih hE'⟩
    obtain ⟨M', hM', hM'x⟩ := exists_rep_of_mem hrest hx
    rw [vjRep_unique hMx hM'x] at hM
    exact hM hM'

theorem elK_facts (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Z Zi U N : Nat} {z u : J}
    (hz : VjRep Z z) (hzi : VjRep Zi z⁻¹) (hu : VjRep U u) {E : List Nat} {EJ : List J}
    (hE : List.Forall₂ VjRep E EJ) (h : elK c rm one Z Zi U N E = true) :
    (∀ e ∈ EJ, e * u = u * e) ∧ EJ.Nodup ∧
      (∀ e ∈ EJ, e = 1 ∨ e * e ≠ 1 ∨ e * (z * e * z⁻¹) ≠ z * e * z⁻¹ * e) ∧ EJ.length = N := by
  unfold elK at h
  obtain ⟨hc, h⟩ := vj_andB_iff.1 h
  obtain ⟨hd, h⟩ := vj_andB_iff.1 h
  obtain ⟨hi, hl⟩ := vj_andB_iff.1 h
  refine ⟨fun e he => ?_, nodup_of_rep hE (distinctK_nodup hd), fun e he => ?_, ?_⟩
  · obtain ⟨M, hM, hMe⟩ := exists_rep_of_mem hE he
    exact eq_of_vjRep (vjRep_mul hK hMe hu) (vjRep_mul hK hu hMe) (allR_mem hc M hM)
  · obtain ⟨M, hM, hMe⟩ := exists_rep_of_mem hE he
    have h1 := allR_mem hi M hM
    unfold invK at h1
    rcases vj_orB_iff.1 h1 with h1 | h1
    · exact Or.inl (eq_of_vjRep hMe (vjRep_one hK) h1)
    · rcases vj_orB_iff.1 h1 with h1 | h1
      · exact Or.inr (Or.inl (ne_of_vjRep (vjRep_mul hK hMe hMe) (vjRep_one hK) h1))
      · rw [vj_strictB_eq] at h1
        have hf := vjRep_mul hK (vjRep_mul hK hz hMe) hzi
        exact Or.inr (Or.inr (ne_of_vjRep (vjRep_mul hK hMe hf) (vjRep_mul hK hf hMe) h1))
  · rw [← hE.length_eq, ← lenR_eq]
    exact Nat.eq_of_beq_eq_true hl

theorem zuK_facts (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Us : List Nat}
    (hU : ∀ j < 11, VjRep (getN one Us j) (QT.uJ j))
    (hEta : ∀ m, VjRep (etaK c rm one Us m) (QT.eta QT.uJ 11 m)) {p m n : Nat} {cols : List Nat}
    {Z U Ui : Nat} {z u : J} (hz : VjRep Z z) (hu : VjRep U u) (hui : VjRep Ui u⁻¹)
    (h : zuK c rm one Us p m n cols Z U Ui = true) :
    z ^ p = 1 ∧ z ≠ 1 ∧ u * z * u⁻¹ = z ^ m ∧ u ^ n = 1 ∧ u ^ (n / 2) = QT.eta QT.uJ 11 1 ∧
      ∀ j < 11, u * QT.uJ j * u⁻¹ = QT.eta QT.uJ 11 (getN 0 cols j) := by
  unfold zuK at h
  obtain ⟨h1, h⟩ := vj_andB_iff.1 h
  obtain ⟨h2, h⟩ := vj_andB_iff.1 h
  obtain ⟨h3, h⟩ := vj_andB_iff.1 h
  obtain ⟨h4, h⟩ := vj_andB_iff.1 h
  obtain ⟨h5, h6⟩ := vj_andB_iff.1 h
  refine ⟨eq_of_vjRep (vjRep_powJ hK hz p) (vjRep_one hK) h1, ne_of_vjRep hz (vjRep_one hK) h2,
    eq_of_vjRep (vjRep_mul hK (vjRep_mul hK hu hz) hui) (vjRep_powJ hK hz m) h3,
    eq_of_vjRep (vjRep_powJ hK hu n) (vjRep_one hK) h4,
    eq_of_vjRep (vjRep_powJ hK hu (Nat.div n 2)) (hEta 1) h5, fun j hj => ?_⟩
  exact eq_of_vjRep (vjRep_mul hK (vjRep_mul hK hu (hU j hj)) hui) (hEta _) (allBelowR_lt h6 j hj)

theorem rowChkK_sound (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {Us : List Nat}
    (hU : ∀ j < 11, VjRep (getN one Us j) (QT.uJ j))
    (hEta : ∀ m, VjRep (etaK c rm one Us m) (QT.eta QT.uJ 11 m)) {A Ai B Bi : Nat} {x y : J}
    (hA : VjRep A x) (hAi : VjRep Ai x⁻¹) (hB : VjRep B y) (hBi : VjRep Bi y⁻¹)
    {prog : List (Nat × Nat × Nat)} {p m n rz ru : Nat} {gens cols : List Nat}
    {bfs : List (Nat × Nat)} {N : Nat}
    (h : rowChkK c rm one Us A Ai B Bi prog p m n rz ru gens cols bfs N = true) :
    ∃ z u : J, ∃ L : List J, RowFactsJ p m n (getN 0 cols) N z u L := by
  have h0 : RegOK [(B, Bi), (A, Ai), (one, one)] := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨y, hB, hBi⟩
    · exact ⟨x, hA, hAi⟩
    · exact ⟨1, vjRep_one hK, by rw [inv_one]; exact vjRep_one hK⟩
  obtain ⟨R, L, hR, hf⟩ := runK_ok hK prog _ 3 h0 h
  unfold finK at hf
  simp only [vj_strictB_eq] at hf
  obtain ⟨hzu, hg⟩ := vj_andB_iff.1 hf
  obtain ⟨z, hz, hzi⟩ := regP_ok hK hR L rz
  obtain ⟨u, hu, hui⟩ := regP_ok hK hR L ru
  obtain ⟨G, gs, hG, hb⟩ := gensK_ok hK hR L gens _ hg
  obtain ⟨E, EJ, hE, he⟩ := bfsGo_ok hK hG bfs [one] [1] 1
    (List.Forall₂.cons (vjRep_one hK) List.Forall₂.nil) hb
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := zuK_facts hK hU hEta hz hu hui hzu
  obtain ⟨e1, e2, e3, e4⟩ := elK_facts hK hz hzi hu hE he
  exact ⟨z, u, EJ, ⟨f1, f2, f3, f4, f5, f6, e1, e2, e3, e4⟩⟩

theorem rowsXorK_go (cols : List Nat) (c : Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (getN (nat_lit 0) cols j))
        (bitB c j)) n : Nat) =
      (List.range n).foldl (fun acc j => if c.testBit j then acc ^^^ getN 0 cols j else acc) 0
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← rowsXorK_go cols c n]
    change Bool.rec (motive := fun _ => Nat) _ _ (bitB c n) = _
    rw [bitB_eq]
    cases c.testBit n <;> rfl

theorem rowsXorK_eq (cols : List Nat) (c : Nat) :
    rowsXorK cols c = QT.rowsXor (getN 0 cols) 11 c :=
  rowsXorK_go cols c 11

theorem ceCntK_go (cols : List Nat) : ∀ n : Nat,
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun c acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
        (Nat.beq (rowsXorK cols c) c)) n : Nat) =
      ((Finset.range n).filter fun c => QT.rowsXor (getN 0 cols) 11 c = c).card
  | 0 => rfl
  | n + 1 => by
    have ih := ceCntK_go cols n
    rw [Finset.range_add_one, Finset.filter_insert, ← rowsXorK_eq]
    change Bool.rec (motive := fun _ => Nat) _ _ (Nat.beq (rowsXorK cols n) n) = _
    have hn : n ∉ (Finset.range n).filter fun c => QT.rowsXor (getN 0 cols) 11 c = c := by
      simp
    cases hb : Nat.beq (rowsXorK cols n) n
    · rw [if_neg (Nat.ne_of_beq_eq_false hb), ← ih]
    · rw [if_pos (Nat.eq_of_beq_eq_true hb), Finset.card_insert_of_notMem hn, ← ih]

theorem ceCntK_eq (cols : List Nat) :
    ceCntK cols = ((Finset.range 2048).filter fun c => QT.rowsXor (getN 0 cols) 11 c = c).card :=
  ceCntK_go cols 2048

theorem maskChkK_facts {cols pi : List Nat} {S : List (List Nat)} (h : maskChkK cols pi S = true) :
    (∀ j, getN 0 cols j < 2 ^ 11) ∧
    (∀ i < 24, ∀ c ∈ S.getD i [], QT.rowsXor (getN 0 cols) 11 c ∈ S.getD (getN 0 pi i) []) ∧
    (∀ i < 24, 1 ∈ S.getD i [] → i = 4 ∨ i = 11) ∧ 1 ∈ S.getD 4 [] ∧ 1 ∈ S.getD 11 [] := by
  unfold maskChkK at h
  obtain ⟨h1, h⟩ := vj_andB_iff.1 h
  obtain ⟨h2, h⟩ := vj_andB_iff.1 h
  obtain ⟨h3, h⟩ := vj_andB_iff.1 h
  obtain ⟨h4, h5⟩ := vj_andB_iff.1 h
  refine ⟨fun j => ?_, fun i hi c hc => ?_, fun i hi h1i => ?_, ?_, ?_⟩
  · rw [getN_getD]
    by_cases hj : j < cols.length
    · rw [List.getD_eq_getElem _ _ hj]
      have := allR_mem h1 _ (List.getElem_mem hj)
      simp only [Nat.blt_eq] at this
      exact lt_of_lt_of_eq this (by norm_num)
    · rw [List.getD_eq_default _ _ (by omega)]
      norm_num
  · have := allR_mem (allBelowR_lt h2 i hi) c (by rw [getLR_eq]; exact hc)
    rw [memR_iff, getLR_eq, rowsXorK_eq] at this
    exact this
  · have := allBelowR_lt h3 i hi
    rcases vj_orB_iff.1 this with h | h
    · rw [getLR_eq] at h
      have h' := (memR_iff 1 _).2 h1i
      rw [h'] at h
      exact absurd h (by decide)
    · rcases vj_orB_iff.1 h with h | h
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr (Nat.eq_of_beq_eq_true h)
  · rw [← getLR_eq, ← memR_iff]
    exact h4
  · rw [← getLR_eq, ← memR_iff]
    exact h5

end CFSG.KC.J4Row

end
