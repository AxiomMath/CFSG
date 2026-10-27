module

public import Certificates.Data.Kernel.A9Mod.Defs
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.Sporadic.Th.Recog.A9Mod.Sound

public section

local instance (priority := high) CFSG.KC.A9Mod.instAddCommGroupZMod2KSound :
    AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

namespace CFSG.KC.A9Mod

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24 CFSG.KC.Misc.Spec
open CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.A9Mod

theorem andB_eq (a b : Bool) : CFSG.KC.Ord.andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : CFSG.KC.Ord.orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KC.Ord.notB a = !a := by cases a <;> rfl

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem allP_true {α : Type} {l : List α} {f : α → Bool} (h : allP l f = true) :
    ∀ c ∈ l, f c = true := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have h' : CFSG.KC.Ord.andB (f c) (allP l f) = true := h
    rw [andB_eq, Bool.and_eq_true] at h'
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h'.1
    · exact ih h'.2 x hx

theorem allP_of {α : Type} {l : List α} {f : α → Bool} (h : ∀ c ∈ l, f c = true) :
    allP l f = true := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change CFSG.KC.Ord.andB (f c) (allP l f) = true
    rw [andB_eq, h c List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem natRec_all (P : ℕ → Bool) (n : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true (fun v ih => CFSG.KC.Ord.andB (P v) ih) n = true) :
    ∀ v < n, P v = true := by
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    have h' : CFSG.KC.Ord.andB (P n) (Nat.rec (motive := fun _ => Bool) true (fun v ih => CFSG.KC.Ord.andB (P v) ih) n)
        = true := h
    rw [andB_eq, Bool.and_eq_true] at h'
    intro v hv
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
    · exact ih h'.2 v hv
    · exact h'.1

theorem allV_true {P : ℕ → Bool} (h : allV P = true) : ∀ v < 256, P v = true :=
  natRec_all P 256 h

theorem memN_true {x : ℕ} {l : List ℕ} (h : memN x l = true) : x ∈ l := by
  unfold memN at h
  simp only [letB_eq] at h
  induction l with
  | nil => exact absurd h Bool.false_ne_true
  | cons z l ih =>
    have h' : CFSG.KC.Ord.orB (Nat.beq x z) (List.rec (motive := fun _ => Bool) false
        (fun z _ ih => CFSG.KC.Ord.orB (Nat.beq x z) ih) l) = true := h
    rw [orB_eq, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact List.mem_cons.2 (Or.inl (Nat.eq_of_beq_eq_true h'))
    · exact List.mem_cons_of_mem _ (ih h')

theorem getN_eq (l : List ℕ) (i : ℕ) : getN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getX_eq (gens : List (ℕ × Bool)) (i : ℕ) : getX gens i = (gens.map Prod.fst).getD i 0 := by
  induction gens generalizing i with
  | nil => rfl
  | cons g gens ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_map_of {α : Type} (l : List α) (φ : α → ℕ) (ψ : ℕ → ℕ) (h0 : ψ 0 = 0) (i : ℕ) :
    (l.map (fun a => ψ (φ a))).getD i 0 = ψ ((l.map φ).getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_map]
  cases l[i]? <;> simp [h0]

theorem mem_repsOf {β : Type} {nodes : List (ℕ × β)} {R : ℕ} (h : R ∈ repsOf nodes) :
    ∃ nd ∈ nodes, nd.1 = R := by
  induction nodes with
  | nil => exact absurd h List.not_mem_nil
  | cons nd nodes ih =>
    rcases List.mem_cons.1 h with h | h
    · exact ⟨nd, List.mem_cons_self, h.symm⟩
    · obtain ⟨nd', h1, h2⟩ := ih h
      exact ⟨nd', List.mem_cons_of_mem _ h1, h2⟩

@[expose] def unQ (q : ℕ) : Array ℕ := Array.ofFn (n := 8) fun j => (q >>> (8 * j.val)) &&& 255

@[expose] noncomputable def lin (q : ℕ) : Module.End (ZMod 2) V8 := toLin (unQ q)

theorem getD_unQ (q : ℕ) (j : Fin 8) : (unQ q).getD j 0 = (q >>> (8 * j.val)) &&& 255 := by
  simp [unQ, Array.getD_eq_getD_getElem?]

theorem t255 (i : ℕ) : (255 : ℕ).testBit i = decide (i < 8) := by
  rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]

theorem toLin_unQ (q : ℕ) : lin q = Matrix.toLin' (pkMat 8 q).transpose := by
  unfold lin toLin
  congr 1
  ext i j
  rw [Matrix.of_apply, getD_unQ, Matrix.transpose_apply]
  simp only [pkMat, Matrix.of_apply, bv, Nat.testBit_and, Nat.testBit_shiftRight, t255, i.2,
    decide_true, Bool.and_true]

theorem lin_mulQ (a b : ℕ) : lin (mulQ a b) = lin a * lin b := by
  rw [toLin_unQ, toLin_unQ, toLin_unQ, mulQ, pkMat_mulF2, Matrix.transpose_mul, Matrix.toLin'_mul,
    Module.End.mul_eq_comp]

theorem IDQ_eq : IDQ = oneF2 8 := by decide +kernel

theorem lin_IDQ : lin IDQ = 1 := by
  rw [toLin_unQ, IDQ_eq, pkMat_oneF2, Matrix.transpose_one, Matrix.toLin'_one, Module.End.one_eq_id]

theorem lin_single (q : ℕ) (j : Fin 8) :
    lin q (Pi.single j 1) = bv ((q >>> (8 * j.val)) &&& 255) := by
  change toLin (unQ q) (Pi.single j 1) = _
  rw [toLin_single, getD_unQ]

theorem bv_mvQ (a v : ℕ) : bv (mvQ a v) = lin a (bv v) := by
  have h := lin_single (mulQ a (Nat.land v 255)) 0
  rw [lin_mulQ, Module.End.mul_apply, lin_single] at h
  simp only [Fin.val_zero, mul_zero, Nat.shiftRight_zero, bv_and_255, Nat.land_eq] at h
  simp only [mvQ, Nat.land_eq, bv_and_255]
  exact h.symm

theorem mvQ_lt (a v : ℕ) : mvQ a v < 256 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem lin_powQ (q k : ℕ) : lin (powQ q k) = lin q ^ k := by
  induction k with
  | zero => exact lin_IDQ.trans (pow_zero _).symm
  | succ k ih =>
    change lin (mulQ (powQ q k) q) = _
    rw [lin_mulQ, ih, pow_succ]

theorem mulQ_lt (a b : ℕ) : mulQ a b < 2 ^ 64 := by
  unfold mulQ mulF2
  simp only [letN_eq]
  have hFR : Nat.mul (Nat.sub (Nat.shiftLeft 1 8) 1)
      (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 8)) 1) (Nat.sub (Nat.shiftLeft 1 8) 1)) <
      2 ^ 64 := by decide
  generalize Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 8)) 1) (Nat.sub (Nat.shiftLeft 1 8) 1)
    = R at hFR ⊢
  generalize Nat.sub (Nat.shiftLeft 1 8) 1 = F at hFR ⊢
  suffices ∀ m, Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun k acc => Nat.xor acc (Nat.land
      (Nat.mul (Nat.land (Nat.shiftRight b k) R) F)
      (Nat.mul (Nat.land (Nat.shiftRight a (Nat.mul 8 k)) F) R))) m < 2 ^ 64 from this 8
  intro m
  induction m with
  | zero => exact Nat.two_pow_pos 64
  | succ m ih =>
    exact Nat.xor_lt_two_pow ih (lt_of_le_of_lt Nat.and_le_right
      (lt_of_le_of_lt (Nat.mul_le_mul_right _ Nat.and_le_right) hFR))

theorem IDQ_lt : IDQ < 2 ^ 64 := by decide +kernel

theorem eq_of_lin_eq {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : lin a = lin b) :
    a = b := by
  rw [toLin_unQ, toLin_unQ] at h
  have hm := Matrix.toLin'.injective h
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have := congrFun (congrFun hm ⟨i % 8, Nat.mod_lt _ (by norm_num)⟩) ⟨i / 8, by omega⟩
    simp only [Matrix.transpose_apply, pkMat, Matrix.of_apply, Fin.val_mk] at this
    rw [Nat.div_add_mod i 8] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have h64 : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem evalFrom_lt (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) (w : List ℕ) (r : ℕ) (hr : r < 2 ^ 64) :
    evalFrom a0 a1 a2 a3 b0 b1 b2 b3 w r < 2 ^ 64 := by
  induction w generalizing r with
  | nil => exact hr
  | cons i w ih => exact ih _ (mulQ_lt _ _)

theorem lane_packMap {α : Type} (f : α → ℕ) (cs : List α) (t : ℕ) :
    (packMap f cs >>> (8 * t)) &&& 255 = ((cs.map f).getD t 0) &&& 255 := by
  induction cs generalizing t with
  | nil =>
    change (0 >>> (8 * t)) &&& 255 = _
    simp
  | cons c cs ih =>
    change ((Nat.lor (Nat.land (f c) 255) (Nat.shiftLeft (packMap f cs) 8)) >>> (8 * t)) &&& 255
      = _
    cases t with
    | zero =>
      rw [List.map_cons, List.getD_cons_zero]
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.lor_eq, Nat.land_eq, Nat.shiftLeft_eq', mul_zero, Nat.shiftRight_zero,
        Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, t255]
      by_cases h : i < 8 <;> simp [h]
    | succ t =>
      rw [List.map_cons, List.getD_cons_succ, ← ih t]
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.lor_eq, Nat.land_eq, Nat.shiftLeft_eq', Nat.testBit_and, Nat.testBit_or,
        Nat.testBit_shiftLeft, Nat.testBit_shiftRight, t255]
      by_cases h : i < 8
      · have h1 : 8 * (t + 1) + i ≥ 8 := by omega
        have h2 : 8 * (t + 1) + i - 8 = 8 * t + i := by omega
        have h3 : ¬ 8 * (t + 1) + i < 8 := by omega
        simp [h, h1, h2, h3]
      · simp [h]

theorem enumG_sound (fs : List (ℕ × ℕ)) (φ : ℕ × Bool → ℕ) :
    ∀ (gens : List (ℕ × Bool)) (k : List ℕ → Bool), enumG fs gens k = true →
      (∀ g ∈ gens, φ g < 256 ∧ (g.2 = true → fixV fs (φ g) = true)) → k (gens.map φ) = true := by
  intro gens
  induction gens with
  | nil => exact fun k h _ => h
  | cons g gens ih =>
    intro k h hg
    obtain ⟨x, fx⟩ := g
    change allV (fun v => CFSG.KC.Ord.orB (CFSG.KC.Ord.andB fx (CFSG.KC.Ord.notB (fixV fs v)))
      (enumG fs gens fun vs => k (List.cons v vs))) = true at h
    have hx := hg (x, fx) List.mem_cons_self
    have hv := allV_true h (φ (x, fx)) hx.1
    rw [orB_eq, andB_eq, notB_eq] at hv
    have he : enumG fs gens (fun vs => k (List.cons (φ (x, fx)) vs)) = true := by
      cases fx
      · simpa using hv
      · simpa [hx.2 rfl] using hv
    exact ih _ he fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')

theorem spinOK_sound (A A' : ℕ → ℕ) (f : Module.End (ZMod 2) V8)
    (hA : ∀ j, f * lin (A j) = lin (A' j) * f) (r : SpinRec) (leaf : ℕ → Bool)
    (h : spinOK A A' r leaf = true) : ∃ c, lin c = f ∧ leaf c = true := by
  obtain ⟨gens, cs, fs, Winv⟩ := r
  change CFSG.KC.Ord.andB (colsOK A' cs) (CFSG.KC.Ord.andB (fixOK A A' gens fs)
    (CFSG.KC.Ord.andB (Nat.beq (mulQ (wQ A gens cs) Winv) IDQ)
      (enumG fs gens fun vals => leaf (mulQ (dQ cs vals) Winv)))) = true at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hcols, hfix, hW, henum⟩ := h
  have hW' : mulQ (wQ A gens cs) Winv = IDQ := Nat.eq_of_beq_eq_true hW
  have key : ∀ j x, f (bv (mvQ (A j) x)) = lin (A' j) (f (bv x)) := fun j x => by
    rw [bv_mvQ, ← Module.End.mul_apply, hA, Module.End.mul_apply]
  have hval : ∀ i, bv (getN (gens.map fun g => toNat (f (bv g.1))) i) = f (bv (getX gens i)) := by
    intro i
    have h0 : toNat (f (bv 0)) = 0 := by rw [bv_zero, map_zero]; rfl
    rw [getN_eq, getX_eq, getD_map_of gens Prod.fst (fun x => toNat (f (bv x))) h0]
    exact (bv_toNat _).1
  refine ⟨mulQ (dQ cs (gens.map fun g => toNat (f (bv g.1)))) Winv, ?_, ?_⟩
  · have hD : lin (dQ cs (gens.map fun g => toNat (f (bv g.1)))) = f * lin (wQ A gens cs) := by
      refine ext_single fun t => ?_
      rw [Module.End.mul_apply, lin_single, lin_single]
      unfold dQ wQ
      rw [lane_packMap, lane_packMap, bv_and_255, bv_and_255, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map]
      rcases hct : cs[t.val]? with _ | c
      · simp [bv_zero]
      · obtain ⟨j, M, i⟩ := c
        have hc := allP_true hcols _ (List.mem_of_getElem? hct)
        change Nat.beq (A' j) M = true at hc
        simp only [Option.map_some, Option.getD_some]
        change bv (mvQ M (getN _ i)) = f (bv (mvQ (A j) (getX gens i)))
        rw [← Nat.eq_of_beq_eq_true hc, bv_mvQ, key, hval]
    rw [lin_mulQ, hD, mul_assoc, ← lin_mulQ, hW', lin_IDQ, mul_one]
  · refine enumG_sound fs (fun g => toNat (f (bv g.1))) gens _ henum fun g hg => ⟨(bv_toNat _).2,
      fun hfx => allP_of fun e he => ?_⟩
    obtain ⟨j, M⟩ := e
    have he' := allP_true hfix _ he
    change CFSG.KC.Ord.andB (Nat.beq (A' j) M) (allP gens fun g => Prod.rec (motive := fun _ => Bool)
      (fun x fx => Bool.rec (motive := fun _ => Bool) true
        (Nat.beq (mvQ (A j) x) (Nat.land x 255)) fx) g) = true at he'
    rw [andB_eq, Bool.and_eq_true] at he'
    obtain ⟨hM, hgs⟩ := he'
    have hx := allP_true hgs g hg
    obtain ⟨x, fx⟩ := g
    change fx = true at hfx
    subst hfx
    change Nat.beq (mvQ (A j) x) (Nat.land x 255) = true at hx
    change Nat.beq (mvQ M (toNat (f (bv x)))) (toNat (f (bv x))) = true
    refine Nat.beq_eq_true_eq _ _ ▸ bv_inj (mvQ_lt _ _) (bv_toNat _).2 ?_
    rw [bv_mvQ, (bv_toNat _).1, ← Nat.eq_of_beq_eq_true hM, ← key, Nat.eq_of_beq_eq_true hx,
      Nat.land_eq, bv_and_255]

variable (σ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8)

theorem evalFrom_spec (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) (w : List ℕ)
    (hw : ∀ i ∈ w, lin (sel8 a0 a1 a2 a3 b0 b1 b2 b3 i) = σ (letter i)) (r : ℕ)
    (R : alternatingGroup (Fin 9)) (hr : lin r = σ R) :
    lin (evalFrom a0 a1 a2 a3 b0 b1 b2 b3 w r) = σ (w.foldl (fun r i => r * letter i) R) := by
  induction w generalizing r R with
  | nil => exact hr
  | cons i w ih =>
    exact ih (fun j hj => hw j (List.mem_cons_of_mem _ hj)) _ _
      (by rw [lin_mulQ, hr, hw i List.mem_cons_self, map_mul])

theorem evalWQ_spec (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) (w : List ℕ)
    (hw : ∀ i ∈ w, lin (sel8 a0 a1 a2 a3 b0 b1 b2 b3 i) = σ (letter i)) :
    lin (evalWQ a0 a1 a2 a3 b0 b1 b2 b3 w) = σ (evalA w) :=
  evalFrom_spec σ _ _ _ _ _ _ _ _ w hw IDQ 1 (by rw [lin_IDQ, map_one])

theorem evalWQ_lt (a0 a1 a2 a3 b0 b1 b2 b3 : ℕ) (w : List ℕ) :
    evalWQ a0 a1 a2 a3 b0 b1 b2 b3 w < 2 ^ 64 :=
  evalFrom_lt _ _ _ _ _ _ _ _ w IDQ IDQ_lt

theorem sel8_spec (a0 a1 a2 a3 b0 b1 b2 b3 k : ℕ)
    (h0 : 0 < k → lin a0 = σ eltG ∧ lin b0 = σ eltG⁻¹)
    (h1 : 1 < k → lin a1 = σ eltS₁ ∧ lin b1 = σ eltS₁⁻¹)
    (h2 : 2 < k → lin a2 = σ eltS₂ ∧ lin b2 = σ eltS₂⁻¹)
    (h3 : 3 < k → lin a3 = σ eltS₃ ∧ lin b3 = σ eltS₃⁻¹) (i : ℕ) (hi : i < 8) (hik : i % 4 < k) :
    lin (sel8 a0 a1 a2 a3 b0 b1 b2 b3 i) = σ (letter i) := by
  interval_cases i
  · exact (h0 (by omega)).1
  · exact (h1 (by omega)).1
  · exact (h2 (by omega)).1
  · exact (h3 (by omega)).1
  · exact (h0 (by omega)).2
  · exact (h1 (by omega)).2
  · exact (h2 (by omega)).2
  · exact (h3 (by omega)).2

theorem inv_g {g : ℕ} (h : lin g = σ eltG) : lin g = σ eltG ∧ lin (powQ g 8) = σ eltG⁻¹ :=
  ⟨h, by rw [lin_powQ, h, ← map_pow, eltG_pow_eight]⟩

theorem inv_s1 {s : ℕ} (h : lin s = σ eltS₁) : lin s = σ eltS₁ ∧ lin (powQ s 5) = σ eltS₁⁻¹ :=
  ⟨h, by rw [lin_powQ, h, ← map_pow, eltS₁_pow_five]⟩

theorem inv_s2 {s : ℕ} (h : lin s = σ eltS₂) : lin s = σ eltS₂ ∧ lin s = σ eltS₂⁻¹ :=
  ⟨h, by rw [h, eltS₂_inv]⟩

theorem inv_s3 {s : ℕ} (h : lin s = σ eltS₃) : lin s = σ eltS₃ ∧ lin (powQ s 2) = σ eltS₃⁻¹ :=
  ⟨h, by rw [lin_powQ, h, ← map_pow, eltS₃_sq]⟩

theorem relsQ_true (g s1 s2 s3 k : ℕ) (h0 : 0 < k → lin g = σ eltG)
    (h1 : 1 < k → lin s1 = σ eltS₁) (h2 : 2 < k → lin s2 = σ eltS₂)
    (h3 : 3 < k → lin s3 = σ eltS₃) (rels : List (List ℕ)) (hrel : ∀ r ∈ rels, evalA r = 1)
    (hlet : ∀ r ∈ rels, ∀ i ∈ r, i < 8 ∧ i % 4 < k) : relsQ g s1 s2 s3 rels = true := by
  unfold relsQ
  simp only [letB_eq]
  refine allP_of (f := fun r => Nat.beq (evalWQ g s1 s2 s3 (powQ g 8) (powQ s1 5) s2 (powQ s3 2) r)
    IDQ) fun r hr => Nat.beq_eq_true_eq _ _ ▸ eq_of_lin_eq (evalWQ_lt _ _ _ _ _ _ _ _ _) IDQ_lt ?_
  rw [evalWQ_spec σ _ _ _ _ _ _ _ _ r fun i hi => sel8_spec σ _ _ _ _ _ _ _ _ k
      (fun hk => inv_g σ (h0 hk)) (fun hk => inv_s1 σ (h1 hk)) (fun hk => inv_s2 σ (h2 hk))
      (fun hk => inv_s3 σ (h3 hk)) i (hlet r hr i hi).1 (hlet r hr i hi).2,
    hrel r hr, map_one, lin_IDQ]

theorem relsK1Q_eq : relsK1Q = relsK1 := rfl

theorem relsK2Q_eq : relsK2Q = relsK2 := rfl

theorem relsA9Q_eq : relsA9Q = relsA9 := rfl

theorem wordsLQ_eq : wordsLQ = wordsL := rfl

theorem wordAQ_eq : wordAQ = wordA := rfl

theorem wordBQ_eq : wordBQ = wordB := rfl

theorem wordB'Q_eq : wordB'Q = wordB' := rfl

theorem toLin_eq_lin (m : Array ℕ) (q : ℕ)
    (h : ∀ j : Fin 8, m.getD j 0 = (q >>> (8 * j.val)) &&& 255) : toLin m = lin q :=
  ext_single fun j => by rw [toLin_single, lin_single, h]

theorem lin_N1Q : lin N1Q = toLin N1 :=
  (toLin_eq_lin N1 N1Q fun j => by fin_cases j <;> decide +kernel).symm

theorem lin_N2Q : lin N2Q = toLin N2 :=
  (toLin_eq_lin N2 N2Q fun j => by fin_cases j <;> decide +kernel).symm

theorem lin_B1MQ : lin B1MQ = toLin B1M :=
  (toLin_eq_lin B1M B1MQ fun j => by fin_cases j <;> decide +kernel).symm

theorem lin_B2MQ : lin B2MQ = toLin B2M :=
  (toLin_eq_lin B2M B2MQ fun j => by fin_cases j <;> decide +kernel).symm

theorem lin_P8AQ : lin P8AQ = toLin P8A :=
  (toLin_eq_lin P8A P8AQ fun j => by fin_cases j <;> decide +kernel).symm

theorem lin_P8BQ : lin P8BQ = toLin P8B :=
  (toLin_eq_lin P8B P8BQ fun j => by fin_cases j <;> decide +kernel).symm

@[expose] noncomputable def conjHom (C Ci : Module.End (ZMod 2) V8) (h1 : C * Ci = 1)
    (h2 : Ci * C = 1) : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8 where
  toFun x := C * σ x * Ci
  map_one' := by rw [map_one, mul_one, h1]
  map_mul' x y := by
    rw [map_mul]
    calc C * (σ x * σ y) * Ci = C * σ x * (Ci * C) * σ y * Ci := by
          rw [h2, mul_one]
          simp only [mul_assoc]
      _ = C * σ x * Ci * (C * σ y * Ci) := by simp only [mul_assoc]

theorem conjHom_apply (C Ci : Module.End (ZMod 2) V8) (h1 : C * Ci = 1) (h2 : Ci * C = 1)
    (x : alternatingGroup (Fin 9)) : conjHom σ C Ci h1 h2 x = C * σ x * Ci :=
  rfl

theorem conjToTarget_of_conj (C Ci : ℕ) (h1 : lin C * lin Ci = 1) (h2 : lin Ci * lin C = 1)
    (h : ConjToTarget (conjHom σ (lin C) (lin Ci) h1 h2)) : ConjToTarget σ := by
  obtain ⟨p, hinj, hc⟩ := h
  have key : ∀ (x : alternatingGroup (Fin 9)) (T : Module.End (ZMod 2) V8),
      toLin p * conjHom σ (lin C) (lin Ci) h1 h2 x = T * toLin p →
        toLin (mm p (unQ C)) * σ x = T * toLin (mm p (unQ C)) := by
    intro x T hx
    rw [conjHom_apply] at hx
    rw [toLin_mm, ← Module.End.mul_eq_comp]
    change toLin p * lin C * σ x = T * (toLin p * lin C)
    calc toLin p * lin C * σ x = toLin p * (lin C * σ x * lin Ci) * lin C := by
          simp only [mul_assoc, h2, mul_one]
      _ = T * toLin p * lin C := by rw [hx]
      _ = T * (toLin p * lin C) := mul_assoc _ _ _
  have hinjC : Function.Injective (lin C) := fun x y hxy => by
    have := congrArg (lin Ci) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, h2, Module.End.one_apply,
      Module.End.one_apply] at this
  refine ⟨mm p (unQ C), ?_, ?_⟩
  · rw [toLin_mm, LinearMap.coe_comp]
    exact hinj.comp hinjC
  · rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨key _ _ ha, key _ _ hb⟩
    · exact Or.inr (Or.inl ⟨key _ _ ha, key _ _ hb⟩)
    · exact Or.inr (Or.inr ⟨key _ _ ha, key _ _ hb⟩)

theorem conjQ_sound (N R m2 m3 t P Pi : ℕ) (h : conjQ N R m2 m3 t P Pi = true)
    (hg : lin N = σ eltG) (h1 : lin R = σ eltS₁) (h2 : lin m2 = σ eltS₂) (h3 : lin m3 = σ eltS₃) :
    ConjToTarget σ := by
  unfold conjQ at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨ha, hb, hinv⟩ := h
  have hw : ∀ w : List ℕ, (∀ i ∈ w, i < 8 ∧ i % 4 < 4) →
      lin (evalWQ N R m2 m3 (powQ N 8) (powQ R 5) m2 (powQ m3 2) w) = σ (evalA w) :=
    fun w hw => evalWQ_spec σ _ _ _ _ _ _ _ _ w fun i hi => sel8_spec σ _ _ _ _ _ _ _ _ 4
      (fun _ => inv_g σ hg) (fun _ => inv_s1 σ h1) (fun _ => inv_s2 σ h2) (fun _ => inv_s3 σ h3) i
      (hw i hi).1 (hw i hi).2
  have hPi : lin Pi * lin P = 1 := by rw [← lin_mulQ, Nat.eq_of_beq_eq_true hinv, lin_IDQ]
  have hinj : Function.Injective (lin P) := fun x y hxy => by
    have := congrArg (lin Pi) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hPi, Module.End.one_apply,
      Module.End.one_apply] at this
  have eA := congrArg lin (Nat.eq_of_beq_eq_true ha)
  have eB := congrArg lin (Nat.eq_of_beq_eq_true hb)
  rw [lin_mulQ, lin_mulQ, wordAQ_eq, hw _ wordA_letters] at eA
  rw [lin_mulQ, lin_mulQ] at eB
  refine ⟨unQ P, hinj, ?_⟩
  rcases Bool.eq_false_or_eq_true (Nat.beq t 2) with ht2 | ht2
  · have ht : t = 2 := Nat.eq_of_beq_eq_true ht2
    subst ht
    have e21 : Nat.beq 2 1 = false := rfl
    simp only [ht2, e21, wordBQ_eq] at eA eB
    rw [hw _ wordB_letters] at eB
    exact Or.inr (Or.inr ⟨by rw [← lin_P8AQ]; exact eA, by rw [← lin_P8BQ]; exact eB⟩)
  · simp only [ht2] at eA eB
    rcases Bool.eq_false_or_eq_true (Nat.beq t 1) with ht1 | ht1
    · simp only [ht1, wordB'Q_eq] at eB
      rw [hw _ wordB'_letters] at eB
      exact Or.inr (Or.inl ⟨by rw [← lin_B1MQ]; exact eA, by rw [← lin_B2MQ]; exact eB⟩)
    · simp only [ht1, wordBQ_eq] at eB
      rw [hw _ wordB_letters] at eB
      exact Or.inl ⟨by rw [← lin_B1MQ]; exact eA, by rw [← lin_B2MQ]; exact eB⟩

theorem witMatch_sound (N R m2 : ℕ) (wits : List WitRec) (m : ℕ)
    (h : witMatch N R m2 wits m = true) :
    ∃ e ∈ wits, m = e.1 ∧ conjQ N R m2 e.1 e.2.1 e.2.2.1 e.2.2.2 = true := by
  induction wits with
  | nil => exact absurd h Bool.false_ne_true
  | cons e wits ih =>
    obtain ⟨m3, t, P, Pi⟩ := e
    change Bool.rec (motive := fun _ => Bool) (witMatch N R m2 wits m) (conjQ N R m2 m3 t P Pi)
      (Nat.beq m m3) = true at h
    rcases Bool.eq_false_or_eq_true (Nat.beq m m3) with hb | hb
    · rw [hb] at h
      exact ⟨_, List.mem_cons_self, Nat.eq_of_beq_eq_true hb, h⟩
    · rw [hb] at h
      obtain ⟨e', h1, h2⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩

theorem getL_cases (j : ℕ) : getL j ∈ wordsL ∨ getL j = ([], []) := by
  rw [← wordsLQ_eq]
  unfold getL
  generalize wordsLQ = l
  induction l generalizing j with
  | nil => exact Or.inr rfl
  | cons x l ih =>
    cases j with
    | zero => exact Or.inl List.mem_cons_self
    | succ j =>
      rcases ih j with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem s3OK_sound (N R m2 : ℕ) (sr : SpinRec) (wits : List WitRec)
    (h : s3OK N R m2 sr wits = true) (hg : lin N = σ eltG) (h1 : lin R = σ eltS₁)
    (h2 : lin m2 = σ eltS₂) : ConjToTarget σ := by
  unfold s3OK at h
  simp only [letB_eq] at h
  have hw : ∀ w : List ℕ, (∀ i ∈ w, i < 8 ∧ i % 4 < 3) →
      lin (evalWQ N R m2 IDQ (powQ N 8) (powQ R 5) m2 IDQ w) = σ (evalA w) :=
    fun w hw => evalWQ_spec σ _ _ _ _ _ _ _ _ w fun i hi => sel8_spec σ _ _ _ _ _ _ _ _ 3
      (fun _ => inv_g σ hg) (fun _ => inv_s1 σ h1) (fun _ => inv_s2 σ h2) (fun hk => by omega) i
      (hw i hi).1 (hw i hi).2
  have hA : ∀ j, σ eltS₃ * lin (evalWQ N R m2 IDQ (powQ N 8) (powQ R 5) m2 IDQ
      (Prod.rec (motive := fun _ => List ℕ) (fun w _ => w) (getL j))) =
      lin (evalWQ N R m2 IDQ (powQ N 8) (powQ R 5) m2 IDQ
        (Prod.rec (motive := fun _ => List ℕ) (fun _ w => w) (getL j))) * σ eltS₃ := by
    intro j
    rcases getL_cases j with hj | hj
    · generalize getL j = p at hj
      obtain ⟨u, v⟩ := p
      have hl := wordsL_letters _ hj
      change σ eltS₃ * lin (evalWQ N R m2 IDQ (powQ N 8) (powQ R 5) m2 IDQ u) =
        lin (evalWQ N R m2 IDQ (powQ N 8) (powQ R 5) m2 IDQ v) * σ eltS₃
      rw [hw u hl.1, hw v hl.2, ← wordsL_spec _ hj, ← map_mul, ← map_mul, inv_mul_cancel_right]
    · rw [hj]
      change σ eltS₃ * lin IDQ = lin IDQ * σ eltS₃
      rw [lin_IDQ, mul_one, one_mul]
  obtain ⟨c, hc, hleaf⟩ := spinOK_sound _ _ (σ eltS₃) hA sr _ h
  rw [orB_eq, notB_eq, relsQ_true σ N R m2 c 4 (fun _ => hg) (fun _ => h1) (fun _ => h2)
    (fun _ => hc) relsA9Q (relsA9Q_eq ▸ relsA9_spec) (relsA9Q_eq ▸ relsA9_letters)] at hleaf
  obtain ⟨⟨m3, t, P, Pi⟩, -, hm, hconj⟩ := witMatch_sound N R m2 wits c (by simpa using hleaf)
  subst hm
  exact conjQ_sound σ N R m2 c t P Pi hconj hg h1 h2 hc

theorem memS_sound (subs : List SubRec) (m : ℕ) (h : memS subs m = true) :
    ∃ e ∈ subs, m = e.1 := by
  induction subs with
  | nil => exact absurd h Bool.false_ne_true
  | cons e subs ih =>
    change CFSG.KC.Ord.orB (Prod.rec (motive := fun _ => Bool) (fun m2 _ => Nat.beq m m2) e) (memS subs m)
      = true at h
    rw [orB_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨m2, x⟩ := e
      exact ⟨_, List.mem_cons_self, Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨e', h1, h2⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩

theorem nodeOK_sound (N : ℕ) (nd : NodeRec) (h : nodeOK N nd = true) (hg : lin N = σ eltG)
    (h1 : lin nd.1 = σ eltS₁) : ConjToTarget σ := by
  obtain ⟨R, sr, subs⟩ := nd
  change lin R = σ eltS₁ at h1
  unfold nodeOK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true] at h
  obtain ⟨hs, hsubs⟩ := h
  have hH : lin (evalWQ N R IDQ IDQ (powQ N 8) (powQ R 5) IDQ IDQ wordHQ) = σ (evalA wordH) :=
    evalWQ_spec σ _ _ _ _ _ _ _ _ _ fun i hi => sel8_spec σ _ _ _ _ _ _ _ _ 2
      (fun _ => inv_g σ hg) (fun _ => inv_s1 σ h1) (fun hk => by omega) (fun hk => by omega) i
      (wordH_letters i hi).1 (wordH_letters i hi).2
  have hA : ∀ j, σ eltS₂ * lin (powQ N j) =
      lin (powQ (evalWQ N R IDQ IDQ (powQ N 8) (powQ R 5) IDQ IDQ wordHQ) j) * σ eltS₂ := by
    intro j
    rw [lin_powQ, lin_powQ, hg, hH]
    refine SemiconjBy.pow_right ?_ j
    change σ eltS₂ * σ eltG = σ (evalA wordH) * σ eltS₂
    rw [← wordH_spec, ← map_mul, ← map_mul, inv_mul_cancel_right]
  obtain ⟨c, hc, hleaf⟩ := spinOK_sound _ _ (σ eltS₂) hA sr _ hs
  rw [orB_eq, notB_eq, relsQ_true σ N R c IDQ 3 (fun _ => hg) (fun _ => h1) (fun _ => hc)
    (fun hk => by omega) relsK2Q (relsK2Q_eq ▸ relsK2_spec) (relsK2Q_eq ▸ relsK2_letters)]
    at hleaf
  obtain ⟨⟨m2, sr3, wits⟩, he, hm⟩ := memS_sound subs c (by simpa using hleaf)
  subst hm
  have := allP_true hsubs _ he
  exact s3OK_sound σ N R c sr3 wits this hg h1 hc

theorem s1Match_sound (N : ℕ) (recs : List S1Rec) (reps : List ℕ) (m : ℕ)
    (h : s1Match N recs reps m = true) :
    ∃ e ∈ recs, m = e.1 ∧ mulQ e.2.1 N = mulQ N e.2.1 ∧ mulQ e.2.1 e.2.2.1 = IDQ ∧
      mulQ e.2.2.1 e.2.1 = IDQ ∧ mulQ e.2.1 e.1 = mulQ e.2.2.2 e.2.1 ∧ e.2.2.2 ∈ reps := by
  induction recs with
  | nil => exact absurd h Bool.false_ne_true
  | cons e recs ih =>
    obtain ⟨m1, C, Ci, R⟩ := e
    change Bool.rec (motive := fun _ => Bool) (s1Match N recs reps m)
      (CFSG.KC.Ord.andB (Nat.beq (mulQ C N) (mulQ N C)) (CFSG.KC.Ord.andB (Nat.beq (mulQ C Ci) IDQ)
        (CFSG.KC.Ord.andB (Nat.beq (mulQ Ci C) IDQ) (CFSG.KC.Ord.andB (Nat.beq (mulQ C m1) (mulQ R C))
          (memN R reps))))) (Nat.beq m m1) = true at h
    rcases Bool.eq_false_or_eq_true (Nat.beq m m1) with hb | hb
    · rw [hb] at h
      simp only [andB_eq, Bool.and_eq_true] at h
      obtain ⟨e1, e2, e3, e4, e5⟩ := h
      exact ⟨_, List.mem_cons_self, Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true e1,
        Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3, Nat.eq_of_beq_eq_true e4,
        memN_true e5⟩
    · rw [hb] at h
      obtain ⟨e', h1, h2⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩

theorem s1OK_sound (N : ℕ) (sr : SpinRec) (recs : List S1Rec) (reps : List ℕ)
    (h : s1OK N sr recs reps = true)
    (hreps : ∀ R ∈ reps, ∀ τ : alternatingGroup (Fin 9) →* Module.End (ZMod 2) V8,
      lin N = τ eltG → lin R = τ eltS₁ → ConjToTarget τ)
    (hg : lin N = σ eltG) : ConjToTarget σ := by
  unfold s1OK at h
  simp only [letB_eq] at h
  have hA : ∀ j, σ eltS₁ * lin (powQ N j) = lin (powQ (mulQ N N) j) * σ eltS₁ := by
    intro j
    rw [lin_powQ, lin_powQ, lin_mulQ, hg]
    refine SemiconjBy.pow_right ?_ j
    change σ eltS₁ * σ eltG = σ eltG * σ eltG * σ eltS₁
    calc σ eltS₁ * σ eltG = σ (eltS₁ * eltG * eltS₁⁻¹ * eltS₁) := by
          rw [inv_mul_cancel_right, map_mul]
      _ = σ eltG * σ eltG * σ eltS₁ := by rw [eltS₁_conj, map_mul, map_mul]
  obtain ⟨c, hc, hleaf⟩ := spinOK_sound _ _ (σ eltS₁) hA sr _ h
  rw [orB_eq, notB_eq, relsQ_true σ N c IDQ IDQ 2 (fun _ => hg) (fun _ => hc) (fun hk => by omega)
    (fun hk => by omega) relsK1Q (relsK1Q_eq ▸ relsK1_spec) (relsK1Q_eq ▸ relsK1_letters)]
    at hleaf
  obtain ⟨⟨m1, C, Ci, R⟩, -, hm, e1, e2, e3, e4, hR⟩ := s1Match_sound N recs reps c
    (by simpa using hleaf)
  subst hm
  have hC1 : lin C * lin Ci = 1 := by rw [← lin_mulQ, e2, lin_IDQ]
  have hC2 : lin Ci * lin C = 1 := by rw [← lin_mulQ, e3, lin_IDQ]
  have l1 := congrArg lin e1
  have l4 := congrArg lin e4
  rw [lin_mulQ, lin_mulQ] at l1 l4
  refine conjToTarget_of_conj σ C Ci hC1 hC2 (hreps R hR _ ?_ ?_)
  · rw [conjHom_apply, ← hg, l1, mul_assoc, hC1, mul_one]
  · rw [conjHom_apply, ← hc, l4, mul_assoc, hC1, mul_one]

end CFSG.KC.A9Mod
