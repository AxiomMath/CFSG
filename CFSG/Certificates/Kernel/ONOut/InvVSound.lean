module

public import CFSG.Certificates.Kernel.ONOut.RowsSound

public section

namespace CFSG.KS.ONOut.InvV

open CFSG.F3.Native CFSG.Sporadic.ON.Native CFSG.KS.ONOut Matrix

theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

@[expose] def pivStep (d c : ℕ) (A : Array V) (piv r : ℕ) : ℕ :=
  if (piv == d && A[r]!.get c != 0) = true then r else piv

@[expose] def pivF (d c : ℕ) (A : Array V) : ℕ := (List.range' c (d - c)).foldl (pivStep d c A) d

@[expose] def elimStep (c : ℕ) (rc : V) (A3 : Array V) (r : ℕ) : Array V :=
  if (r != c) = true then
    (if (A3[r]!.get c == 1) = true then A3.set! r (A3[r]!.sub rc)
     else if (A3[r]!.get c == 2) = true then A3.set! r (A3[r]!.add rc) else A3) else A3

@[expose] def elimF (d c : ℕ) (A2 : Array V) : Array V :=
  (List.range' 0 d).foldl (elimStep c A2[c]!) A2

@[expose] def swapF (A : Array V) (p c : ℕ) : Array V := (A.set! p A[c]!).set! c A[p]!

theorem gj_eq (d c : ℕ) (A : Array V) : gjStep d A c =
    if pivF d c A < d then
      (if ((swapF A (pivF d c A) c)[c]!.get c == 2) = true then
        elimF d c ((swapF A (pivF d c A) c).set! c (swapF A (pivF d c A) c)[c]!.neg)
      else elimF d c (swapF A (pivF d c A) c))
    else A := by
  unfold gjStep pivF pivStep elimF elimStep swapF
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range', ite_pure_yield,
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one]
  split <;> (try split) <;> rfl

@[expose] def augF (d : ℕ) (X : Array V) : Array V :=
  Array.ofFn (n := d) fun i => (⟨X[i.val]!.p ||| (1 <<< (d + i.val)), X[i.val]!.m⟩ : V)

@[expose] def rightF (d : ℕ) (r : V) : V := ⟨r.p >>> d, r.m >>> d⟩

theorem invV_eq (d : ℕ) (X : Array V) : invV d X =
    ((List.range' 0 d).foldl (fun A c => gjStep d A c) (augF d X)).map (rightF d) := by
  unfold invV augF rightF
  simp only [Id.run_bind, Id.run_pure, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure, Std.Legacy.Range.size, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

theorem get_cases (a : V) (j : ℕ) : (a.get j = 0 ∧ a.val j = 0) ∨ (a.get j = 1 ∧ a.val j = 1) ∨
    (a.get j = 2 ∧ a.val j = 2) := by
  unfold V.val
  have := get_lt a j
  interval_cases h : a.get j <;> simp

@[expose] def Lm (d : ℕ) (A : Array V) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  Matrix.of fun i j => A[i.val]!.val j.val

@[expose] def Rm (d : ℕ) (A : Array V) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  Matrix.of fun i j => A[i.val]!.val (d + j.val)

structure Aug (d c : ℕ) (Xm : Matrix (Fin d) (Fin d) (ZMod 3)) (A : Array V) : Prop where
  size : A.size = d
  rows : ∀ i : ℕ, RowC (2 * d) A[i]!
  eqn : Lm d A = Rm d A * Xm
  det : (Lm d A).det ≠ 0
  unit : ∀ i j : Fin d, j.val < c → Lm d A i j = if i = j then 1 else 0

theorem perm_rows {d : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A B : Array V}
    (hA : Lm d A = Rm d A * Xm) (σ : Equiv.Perm (Fin d))
    (hB : ∀ i : Fin d, B[i.val]! = A[(σ i).val]!) :
    Lm d B = (Lm d A).submatrix σ id ∧ Rm d B = (Rm d A).submatrix σ id ∧
      Lm d B = Rm d B * Xm := by
  have h1 : Lm d B = (Lm d A).submatrix σ id := by
    ext i j
    simp [Lm, hB]
  have h2 : Rm d B = (Rm d A).submatrix σ id := by
    ext i j
    simp [Rm, hB]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, hA]
  ext i j
  simp [Matrix.mul_apply]

theorem update_rows {d : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A B : Array V}
    (hA : Lm d A = Rm d A * Xm) (r : Fin d) (u v : Fin d → ZMod 3) (s : ZMod 3) (c : Fin d)
    (hu : ∀ j : Fin d, B[r.val]!.val j.val = A[r.val]!.val j.val + s * A[c.val]!.val j.val)
    (hv : ∀ j : Fin d, B[r.val]!.val (d + j.val) = A[r.val]!.val (d + j.val) +
      s * A[c.val]!.val (d + j.val))
    (hB : ∀ i : Fin d, i ≠ r → B[i.val]! = A[i.val]!) (hu' : u = Lm d A r + s • Lm d A c)
    (hv' : v = Rm d A r + s • Rm d A c) :
    Lm d B = (Lm d A).updateRow r u ∧ Lm d B = Rm d B * Xm := by
  have h1 : Lm d B = (Lm d A).updateRow r u := by
    ext i j
    by_cases hi : i = r
    · subst hi
      simp [Lm, hu, hu']
    · simp [Lm, hB i hi, Matrix.updateRow_ne hi]
  have h2 : Rm d B = (Rm d A).updateRow r v := by
    ext i j
    by_cases hi : i = r
    · subst hi
      simp [Rm, hv, hv']
    · simp [Rm, hB i hi, Matrix.updateRow_ne hi]
  refine ⟨h1, ?_⟩
  rw [h1, h2]
  ext i j
  by_cases hi : i = r
  · subst hi
    have e := congrFun (congrFun hA i) j
    have e2 := congrFun (congrFun hA c) j
    simp only [Matrix.updateRow_self, hu', hv', Matrix.mul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e e2 ⊢
    rw [e, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [Matrix.updateRow_ne hi]
    rw [hA]
    simp [Matrix.mul_apply, Matrix.updateRow_ne hi]

theorem det_perm_ne {d : ℕ} {L : Matrix (Fin d) (Fin d) (ZMod 3)} (σ : Equiv.Perm (Fin d))
    (h : L.det ≠ 0) : (L.submatrix σ id).det ≠ 0 := by
  rw [Matrix.det_permute]
  intro h0
  apply h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] at h0
  · simpa using h0
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h0
    exact neg_eq_zero.1 h0

theorem det_double_ne {d : ℕ} {L : Matrix (Fin d) (Fin d) (ZMod 3)} (r : Fin d) (h : L.det ≠ 0) :
    (L.updateRow r (L r + (1 : ZMod 3) • L r)).det ≠ 0 := by
  have e : L r + (1 : ZMod 3) • L r = (2 : ZMod 3) • L r := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  intro h0
  apply h
  rcases mul_eq_zero.1 h0 with h2 | h2
  · exact absurd h2 (by decide)
  · exact h2

theorem pivot_exists {d c : ℕ} {L : Matrix (Fin d) (Fin d) (ZMod 3)} (hdet : L.det ≠ 0)
    (hc : c < d) (hu : ∀ i j : Fin d, j.val < c → L i j = if i = j then 1 else 0) :
    ∃ r : Fin d, c ≤ r.val ∧ L r ⟨c, hc⟩ ≠ 0 := by
  by_contra hne
  push Not at hne
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun k => if k.val = c then 1 else if k.val < c then -L k ⟨c, hc⟩ else 0, fun hv => ?_, ?_⟩
  · have := congrFun hv ⟨c, hc⟩
    simp at this
  · funext i
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
    have key : ∀ k : Fin d,
        L i k * (if k.val = c then 1 else if k.val < c then -L k ⟨c, hc⟩ else 0) =
          (if k = ⟨c, hc⟩ then L i ⟨c, hc⟩ else 0) +
            (if k = i then (if i.val < c then -L i ⟨c, hc⟩ else 0) else 0) := by
      intro k
      by_cases h1 : k.val = c
      · have e : k = ⟨c, hc⟩ := Fin.ext h1
        subst e
        by_cases hci : (⟨c, hc⟩ : Fin d) = i
        · subst hci
          simp
        · simp [hci]
      · have hk : k ≠ ⟨c, hc⟩ := fun e => h1 (by rw [e])
        rw [if_neg h1, if_neg hk, zero_add]
        by_cases h2 : k.val < c
        · rw [if_pos h2, hu i k h2]
          by_cases hik : i = k
          · subst hik
            simp [h2]
          · rw [if_neg hik, if_neg (Ne.symm hik), zero_mul]
        · rw [if_neg h2, mul_zero]
          by_cases hik : k = i
          · subst hik
            rw [if_pos rfl, if_neg h2]
          · rw [if_neg hik]
    rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    by_cases hi : i.val < c
    · rw [if_pos hi]
      exact add_neg_cancel _
    · rw [if_neg hi, hne i (by omega), add_zero]

theorem piv_aux (A : Array V) (c d : ℕ) : ∀ m s p, c ≤ s → s + m ≤ d →
    (p = d ∨ (c ≤ p ∧ p < d ∧ A[p]!.get c ≠ 0)) →
    (((List.range' s m).foldl (pivStep d c A) p = d ∨
      (c ≤ (List.range' s m).foldl (pivStep d c A) p ∧
        (List.range' s m).foldl (pivStep d c A) p < d ∧
        A[(List.range' s m).foldl (pivStep d c A) p]!.get c ≠ 0)) ∧
      ((List.range' s m).foldl (pivStep d c A) p = d →
        p = d ∧ ∀ r, s ≤ r → r < s + m → A[r]!.get c = 0)) := by
  intro m
  induction m with
  | zero =>
    intro s p _ _ hp
    simp only [List.range'_zero, List.foldl_nil]
    exact ⟨hp, fun h => ⟨h, fun r h1 h2 => by omega⟩⟩
  | succ m ih =>
    intro s p hs hm hp
    rw [List.range'_succ, List.foldl_cons]
    unfold pivStep
    by_cases hc : (p == d && A[s]!.get c != 0) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
      obtain ⟨-, hnz⟩ := hc
      obtain ⟨h1, h2⟩ := ih (s + 1) s (by omega) (by omega) (Or.inr ⟨hs, by omega, hnz⟩)
      refine ⟨h1, fun h => ?_⟩
      obtain ⟨e, -⟩ := h2 h
      omega
    · rw [if_neg hc]
      obtain ⟨h1, h2⟩ := ih (s + 1) p (by omega) (by omega) hp
      refine ⟨h1, fun h => ?_⟩
      obtain ⟨e, hr⟩ := h2 h
      refine ⟨e, fun r hr1 hr2 => ?_⟩
      by_cases hrs : r = s
      · subst hrs
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_and, not_not] at hc
        exact hc e
      · exact hr r (by omega) (by omega)

theorem pivF_spec {A : Array V} {c d : ℕ} (hc : c < d)
    (h : ∃ r, c ≤ r ∧ r < d ∧ A[r]!.get c ≠ 0) :
    c ≤ pivF d c A ∧ pivF d c A < d ∧ A[pivF d c A]!.get c ≠ 0 := by
  obtain ⟨h1, h2⟩ := piv_aux A c d (d - c) c d (Nat.le_refl c) (by omega) (Or.inl rfl)
  unfold pivF
  rcases h1 with h1 | h1
  · obtain ⟨-, hz⟩ := h2 h1
    obtain ⟨r, hr1, hr2, hr3⟩ := h
    exact absurd (hz r hr1 (by omega)) hr3
  · exact h1

theorem swap_get {A : Array V} {p c : ℕ} (hp : p < A.size) (hc : c < A.size) (i : ℕ) :
    (swapF A p c)[i]! = if i = c then A[p]! else if i = p then A[c]! else A[i]! := by
  unfold swapF
  by_cases h1 : i = c
  · subst h1
    rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!]; exact hc), if_pos rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm h1), if_neg h1]
    by_cases h2 : i = p
    · subst h2
      rw [Array.getElem!_set!_self _ _ _ hp, if_pos rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm h2), if_neg h2]

theorem ite_iff_congr {α : Type} {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) (a b : α) :
    (if P then a else b) = if Q then a else b := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

theorem swap_aug {d c p : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A : Array V}
    (h : Aug d c Xm A) (hc : c < d) (hcp : c ≤ p) (hp : p < d) :
    Aug d c Xm (swapF A p c) ∧ (swapF A p c)[c]! = A[p]! := by
  have hs := h.size
  have hget := swap_get (A := A) (p := p) (c := c) (by omega) (by omega)
  have hσ : ∀ i : Fin d, (swapF A p c)[i.val]! =
      A[((Equiv.swap (⟨c, hc⟩ : Fin d) ⟨p, hp⟩) i).val]! := by
    intro i
    rw [hget, Equiv.swap_apply_def]
    by_cases h1 : i = ⟨c, hc⟩
    · subst h1
      simp
    · have h1' : i.val ≠ c := fun e => h1 (Fin.ext e)
      by_cases h2 : i = ⟨p, hp⟩
      · subst h2
        simp only [h1', h1, if_false, if_true]
      · have h2' : i.val ≠ p := fun e => h2 (Fin.ext e)
        rw [if_neg h1', if_neg h2', if_neg h1, if_neg h2]
  obtain ⟨e1, -, e3⟩ := perm_rows h.eqn _ hσ
  refine ⟨⟨by simp [swapF, hs], fun i => ?_, e3, ?_, fun i j hj => ?_⟩, by rw [hget, if_pos rfl]⟩
  · rw [hget]
    split_ifs <;> exact h.rows _
  · rw [e1]
    exact det_perm_ne _ h.det
  · rw [e1, Matrix.submatrix_apply, id, h.unit _ j hj]
    have hj1 : j ≠ ⟨c, hc⟩ := fun e => by rw [e] at hj; exact lt_irrefl _ hj
    have hj2 : j ≠ ⟨p, hp⟩ := fun e => by rw [e] at hj; simp at hj; omega
    have hfix : Equiv.swap (⟨c, hc⟩ : Fin d) ⟨p, hp⟩ j = j :=
      Equiv.swap_apply_of_ne_of_ne hj1 hj2
    apply ite_iff_congr
    constructor
    · intro e
      rw [← hfix] at e
      exact (Equiv.swap _ _).injective e
    · intro e
      rw [e, hfix]

theorem neg_val_two {a : V} (ha : a.wf = true) (j : ℕ) (h : a.val j = 2) : a.neg.val j = 1 := by
  rw [V.val_neg a j ha, h]
  decide

theorem neg_aug {d c : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A : Array V}
    (h : Aug d c Xm A) (hc : c < d) (h2 : A[c]!.val c = 2) :
    Aug d c Xm (A.set! c A[c]!.neg) ∧ (A.set! c A[c]!.neg)[c]!.val c = 1 := by
  have hs := h.size
  have hself : (A.set! c A[c]!.neg)[c]! = A[c]!.neg :=
    Array.getElem!_set!_self _ _ _ (by omega)
  have hne : ∀ i : ℕ, i ≠ c → (A.set! c A[c]!.neg)[i]! = A[i]! := fun i hi =>
    Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi)
  have hw := (h.rows c).1
  have hneg : ∀ k : ℕ, (A.set! c A[c]!.neg)[c]!.val k = A[c]!.val k + 1 * A[c]!.val k := by
    intro k
    rw [hself, V.val_neg _ _ hw]
    have : ∀ x : ZMod 3, -x = x + 1 * x := by decide
    exact this _
  obtain ⟨e1, e2⟩ := update_rows h.eqn ⟨c, hc⟩ _ _ 1 ⟨c, hc⟩ (fun j => hneg j.val)
    (fun j => hneg (d + j.val)) (fun i hi => hne i.val (fun e => hi (Fin.ext e))) rfl rfl
  refine ⟨⟨by simp [hs], fun i => ?_, e2, ?_, fun i j hj => ?_⟩, ?_⟩
  · by_cases hi : i = c
    · subst hi
      rw [hself]
      exact rowC_neg (h.rows _)
    · rw [hne i hi]
      exact h.rows i
  · rw [e1]
    exact det_double_ne _ h.det
  · rw [e1]
    by_cases hi : i = ⟨c, hc⟩
    · subst hi
      have hjc : (⟨c, hc⟩ : Fin d) ≠ j := fun e => by rw [← e] at hj; exact lt_irrefl _ hj
      rw [Matrix.updateRow_self, if_neg hjc]
      have := h.unit ⟨c, hc⟩ j hj
      rw [if_neg hjc] at this
      simp [this]
    · rw [Matrix.updateRow_ne hi]
      exact h.unit i j hj
  · rw [hself]
    exact neg_val_two hw c h2

theorem addrow_aug {d c : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {B : Array V}
    (hB : Aug d c Xm B) (hc : c < d) {s : ℕ} (hs : s < d) (hsc : s ≠ c) (w : V) (t : ZMod 3)
    (hw : ∀ k, w.val k = B[s]!.val k + t * B[c]!.val k) (hwr : RowC (2 * d) w) :
    Aug d c Xm (B.set! s w) ∧ (∀ i : ℕ, i ≠ s → (B.set! s w)[i]! = B[i]!) ∧
      (B.set! s w)[s]! = w := by
  have hsz := hB.size
  have hself : (B.set! s w)[s]! = w := Array.getElem!_set!_self _ _ _ (by omega)
  have hne : ∀ i : ℕ, i ≠ s → (B.set! s w)[i]! = B[i]! := fun i hi =>
    Array.getElem!_set!_ne _ _ _ _ (Ne.symm hi)
  have hrc : (⟨s, hs⟩ : Fin d) ≠ ⟨c, hc⟩ := fun e => hsc (Fin.mk.inj e)
  obtain ⟨e1, e2⟩ := update_rows hB.eqn ⟨s, hs⟩ _ _ t ⟨c, hc⟩ (fun j => by rw [hself]; exact hw _)
    (fun j => by rw [hself]; exact hw _) (fun i hi => hne i.val (fun e => hi (Fin.ext e))) rfl rfl
  refine ⟨⟨by simp [hsz], fun i => ?_, e2, ?_, fun i j hj => ?_⟩, hne, hself⟩
  · by_cases hi : i = s
    · subst hi
      rw [hself]
      exact hwr
    · rw [hne i hi]
      exact hB.rows i
  · rw [e1, Matrix.det_updateRow_add_smul_self _ hrc]
    exact hB.det
  · rw [e1]
    by_cases hi : i = ⟨s, hs⟩
    · subst hi
      have hcj : (⟨c, hc⟩ : Fin d) ≠ j := fun e => by rw [← e] at hj; exact lt_irrefl _ hj
      have u1 := hB.unit ⟨s, hs⟩ j hj
      have u2 := hB.unit ⟨c, hc⟩ j hj
      rw [if_neg hcj] at u2
      rw [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, u1, u2, smul_zero, add_zero]
    · rw [Matrix.updateRow_ne hi]
      exact hB.unit i j hj

theorem val_sub' {a b : V} (ha : a.wf = true) (hb : b.wf = true) (k : ℕ) :
    (a.sub b).val k = a.val k + 2 * b.val k := by
  rw [V.val_sub ha hb]
  have : ∀ x y : ZMod 3, x - y = x + 2 * y := by decide
  exact this _ _

theorem val_add' {a b : V} (ha : a.wf = true) (hb : b.wf = true) (k : ℕ) :
    (a.add b).val k = a.val k + 1 * b.val k := by
  rw [V.val_add ha hb]
  ring

theorem elim_one {d c : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A2 B : Array V} (hc : c < d)
    (h1 : A2[c]!.val c = 1) {s : ℕ} (hs : s < d) (hB : Aug d c Xm B) (hBc : B[c]! = A2[c]!)
    (hz : ∀ r : Fin d, r.val < s → r.val ≠ c → Lm d B r ⟨c, hc⟩ = 0) :
    Aug d c Xm (elimStep c A2[c]! B s) ∧ (elimStep c A2[c]! B s)[c]! = A2[c]! ∧
      ∀ r : Fin d, r.val < s + 1 → r.val ≠ c → Lm d (elimStep c A2[c]! B s) r ⟨c, hc⟩ = 0 := by
  unfold elimStep
  by_cases hsc : s = c
  · rw [if_neg (by simp [hsc])]
    exact ⟨hB, hBc, fun r hr hrc => hz r (by omega) hrc⟩
  rw [if_pos (by simp [hsc])]
  have hwc : B[c]!.val c = 1 := by rw [hBc, h1]
  have hws := (hB.rows s).1
  have hwc' := (hB.rows c).1
  have hrest : ∀ (B' : Array V), (∀ i : ℕ, i ≠ s → B'[i]! = B[i]!) →
      Lm d B' ⟨s, hs⟩ ⟨c, hc⟩ = 0 →
      ∀ r : Fin d, r.val < s + 1 → r.val ≠ c → Lm d B' r ⟨c, hc⟩ = 0 := by
    intro B' hB' hs0 r hr hrc
    by_cases hrs : r.val = s
    · have : r = ⟨s, hs⟩ := Fin.ext hrs
      rw [this]
      exact hs0
    · have := hz r (by omega) hrc
      simp only [Lm, Matrix.of_apply] at this ⊢
      rw [hB' r.val hrs]
      exact this
  rcases get_cases B[s]! c with ⟨g, v⟩ | ⟨g, v⟩ | ⟨g, v⟩
  · rw [g, if_neg (by decide), if_neg (by decide)]
    refine ⟨hB, hBc, hrest B (fun _ _ => rfl) ?_⟩
    simp only [Lm, Matrix.of_apply]
    exact v
  · rw [g, if_pos (by decide), ← hBc]
    obtain ⟨a1, a2, a3⟩ := addrow_aug hB hc hs hsc _ 2 (val_sub' hws hwc')
      (rowC_sub (hB.rows s) (hB.rows c))
    refine ⟨a1, by rw [a2 c (Ne.symm hsc), hBc], hrest _ a2 ?_⟩
    simp only [Lm, Matrix.of_apply]
    rw [a3, val_sub' hws hwc', v, hwc]
    decide
  · rw [g, if_neg (by decide), if_pos (by decide), ← hBc]
    obtain ⟨a1, a2, a3⟩ := addrow_aug hB hc hs hsc _ 1 (val_add' hws hwc')
      (rowC_add (hB.rows s) (hB.rows c))
    refine ⟨a1, by rw [a2 c (Ne.symm hsc), hBc], hrest _ a2 ?_⟩
    simp only [Lm, Matrix.of_apply]
    rw [a3, val_add' hws hwc', v, hwc]
    decide

theorem elim_aug {d c : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A2 : Array V}
    (h : Aug d c Xm A2) (hc : c < d) (h1 : A2[c]!.val c = 1) :
    Aug d (c + 1) Xm (elimF d c A2) := by
  have key : ∀ m s (B : Array V), s + m ≤ d → Aug d c Xm B → B[c]! = A2[c]! →
      (∀ r : Fin d, r.val < s → r.val ≠ c → Lm d B r ⟨c, hc⟩ = 0) →
      Aug d c Xm ((List.range' s m).foldl (elimStep c A2[c]!) B) ∧
        ((List.range' s m).foldl (elimStep c A2[c]!) B)[c]! = A2[c]! ∧
        ∀ r : Fin d, r.val < s + m → r.val ≠ c →
          Lm d ((List.range' s m).foldl (elimStep c A2[c]!) B) r ⟨c, hc⟩ = 0 := by
    intro m
    induction m with
    | zero =>
      intro s B _ hB hBc hz
      simp only [List.range'_zero, List.foldl_nil, Nat.add_zero]
      exact ⟨hB, hBc, hz⟩
    | succ m ih =>
      intro s B hsm hB hBc hz
      rw [List.range'_succ, List.foldl_cons]
      obtain ⟨b1, b2, b3⟩ := elim_one hc h1 (by omega) hB hBc hz
      obtain ⟨a1, a2, a3⟩ := ih (s + 1) _ (by omega) b1 b2 b3
      exact ⟨a1, a2, fun r hr hrc => a3 r (by omega) hrc⟩
  obtain ⟨a1, a2, a3⟩ := key d 0 A2 (by omega) h rfl (fun r hr => absurd hr (Nat.not_lt_zero _))
  unfold elimF
  refine ⟨a1.size, a1.rows, a1.eqn, a1.det, fun i j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
  · exact a1.unit i j hj
  · have e : j = ⟨c, hc⟩ := Fin.ext hj
    subst e
    by_cases hi : i = ⟨c, hc⟩
    · subst hi
      rw [if_pos rfl]
      simp only [Lm, Matrix.of_apply]
      rw [a2, h1]
    · rw [if_neg hi]
      exact a3 i (by omega) (fun e => hi (Fin.ext e))

theorem val_of_get {a : V} {j k : ℕ} (h : a.get j = k) : a.val j = (k : ZMod 3) := by
  unfold V.val
  rw [h]

theorem gj_aug {d c : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} {A : Array V}
    (h : Aug d c Xm A) (hc : c < d) : Aug d (c + 1) Xm (gjStep d A c) := by
  obtain ⟨r, hr1, hr2⟩ := pivot_exists h.det hc h.unit
  have hex : ∃ r, c ≤ r ∧ r < d ∧ A[r]!.get c ≠ 0 := by
    refine ⟨r.val, hr1, r.isLt, fun g => hr2 ?_⟩
    simp only [Lm, Matrix.of_apply]
    rw [val_of_get g]
    rfl
  obtain ⟨p1, p2, p3⟩ := pivF_spec hc hex
  rw [gj_eq, if_pos p2]
  obtain ⟨s1, s2⟩ := swap_aug h hc p1 p2
  have hnz : (swapF A (pivF d c A) c)[c]!.get c ≠ 0 := by
    rw [s2]
    exact p3
  split
  · rename_i hg
    have hv2 : (swapF A (pivF d c A) c)[c]!.val c = 2 := by
      rw [val_of_get (beq_iff_eq.1 hg)]
      rfl
    obtain ⟨n1, n2⟩ := neg_aug s1 hc hv2
    exact elim_aug n1 hc n2
  · rename_i hg
    have hv1 : (swapF A (pivF d c A) c)[c]!.val c = 1 := by
      rcases get_cases (swapF A (pivF d c A) c)[c]! c with ⟨g, -⟩ | ⟨-, v⟩ | ⟨g, -⟩
      · exact absurd g hnz
      · exact v
      · exact absurd (beq_iff_eq.2 g) hg
    exact elim_aug s1 hc hv1

theorem loop_aug {d : ℕ} {Xm : Matrix (Fin d) (Fin d) (ZMod 3)} :
    ∀ m s (A : Array V), s + m ≤ d → Aug d s Xm A →
      Aug d (s + m) Xm ((List.range' s m).foldl (fun A c => gjStep d A c) A) := by
  intro m
  induction m with
  | zero =>
    intro s A _ h
    simpa using h
  | succ m ih =>
    intro s A hsm h
    rw [List.range'_succ, List.foldl_cons, show s + (m + 1) = s + 1 + m by omega]
    exact ih (s + 1) _ (by omega) (gj_aug h (by omega))

theorem testBit_one_shl (i j : ℕ) : (1 <<< i).testBit j = decide (j = i) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : j = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem aug_get {d : ℕ} (X : Array V) {i : ℕ} (hi : i < d) :
    (augF d X)[i]! = (⟨X[i]!.p ||| (1 <<< (d + i)), X[i]!.m⟩ : V) := by
  unfold augF
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem aug_base {d : ℕ} {X : Array V} (hX : canonM d X = true)
    {M : Matrix (Fin d) (Fin d) (ZMod 3)} (hM : toMat d X * M = 1) :
    Aug d 0 (toMat d X) (augF d X) := by
  have hXr := rows_of_canonM hX
  have hrow : ∀ i : ℕ, RowC (2 * d) (augF d X)[i]! := by
    intro i
    by_cases hi : i < d
    · rw [aug_get X hi]
      obtain ⟨hw, hb⟩ := hXr i
      refine ⟨V.wf_of_bits fun j => ?_, fun j hj => ?_⟩
      · simp only [Nat.testBit_or, testBit_one_shl]
        by_cases hj : j = d + i
        · rw [(hb j (by omega)).2]
          simp
        · simp only [hj, decide_false, Bool.or_false]
          exact V.not_both hw j
      · simp only [Nat.testBit_or, testBit_one_shl, (hb j (by omega)).1, (hb j (by omega)).2]
        simp only [Bool.false_or, decide_eq_false_iff_not, and_true]
        omega
    · unfold augF
      rw [getElem!_neg _ i (by simpa using hi)]
      exact rowC_zero _
  have hL : Lm d (augF d X) = toMat d X := by
    ext i j
    simp only [Lm, Matrix.of_apply, toMat_apply]
    rw [aug_get X i.isLt, V.val_eq_bitVal, V.val_eq_bitVal]
    simp only [Nat.testBit_or, testBit_one_shl]
    rw [decide_eq_false (by omega : ¬ j.val = d + i.val), Bool.or_false]
  have hR : Rm d (augF d X) = 1 := by
    ext i j
    simp only [Rm, Matrix.of_apply, Matrix.one_apply]
    rw [aug_get X i.isLt, V.val_eq_bitVal]
    obtain ⟨-, hb⟩ := hXr i.val
    simp only [Nat.testBit_or, testBit_one_shl, (hb (d + j.val) (by omega)).1,
      (hb (d + j.val) (by omega)).2, Bool.false_or]
    by_cases hij : i = j
    · subst hij
      simp [bitVal]
    · have : ¬ d + j.val = d + i.val := fun e => hij (Fin.ext (by omega))
      have hji : ¬ j.val = i.val := fun e => hij (Fin.ext e.symm)
      simp [bitVal, this, hij, hji]
  refine ⟨by simp [augF], hrow, by rw [hL, hR, one_mul], ?_,
    fun i j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [hL]
  intro h0
  have := congrArg Matrix.det hM
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem right_val (d : ℕ) (r : V) (j : ℕ) : (rightF d r).val j = r.val (d + j) := by
  rw [V.val_eq_bitVal, V.val_eq_bitVal]
  simp only [rightF, Nat.testBit_shiftRight]

theorem right_rowC {d : ℕ} {r : V} (h : RowC (2 * d) r) : RowC d (rightF d r) := by
  refine ⟨V.wf_of_bits fun j => ?_, fun j hj => ?_⟩
  · simp only [rightF, Nat.testBit_shiftRight]
    exact V.not_both h.1 _
  · simp only [rightF, Nat.testBit_shiftRight]
    exact h.2 _ (by omega)

end CFSG.KS.ONOut.InvV

namespace CFSG.KS.ONOut

open CFSG.F3.Native CFSG.Sporadic.ON.Native CFSG.KS.ONOut.InvV

theorem invV_sound {d : ℕ} {X : Array V} {M : Matrix (Fin d) (Fin d) (ZMod 3)}
    (hX : canonM d X = true) (hM : toMat d X * M = 1) :
    canonM d (invV d X) = true ∧ toMat d (invV d X) = M := by
  have hA := loop_aug d 0 (augF d X) (by omega) (aug_base hX hM)
  rw [Nat.zero_add] at hA
  have hL : Lm d ((List.range' 0 d).foldl (fun A c => gjStep d A c) (augF d X)) = 1 := by
    ext i j
    rw [hA.unit i j j.isLt, Matrix.one_apply]
  have hR : Rm d ((List.range' 0 d).foldl (fun A c => gjStep d A c) (augF d X)) = M := by
    have e := hA.eqn
    rw [hL] at e
    calc Rm d _ = Rm d _ * (toMat d X * M) := by rw [hM, Matrix.mul_one]
      _ = (Rm d _ * toMat d X) * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [← e, Matrix.one_mul]
  rw [invV_eq]
  have hs := hA.size
  have hget : ∀ i < d,
      (((List.range' 0 d).foldl (fun A c => gjStep d A c) (augF d X)).map (rightF d))[i]! =
        rightF d ((List.range' 0 d).foldl (fun A c => gjStep d A c) (augF d X))[i]! := by
    intro i hi
    rw [getElem!_pos _ i (by simp [hs, hi]), Array.getElem_map, getElem!_pos _ i (by omega)]
  refine ⟨canonM_of (by simp [hs]) fun i hi => by rw [hget i hi]; exact right_rowC (hA.rows i), ?_⟩
  ext i j
  rw [toMat_apply, hget i.val i.isLt, right_val, ← hR]
  rfl

end CFSG.KS.ONOut

end
