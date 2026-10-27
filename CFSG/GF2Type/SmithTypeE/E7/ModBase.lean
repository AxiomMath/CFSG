module

public import CFSG.GF2Type.SmithTypeE.E7.ModConj
public import CFSG.GF2Type.SmithTypeE.DMod.StabOrbit
public import Certificates.Certificate38771

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.GF2Type.SmithTypeE.DMod
open CFSG.SmithD6 (applyCols tvCols wt stabCls Mf7Span mf7SpanData mf7SpanOK mf7IntOK
  mf7Commute mf7Braid mf7Dih mf7IsWt mf7Ap mf7Ap_eq mf7All mf7Gens mf7ChkReps mf7ChkRepCls
  mf7KindOf mf7KindOf_mem mf7RelOf mf7Reps mf7RepKinds)

theorem forIn_false_aux (p : ℕ → Bool) (L : List ℕ) (hL : ∃ i ∈ L, p i = false) :
    (forIn L ((none : Option Bool), ()) fun i _ =>
      if (!p i) = true then
        (pure (ForInStep.done ((some false : Option Bool), ())) :
          Id (ForInStep (Option Bool × Unit)))
      else pure (ForInStep.yield ((none : Option Bool), ()))) =
      ((some false : Option Bool), ()) := by
  induction L with
  | nil =>
    obtain ⟨i, hi, -⟩ := hL
    simp at hi
  | cons a as ih =>
    by_cases ha : p a = false
    · simp only [List.forIn_cons, ha, Bool.not_false, if_true]
      rfl
    · have ha' : p a = true := by simpa using ha
      obtain ⟨i, hi, hpi⟩ := hL
      rcases List.mem_cons.mp hi with rfl | hi'
      · exact absurd (ha'.symm.trans hpi) (by simp)
      · simp only [List.forIn_cons, ha', Bool.not_true, Bool.false_eq_true, if_false]
        exact ih ⟨i, hi', hpi⟩

theorem allLoop_spec {n : ℕ} {p : ℕ → Bool} (h : mf7All n p = true) {i : ℕ} (hi : i < n) :
    p i = true := by
  by_cases hpi : p i = true
  · exact hpi
  · exfalso
    have hf : p i = false := by simpa using hpi
    unfold mf7All at h
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
    have hmem : i ∈ List.range' 0 [:n].size := by
      rw [List.mem_range'_1]
      simp only [Std.Legacy.Range.size]
      omega
    rw [forIn_false_aux p _ ⟨i, hmem, hf⟩] at h
    simp at h

theorem mf7Gens_get (T : Array ℕ) {m : ℕ} (hm : m < 32) :
    (mf7Gens T)[m]! = T[m]! ^^^ 2 ^ m := by
  simp [mf7Gens, getElem!_pos, hm]

theorem mf7IsWt_spec {v : ℕ} (h : mf7IsWt v = true) : ∃ j < 75735, wt j = v := by
  simp only [mf7IsWt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨_, h.1, h.2⟩

theorem ap_xor (cols : Array ℕ) (a b : ℕ) :
    applyCols cols (a ^^^ b) = applyCols cols a ^^^ applyCols cols b := by
  unfold applyCols
  generalize List.range cols.size = L
  suffices h : ∀ x y,
      L.foldl (fun acc m => if (a ^^^ b).testBit m then acc ^^^ cols[m]! else acc) (x ^^^ y) =
        L.foldl (fun acc m => if a.testBit m then acc ^^^ cols[m]! else acc) x ^^^
          L.foldl (fun acc m => if b.testBit m then acc ^^^ cols[m]! else acc) y by
    simpa using h 0 0
  induction L with
  | nil => intro x y; rfl
  | cons m L ih =>
    intro x y
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Nat.testBit_xor]
    cases a.testBit m <;> cases b.testBit m <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem ap_two_pow (cols : Array ℕ) {m : ℕ} (hm : m < cols.size) :
    applyCols cols (2 ^ m) = cols[m]! := by
  unfold applyCols
  have key : ∀ n, (List.range n).foldl
      (fun acc j => if (2 ^ m).testBit j then acc ^^^ cols[j]! else acc) 0 =
        if m < n then cols[m]! else 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_two_pow]
      by_cases h1 : m = n
      · subst h1
        simp
      · by_cases h2 : m < n
        · simp [h1, h2, show m < n + 1 by omega]
        · simp [h1, h2, show ¬ m < n + 1 by omega]
  rw [key]
  simp [hm]

theorem ap_lt {cols : Array ℕ} {n : ℕ} (h : ∀ m < cols.size, cols[m]! < 2 ^ n) (c : ℕ) :
    applyCols cols c < 2 ^ n := by
  unfold applyCols
  have key : ∀ L : List ℕ, (∀ m ∈ L, m < cols.size) → ∀ a < 2 ^ n,
      L.foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) a < 2 ^ n := by
    intro L
    induction L with
    | nil => intro _ a ha; simpa using ha
    | cons m L ih =>
      intro hL a ha
      simp only [List.foldl_cons]
      apply ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      split_ifs
      · exact Nat.xor_lt_two_pow ha (h m (hL m List.mem_cons_self))
      · exact ha
  exact key _ (fun m hm => List.mem_range.mp hm) 0 (by positivity)

theorem decomp_bit {c n : ℕ} (hc : c < 2 ^ (n + 1)) :
    c = c % 2 ^ n ^^^ (if c.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow]
  by_cases hi : i < n
  · split_ifs <;> simp [hi, show n ≠ i by omega]
  · by_cases hin : i = n
    · subst hin
      split_ifs with h <;> simp [h]
    · have : c.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hc
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      split_ifs <;> simp [hi, this, Ne.symm hin]

theorem eq_of_xorLin {f g : ℕ → ℕ} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) (n : ℕ) (h : ∀ m < n, f (2 ^ m) = g (2 ^ m)) :
    ∀ c < 2 ^ n, f c = g c := by
  have hf0 : f 0 = 0 := by
    have := hf 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  have hg0 : g 0 = 0 := by
    have := hg 0 0
    rw [Nat.xor_self] at this
    rw [this, Nat.xor_self]
  induction n with
  | zero =>
    intro c hc
    have : c = 0 := by simpa using hc
    rw [this, hf0, hg0]
  | succ n ih =>
    intro c hc
    rw [decomp_bit hc, hf, hg, ih (fun m hm => h m (by omega)) _ (Nat.mod_lt _ (by positivity))]
    congr 1
    split_ifs
    · exact h n (by omega)
    · rw [hf0, hg0]

theorem getElem!_map_nat (B : Array ℕ) (f : ℕ → ℕ) {i : ℕ} (hi : i < B.size) :
    (B.map f)[i]! = f B[i]! := by
  rw [getElem!_pos (B.map f) i (by simpa using hi), getElem!_pos B i hi, Array.getElem_map]

theorem comm_eq_basis32 {T : Array ℕ} (hT : T.size = 32) {D : Mf7Span} (hcoef : D.coef.size = 32)
    (h : ∀ m < 32, applyCols D.basis D.coef[m]! = T[m]! ^^^ 2 ^ m) {c : ℕ} (hc : c < 2 ^ 32) :
    applyCols T c ^^^ c = applyCols D.basis (applyCols D.coef c) := by
  refine eq_of_xorLin (f := fun c => applyCols T c ^^^ c)
    (g := fun c => applyCols D.basis (applyCols D.coef c))
    (fun a b => ?_) (fun a b => by simp only [ap_xor]) 32 (fun m hm => ?_) c hc
  · simp only [ap_xor]
    ac_rfl
  · rw [ap_two_pow _ (by omega), ap_two_pow _ (by omega), h m hm]

theorem syn_comm32 {T : Array ℕ} (hT : T.size = 32) {D : Mf7Span}
    (h : ∀ m < 32, applyCols D.syn (T[m]! ^^^ 2 ^ m) = 0) {c : ℕ} (hc : c < 2 ^ 32) :
    applyCols D.syn (applyCols T c ^^^ c) = 0 := by
  refine eq_of_xorLin (f := fun c => applyCols D.syn (applyCols T c ^^^ c))
    (g := fun _ => 0) (fun a b => ?_) (fun a b => by simp) 32 (fun m hm => ?_) c hc
  · rw [← ap_xor]
    congr 1
    rw [ap_xor]
    ac_rfl
  · rw [ap_two_pow _ (by omega)]
    exact h m hm

theorem syn_basis8 {D E : Mf7Span} (hb : D.basis.size = 8) {d : ℕ} (hd : d < 2 ^ 8) :
    applyCols (D.basis.map (applyCols E.syn)) d = applyCols E.syn (applyCols D.basis d) := by
  refine eq_of_xorLin (f := applyCols (D.basis.map (applyCols E.syn)))
    (g := fun d => applyCols E.syn (applyCols D.basis d)) (ap_xor _)
    (fun a b => by simp only [ap_xor]) 8 (fun i hi => ?_) d hd
  rw [ap_two_pow _ (by simpa [hb] using hi), ap_two_pow _ (by omega),
    getElem!_map_nat _ _ (by omega)]

theorem spanOK_parts {T : Array ℕ} {D : Mf7Span} (h : mf7SpanOK T D = true) :
    D.basis.size = 8 ∧ D.coef.size = 32 ∧
      ∀ m < 32, D.coef[m]! < 2 ^ 8 ∧ applyCols D.basis D.coef[m]! = T[m]! ^^^ 2 ^ m ∧
        applyCols D.syn (T[m]! ^^^ 2 ^ m) = 0 := by
  simp only [mf7SpanOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hb, hc⟩, hm⟩ := h
  refine ⟨hb, hc, fun m hm' => ?_⟩
  have h1 := allLoop_spec hm hm'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, mf7Ap_eq] at h1
  rw [mf7Gens_get T hm'] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

theorem int_code {A B : Array ℕ} {DA DB : Mf7Span} (hA : A.size = 32) (hB : B.size = 32)
    (hDA : mf7SpanOK A DA = true) (hDB : mf7SpanOK B DB = true)
    (hI : mf7IntOK A B DB DA = true) {x y : ℕ} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (h : applyCols A x ^^^ x = applyCols B y ^^^ y) :
    applyCols A x ^^^ x = 0 ∨
      (mf7Commute A B = true ∧ ∃ j < 75735, wt j = applyCols A x ^^^ x) := by
  obtain ⟨hbA, hcA, hA3⟩ := spanOK_parts hDA
  obtain ⟨-, -, hB3⟩ := spanOK_parts hDB
  obtain ⟨d, hd_def⟩ : ∃ d, d = applyCols DA.coef x := ⟨_, rfl⟩
  have hd8 : d < 2 ^ 8 := by
    rw [hd_def]
    exact ap_lt (fun m hm => (hA3 m (by omega)).1) x
  have hd : d < 256 := by simpa using hd8
  have hv : applyCols A x ^^^ x = applyCols DA.basis d := by
    rw [hd_def]
    exact comm_eq_basis32 hA hcA (fun m hm => (hA3 m hm).2.1) hx
  have hsynB : applyCols DB.syn (applyCols B y ^^^ y) = 0 :=
    syn_comm32 hB (fun m hm => (hB3 m hm).2.2) hy
  have hsyn : applyCols DB.syn (applyCols DA.basis d) = 0 := by
    rw [← hv, h]
    exact hsynB
  have hS : applyCols (DA.basis.map (applyCols DB.syn)) d = 0 := by
    rw [syn_basis8 hbA hd8]
    exact hsyn
  have hmap : DA.basis.map (mf7Ap DB.syn) = DA.basis.map (applyCols DB.syn) := by
    congr 1
    funext v
    exact mf7Ap_eq DB.syn v
  have e1 : mf7Ap (DA.basis.map (mf7Ap DB.syn)) d = 0 := by
    rw [mf7Ap_eq, hmap, hS]
  have e2 : mf7Ap DA.basis d = applyCols A x ^^^ x := by
    rw [mf7Ap_eq, hv]
  have hI' := hI
  simp only [mf7IntOK] at hI'
  have hc := allLoop_spec hI' hd
  simp only [e1, e2, ne_eq, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true] at hc
  rcases hc with h0 | ⟨hcom, hw⟩
  · exact Or.inl h0
  · exact Or.inr ⟨hcom, mf7IsWt_spec hw⟩

theorem span0_ok :
    mf7SpanOK (tvCols 0) (mf7SpanData (tvCols 0)) = true := by
  have h := Certificates.certificate38771.1
  simp only [mf7ChkReps, Bool.and_eq_true] at h
  exact h.1

theorem reps_cls {c : ℕ} (hc : c < 6) :
    mf7Reps[c]! < 365211 ∧ stabCls mf7Reps[c]! = c := by
  have h := Certificates.certificate38771.2
  simp only [mf7ChkRepCls] at h
  have hc' := allLoop_spec h hc
  simpa only [decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] using hc'

theorem reps_rel {c : ℕ} (hc : c < 6) :
    mf7Commute (tvCols 0) (tvCols mf7Reps[c]!) = true ∨
      mf7Braid (tvCols 0) (tvCols mf7Reps[c]!) = true ∨
      mf7Dih (tvCols 0) (tvCols mf7Reps[c]!) = true := by
  have h := Certificates.certificate38771.1
  simp only [mf7ChkReps, Bool.and_eq_true] at h
  have hc' := allLoop_spec h.2 hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc'
  obtain ⟨⟨hk, hrel⟩, -⟩ := hc'
  have hkind := mf7KindOf_mem (tvCols 0) (tvCols mf7Reps[c]!)
  rw [hk] at hkind
  generalize mf7RepKinds[c]! = κ at hkind hrel
  rcases hkind with rfl | rfl | rfl
  · left
    simpa [mf7RelOf] using hrel
  · right
    left
    simp only [mf7RelOf, Bool.and_eq_true] at hrel
    exact hrel.1
  · right
    right
    simp only [mf7RelOf, Bool.and_eq_true] at hrel
    exact hrel.1.1

theorem reps_int {c : ℕ} (hc : c < 6) (hc0 : c ≠ 0) :
    mf7SpanOK (tvCols mf7Reps[c]!) (mf7SpanData (tvCols mf7Reps[c]!)) = true ∧
      mf7IntOK (tvCols 0) (tvCols mf7Reps[c]!) (mf7SpanData (tvCols mf7Reps[c]!))
        (mf7SpanData (tvCols 0)) = true := by
  have h := Certificates.certificate38771.1
  simp only [mf7ChkReps, Bool.and_eq_true] at h
  have hc' := allLoop_spec h.2 hc
  have hc0' : (c == 0) = false := by simpa using hc0
  simp only [Bool.and_eq_true, beq_iff_eq, hc0', Bool.false_or] at hc'
  exact hc'.2

section Vectors

theorem relC_of_mf7Commute
    {k l : ℕ} (hk : k < 365211) (hl : l < 365211)
    (h : mf7Commute (tvCols k) (tvCols l) = true) : RelC (tvEquiv k) (tvEquiv l) := by
  unfold mf7Commute at h
  apply linearEquiv_ext_single
  intro m
  have h' := allLoop_spec h m.isLt
  simp only [beq_iff_eq, mf7Ap_eq] at h'
  simp only [LinearEquiv.mul_apply, tvEquiv_single hk, tvEquiv_single hl, tvEquiv_decode hk,
    tvEquiv_decode hl]
  exact congrArg decode32 h'

theorem relB_of_mf7Braid
    {k l : ℕ} (hk : k < 365211) (hl : l < 365211)
    (h : mf7Braid (tvCols k) (tvCols l) = true) : RelB (tvEquiv k) (tvEquiv l) := by
  unfold mf7Braid at h
  unfold RelB
  apply linearEquiv_ext_single
  intro m
  have h' := allLoop_spec h m.isLt
  simp only [beq_iff_eq, mf7Ap_eq] at h'
  simp only [LinearEquiv.mul_apply, tvEquiv_single hk, tvEquiv_single hl, tvEquiv_decode hk,
    tvEquiv_decode hl]
  exact congrArg decode32 h'

theorem relD_of_mf7Dih
    {k l : ℕ} (hk : k < 365211) (hl : l < 365211)
    (h : mf7Dih (tvCols k) (tvCols l) = true) : RelD (tvEquiv k) (tvEquiv l) := by
  unfold mf7Dih at h
  unfold RelD
  apply linearEquiv_ext_single
  intro m
  have h' := allLoop_spec h m.isLt
  simp only [beq_iff_eq, mf7Ap_eq] at h'
  simp only [LinearEquiv.mul_apply, tvEquiv_single hk, tvEquiv_single hl, tvEquiv_decode hk,
    tvEquiv_decode hl]
  exact congrArg decode32 h'

theorem rel_of_codes
    {r : ℕ} (hr : r < 365211)
    (h : mf7Commute (tvCols 0) (tvCols r) = true ∨ mf7Braid (tvCols 0) (tvCols r) = true ∨
      mf7Dih (tvCols 0) (tvCols r) = true) :
    RelC (tvE 0) (tvE ⟨r, hr⟩) ∨ RelB (tvE 0) (tvE ⟨r, hr⟩) ∨ RelD (tvE 0) (tvE ⟨r, hr⟩) := by
  have h0 : (0 : ℕ) < 365211 := by norm_num
  rcases h with h | h | h
  · exact Or.inl (relC_of_mf7Commute h0 hr h)
  · exact Or.inr (Or.inl (relB_of_mf7Braid h0 hr h))
  · exact Or.inr (Or.inr (relD_of_mf7Dih h0 hr h))

@[expose] def IntV (a b : V ≃ₗ[ZMod 2] V) : Prop :=
  ∀ u : V, InEV a u → InEV b u → u = 0 ∨ (RelC a b ∧ ∃ j : Fin 75735, u = wtV j.val)

theorem intV_rep
    {r : ℕ} (hr : r < 365211) {DA DB : Mf7Span}
    (hDA : mf7SpanOK (tvCols 0) DA = true) (hDB : mf7SpanOK (tvCols r) DB = true)
    (hI : mf7IntOK (tvCols 0) (tvCols r) DB DA = true) :
    IntV (tvE 0) (tvE ⟨r, hr⟩) := by
  show IntV (tvEquiv 0) (tvEquiv r)
  have h0 : (0 : ℕ) < 365211 := by norm_num
  intro u hu hu'
  obtain ⟨x, hx⟩ := hu
  obtain ⟨y, hy⟩ := hu'
  obtain ⟨c, hc⟩ : ∃ c, c = code32 x := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = code32 y := ⟨_, rfl⟩
  have hc2 : c < 2 ^ 32 := hc ▸ code32_lt x
  have hc2' : c' < 2 ^ 32 := hc' ▸ code32_lt y
  have e1 : u = decode32 (applyCols (tvCols 0) c ^^^ c) := by
    rw [decode32_xor, ← tvEquiv_decode h0 c, hc, decode32_code32]
    exact hx
  have e2 : u = decode32 (applyCols (tvCols r) c' ^^^ c') := by
    rw [decode32_xor, ← tvEquiv_decode hr c', hc', decode32_code32]
    exact hy
  have hcode : applyCols (tvCols 0) c ^^^ c = applyCols (tvCols r) c' ^^^ c' :=
    eq_of_decode32_eq (Nat.xor_lt_two_pow (n := 32) (applyCols_tv_lt h0 c) hc2)
      (Nat.xor_lt_two_pow (n := 32) (applyCols_tv_lt hr c') hc2') (e1.symm.trans e2)
  rcases int_code (size_tvCols 0) (size_tvCols r) hDA hDB hI hc2 hc2' hcode with
    h1 | ⟨hcom, j, hj, hjw⟩
  · left
    rw [e1, h1, decode32_zero]
  · right
    refine ⟨relC_of_mf7Commute h0 hr hcom, ⟨⟨j, hj⟩, ?_⟩⟩
    rw [e1, ← hjw]
    rfl

theorem intV_smul
    (g : TD6) {k l : Fin 365211} (h : IntV (tvE k) (tvE l)) :
    IntV (tvE ((g : Equiv.Perm (Fin 365211)) k)) (tvE ((g : Equiv.Perm (Fin 365211)) l)) := by
  intro u hu hu'
  have hu_eq : u = rhoMod g ((rhoMod g).symm u) := ((rhoMod g).apply_symm_apply u).symm
  rw [hu_eq] at hu hu' ⊢
  have h1 := (inEV_tvE_smul g k _).mp hu
  have h2 := (inEV_tvE_smul g l _).mp hu'
  rcases h _ h1 h2 with h0 | ⟨hc, j, hj⟩
  · left
    rw [h0, map_zero]
  · right
    refine ⟨relC_tvE g hc, g • j, ?_⟩
    rw [hj, rhoMod_wtV]

end Vectors

theorem exists_rep_map
    (K L : Fin 365211) (hKL : K ≠ L) :
    ∃ c, c < 6 ∧ c ≠ 0 ∧ ∃ p ∈ TD6, p 0 = K ∧
      ∃ hr : mf7Reps[c]! < 365211, p ⟨mf7Reps[c]!, hr⟩ = L := by
  obtain ⟨g, hg, hg0⟩ := exists_mem_TD6_apply_zero_eq K
  obtain ⟨L', hL'⟩ : ∃ L' : Fin 365211, g L' = L := ⟨g⁻¹ L, by simp⟩
  have hL'0 : L' ≠ 0 := by
    intro h
    apply hKL
    rw [← hg0, ← hL', h]
  obtain ⟨c, hc⟩ : ∃ c, stabCls L'.val = c := ⟨_, rfl⟩
  have hc6 : c < 6 := by
    have := stabCls_le L'.val
    omega
  have hc0 : c ≠ 0 := by
    intro h0
    apply hL'0
    apply Fin.ext
    exact stabCls_eq_zero_iff.mp (hc.trans h0)
  obtain ⟨hr, hrc⟩ := reps_cls hc6
  have hab : stabCls L'.val = stabCls mf7Reps[c]! := by
    rw [hc, hrc]
  obtain ⟨h, hh, hh0, hhL⟩ := exists_stab_image (a := L') (b := ⟨mf7Reps[c]!, hr⟩) hab
  refine ⟨c, hc6, hc0, g * h⁻¹, TD6.mul_mem hg (TD6.inv_mem hh), ?_, hr, ?_⟩
  · rw [Equiv.Perm.mul_apply]
    have h1 : h⁻¹ 0 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hh0.symm
    rw [h1, hg0]
  · rw [Equiv.Perm.mul_apply]
    have h1 : h⁻¹ ⟨mf7Reps[c]!, hr⟩ = L' := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hhL.symm
    rw [h1, hL']

theorem pair_vec
    (K L : Fin 365211) (hKL : K ≠ L) :
    RelC (tvE K) (tvE L) ∨ RelB (tvE K) (tvE L) ∨ RelD (tvE K) (tvE L) := by
  obtain ⟨c, hc6, -, p, hp, hp0, hr, hpL⟩ := exists_rep_map K L hKL
  have hD := rel_of_codes hr (reps_rel hc6)
  have e0 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) 0 = K := hp0
  have e1 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) ⟨mf7Reps[c]!, hr⟩ = L := hpL
  rcases hD with h | h | h
  · left
    have h' := relC_tvE ⟨p, hp⟩ h
    rw [e0, e1] at h'
    exact h'
  · right
    left
    have h' := relB_tvE ⟨p, hp⟩ h
    rw [e0, e1] at h'
    exact h'
  · right
    right
    have h' := relD_tvE ⟨p, hp⟩ h
    rw [e0, e1] at h'
    exact h'

theorem intV_pair
    (K L : Fin 365211) (hKL : K ≠ L) :
    IntV (tvE K) (tvE L) := by
  obtain ⟨c, hc6, hc0, p, hp, hp0, hr, hpL⟩ := exists_rep_map K L hKL
  obtain ⟨hDB, hI⟩ := reps_int hc6 hc0
  have hT : IntV (tvE 0) (tvE ⟨mf7Reps[c]!, hr⟩) := intV_rep hr span0_ok hDB hI
  have hT' := intV_smul ⟨p, hp⟩ hT
  have e0 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) 0 = K := hp0
  have e1 : ((⟨p, hp⟩ : TD6) : Equiv.Perm (Fin 365211)) ⟨mf7Reps[c]!, hr⟩ = L := hpL
  rw [e0, e1] at hT'
  exact hT'

theorem pair_rel_sym7
    {k l : Nat} (hk : k < 365211) (hl : l < 365211)
    (hkl : k ≠ l) :
    (∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) c) =
      applyCols (tvCols l) (applyCols (tvCols k) c)) ∨
    (∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k) c)) =
      applyCols (tvCols l) (applyCols (tvCols k) (applyCols (tvCols l) c))) ∨
    (∀ c < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) c))) =
      applyCols (tvCols l) (applyCols (tvCols k)
        (applyCols (tvCols l) (applyCols (tvCols k) c)))) := by
  have hne : (⟨k, hk⟩ : Fin 365211) ≠ ⟨l, hl⟩ := fun h => hkl (Fin.mk.inj h)
  rcases pair_vec ⟨k, hk⟩ ⟨l, hl⟩ hne with h | h | h
  · exact Or.inl (comm_code_of_relC hk hl h)
  · exact Or.inr (Or.inl (braid_code_of_relB hk hl h))
  · exact Or.inr (Or.inr (dih_code_of_relD hk hl h))

theorem int_rel_sym7
    {k l : Nat} (hk : k < 365211) (hl : l < 365211)
    (hkl : k ≠ l) {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : applyCols (tvCols k) c ^^^ c = applyCols (tvCols l) c' ^^^ c') :
    applyCols (tvCols k) c ^^^ c = 0 ∨
      ((∀ e < 2 ^ 32, applyCols (tvCols k) (applyCols (tvCols l) e) =
          applyCols (tvCols l) (applyCols (tvCols k) e)) ∧
        ∃ j < 75735, wt j = applyCols (tvCols k) c ^^^ c) := by
  have hne : (⟨k, hk⟩ : Fin 365211) ≠ ⟨l, hl⟩ := fun h => hkl (Fin.mk.inj h)
  have hI : IntV (tvEquiv k) (tvEquiv l) := intV_pair ⟨k, hk⟩ ⟨l, hl⟩ hne
  have hu1 : decode32 (applyCols (tvCols k) c ^^^ c) = tvEquiv k (decode32 c) + decode32 c := by
    rw [decode32_xor, tvEquiv_decode hk c]
  have hu2 : decode32 (applyCols (tvCols l) c' ^^^ c') = tvEquiv l (decode32 c') + decode32 c' := by
    rw [decode32_xor, tvEquiv_decode hl c']
  have hin1 : InEV (tvEquiv k) (decode32 (applyCols (tvCols k) c ^^^ c)) :=
    ⟨decode32 c, hu1⟩
  have hin2 : InEV (tvEquiv l) (decode32 (applyCols (tvCols k) c ^^^ c)) := by
    refine ⟨decode32 c', ?_⟩
    rw [h, hu2]
  have hbd : applyCols (tvCols k) c ^^^ c < 2 ^ 32 :=
    Nat.xor_lt_two_pow (n := 32) (applyCols_tv_lt hk c) hc
  rcases hI _ hin1 hin2 with h0 | ⟨hC, j, hj⟩
  · left
    exact eq_of_decode32_eq hbd (by norm_num) (h0.trans decode32_zero.symm)
  · right
    refine ⟨comm_code_of_relC hk hl hC, j.val, j.2, ?_⟩
    exact eq_of_decode32_eq (wt_lt j.2) hbd hj.symm

end CFSG.GF2Type.SmithTypeE.E7
