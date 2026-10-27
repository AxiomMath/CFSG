module

public import Certificates.Data.Kernel.SporSch.Co1Orb
public import CFSG.Sporadic.Schreier.Co1LocalOrbitInputs
import CFSG.Certificates.Kernel.Spor.PK.Basic
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch.Orb

open CFSG.Sporadic.Co1Schreier Matrix

@[expose] def conjVecP (CE : List (List (List Nat))) (i : Fin 3) (j : Fin 6) : Fin 6 → ZMod 3 :=
  Native.expVec ((CE.getD i.val []).getD j.val [])

@[expose] def actTP (CE : List (List (List Nat))) (i : Fin 3) (f : Fin 6 → ZMod 3) :
    Fin 6 → ZMod 3 :=
  let l := List.ofFn fun j => f ⬝ᵥ conjVecP CE i j
  fun j => l.getD j.val 0

@[expose] def γP (EC : List (List Nat)) (j : Fin 12) : Fin 6 → ZMod 3 :=
  fun i => ((EC.getD j.val []).getD i.val 0 : ℕ)

@[expose] def orbRepP (EC : List (List Nat)) : Fin 4 → Fin 6 → ZMod 3 :=
  ![0, γP EC 0, Pi.single 5 1, Pi.single 4 1]

@[expose] def orbTreeP (T₀ T₁ T₂ T₃ : List (ℕ × ℕ × ℕ)) : Fin 4 → List (ℕ × ℕ × ℕ) :=
  ![T₀, T₁, T₂, T₃]

@[expose] def treeCodesP (OT : Fin 4 → List (ℕ × ℕ × ℕ)) (k : Fin 4) : List ℕ := (OT k).map (·.1)

@[expose] def treeOKP (CE : List (List (List Nat))) (EC : List (List Nat))
    (OT : Fin 4 → List (ℕ × ℕ × ℕ)) (k : Fin 4) : Bool :=
  (OT k).length == orbSize k && ((treeCodesP OT k).map decodeF).Nodup &&
    (treeCodesP OT k).headD 0 == encodeF (orbRepP EC k) &&
    (List.range (OT k).length).all fun m => m == 0 ||
      (decide (((OT k).getD m (0, 0, 0)).2.1 < m) &&
        decide (((OT k).getD m (0, 0, 0)).2.2 < 3) &&
        ((OT k).getD m (0, 0, 0)).1 == encodeF (actTP CE (Fin.ofNat 3
          ((OT k).getD m (0, 0, 0)).2.2)
          (decodeF ((OT k).getD ((OT k).getD m (0, 0, 0)).2.1 (0, 0, 0)).1)))

@[expose] def treeClosedP (CE : List (List (List Nat))) (OT : Fin 4 → List (ℕ × ℕ × ℕ))
    (k : Fin 4) : Bool :=
  (treeCodesP OT k).all fun c => (List.finRange 3).all fun i =>
    (treeCodesP OT k).contains (encodeF (actTP CE i (decodeF c)))

theorem decodeF_encodeF (f : Fin 6 → ZMod 3) : decodeF (encodeF f) = f := by
  funext j
  have h : ∀ i, (f i).val < 3 := fun i => ZMod.val_lt (f i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have key : encodeF f / 3 ^ j.val % 3 = (f j).val := by
    simp only [encodeF, Fin.sum_univ_six]
    fin_cases j <;> simp <;> omega
  rw [decodeF, key, ZMod.natCast_zmod_val]

end CFSG.KS.SporSch.Orb

end

namespace CFSG.KS.SporSch.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.Co2Shape CFSG.KS.Mathieu CFSG.KS.SporSch.M24
  CFSG.Sporadic.Co1Schreier Matrix

theorem encodeF_decodeF {c : Nat} (hc : c < 729) : encodeF (decodeF c) = c := by
  simp only [encodeF, decodeF, Fin.sum_univ_six, ZMod.val_natCast]
  simp
  omega

theorem encodeF_inj {f g : Fin 6 → ZMod 3} (h : encodeF f = encodeF g) : f = g := by
  rw [← decodeF_encodeF f, h, decodeF_encodeF]

theorem encodeF_lt (f : Fin 6 → ZMod 3) : encodeF f < 729 := by
  have h : ∀ i, (f i).val < 3 := fun i => ZMod.val_lt (f i)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [encodeF, Fin.sum_univ_six]
  simp
  omega

theorem foldr_add (g : Nat → Nat) : ∀ (l : List Nat) (s : Nat),
    l.foldr (fun j s => Nat.add s (g j)) s = s + (l.map g).sum
  | [], s => by simp
  | j :: l, s => by
    rw [List.foldr_cons, foldr_add g l s, List.map_cons, List.sum_cons, Nat.add_eq]
    omega

theorem range_sum (g : Nat → Nat) (n : Nat) :
    ((List.range n).map g).sum = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem foldN_add (n : Nat) (g : Nat → Nat) :
    foldN n (fun j s => Nat.add s (g j)) 0 = ∑ j ∈ Finset.range n, g j := by
  rw [foldN_eq, foldr_add, range_sum, Nat.zero_add]

theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change nget l i = _
      rw [ih]
      simp

theorem ngetL_eq (l : List (List Nat)) (i : Nat) : ngetL l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change ngetL l i = _
      rw [ih]
      simp

theorem ngetLL_eq (l : List (List (List Nat))) (i : Nat) : ngetLL l i = l.getD i [] := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change ngetLL l i = _
      rw [ih]
      simp

theorem cOf_eq (t : Nat × Nat × Nat) : cOf t = t.1 := by
  obtain ⟨a, b, c⟩ := t
  rfl

theorem pOf_eq (t : Nat × Nat × Nat) : pOf t = t.2.1 := by
  obtain ⟨a, b, c⟩ := t
  rfl

theorem gOf_eq (t : Nat × Nat × Nat) : gOf t = t.2.2 := by
  obtain ⟨a, b, c⟩ := t
  rfl

theorem codes_eq : ∀ T : List (Nat × Nat × Nat), codes T = T.map (·.1)
  | [] => rfl
  | t :: T => by
    change cOf t :: codes T = _
    rw [cOf_eq, codes_eq T]
    rfl

theorem lenT_eq : ∀ T : List (Nat × Nat × Nat), lenT T = T.length
  | [] => rfl
  | t :: T => by
    change Nat.succ (lenT T) = _
    rw [lenT_eq T]
    rfl

theorem getD_codes (T : List (Nat × Nat × Nat)) (p : Nat) :
    (T.map (·.1)).getD p 0 = (T.getD p (0, 0, 0)).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases T[p]? <;> rfl

theorem headD_eq_getD (l : List Nat) : l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

theorem memL'_iff (x : Nat) : ∀ S : List Nat, memL' x S = true ↔ x ∈ S
  | [] => by simp [memL']
  | y :: S => by
    have e : memL' x (y :: S) = Bool.rec (motive := fun _ => Bool) (memL' x S) true (Nat.beq x y) :=
      rfl
    rw [e, List.mem_cons, ← memL'_iff x S]
    by_cases h : x = y
    · simp [h]
    · have : Nat.beq x y = false := by
        cases hb : Nat.beq x y
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) h
      rw [this]
      simp [h]

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem distinctL_sound {n : Nat} : ∀ {l : List Nat} {M : Nat}, distinctL n l M = true →
    l.Nodup ∧ ∀ x ∈ l, x < n ∧ M.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: l, M, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) x)) (distinctL n l))
          (Bool.rec (motive := fun _ => Bool) true false (hasBit M x)))
        (Nat.blt x n) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    rw [strictB_eq] at h4
    have hx : M.testBit x = false := by
      rw [← hasBit_eq]
      cases hb : hasBit M x
      · rfl
      · rw [hb] at h3
        exact absurd h3 (by decide)
    obtain ⟨hnd, hl⟩ := distinctL_sound h4
    have key : ∀ y ∈ l, y < n ∧ M.testBit y = false ∧ y ≠ x := by
      intro y hy
      obtain ⟨hyn, hyb⟩ := hl y hy
      have e : (Nat.lor M (Nat.shiftLeft 1 x)).testBit y = (M.testBit y || decide (y = x)) := by
        change (M ||| 1 <<< x).testBit y = _
        rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
        by_cases hxy : y = x
        · subst hxy
          simp
        · simp [hxy, Ne.symm hxy]
      rw [e, Bool.or_eq_false_iff] at hyb
      exact ⟨hyn, hyb.1, by simpa using hyb.2⟩
    refine ⟨List.nodup_cons.2 ⟨fun hm => (key x hm).2.2 rfl, hnd⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact ⟨Nat.le_of_ble_eq_true h1, hx⟩
    · exact ⟨(key y hy').1, (key y hy').2.1⟩

theorem actTP_val (CE : List (List (List Nat))) (i : Fin 3) (c : Nat) (j : Fin 6) :
    (actTP CE i (decodeF c) j).val =
      (∑ l ∈ Finset.range 6, dig3 c l * nget (ngetL (ngetLL CE i) j) l) % 3 := by
  have e1 : actTP CE i (decodeF c) j = decodeF c ⬝ᵥ conjVecP CE i j := by
    simp only [actTP]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  rw [e1, ← ZMod.val_natCast (n := 3)]
  congr 1
  rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
    (fun l => ((dig3 c l * nget (ngetL (ngetLL CE i) j) l : ℕ) : ZMod 3))]
  simp only [dotProduct, decodeF, conjVecP, Native.expVec, Nat.cast_mul, dig3, nget_eq, ngetL_eq,
    ngetLL_eq]
  rfl

theorem actC_eq (CE : List (List (List Nat))) (i : Fin 3) (c : Nat) :
    actC CE i c = encodeF (actTP CE i (decodeF c)) := by
  have e : actC CE i c = foldN 6 (fun j s => Nat.add s ((fun j => Nat.mul (Nat.mod
      (foldN 6 (fun l t => Nat.add t (Nat.mul (dig3 c l) (nget (ngetL (ngetLL CE i) j) l))) 0) 3)
      (Nat.pow 3 j)) j)) 0 := rfl
  rw [e, foldN_add, encodeF, ← Fin.sum_univ_eq_sum_range (fun j => Nat.mul (Nat.mod
      (foldN 6 (fun l t => Nat.add t (Nat.mul (dig3 c l) (nget (ngetL (ngetLL CE i) j) l))) 0) 3)
      (Nat.pow 3 j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [foldN_add, actTP_val]
  rfl

theorem actC_eq' (CE : List (List (List Nat))) {g : Nat} (hg : g < 3) (c : Nat) :
    actC CE g c = encodeF (actTP CE (Fin.ofNat 3 g) (decodeF c)) := by
  have := actC_eq CE (Fin.ofNat 3 g) c
  rwa [Fin.val_ofNat, Nat.mod_eq_of_lt hg] at this

theorem encG_eq (EC : List (List Nat)) (j : Fin 12) : encG EC j = encodeF (γP EC j) := by
  have e : encG EC j = foldN 6 (fun l s => Nat.add s ((fun l => Nat.mul
      (Nat.mod (nget (ngetL EC j) l) 3) (Nat.pow 3 l)) l)) 0 := rfl
  rw [e, foldN_add, encodeF, ← Fin.sum_univ_eq_sum_range (fun l => Nat.mul
      (Nat.mod (nget (ngetL EC j) l) 3) (Nat.pow 3 l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [γP, ZMod.val_natCast, nget_eq, ngetL_eq]
  rfl

theorem encNG_eq (EC : List (List Nat)) (j : Fin 12) : encNG EC j = encodeF (-γP EC j) := by
  have e : encNG EC j = foldN 6 (fun l s => Nat.add s ((fun l => Nat.mul
      (Nat.mod (Nat.sub 3 (Nat.mod (nget (ngetL EC j) l) 3)) 3) (Nat.pow 3 l)) l)) 0 := rfl
  rw [e, foldN_add, encodeF, ← Fin.sum_univ_eq_sum_range (fun l => Nat.mul
      (Nat.mod (Nat.sub 3 (Nat.mod (nget (ngetL EC j) l) 3)) 3) (Nat.pow 3 l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.neg_apply, γP, nget_eq, ngetL_eq]
  rfl

theorem enc_single5 : encodeF (Pi.single (5 : Fin 6) (1 : ZMod 3)) = 243 := by decide

theorem enc_single4 : encodeF (Pi.single (4 : Fin 6) (1 : ZMod 3)) = 81 := by decide

theorem anyG_iff (EC : List (List Nat)) (c : Nat) :
    anyG EC c = true ↔ ∃ j < 12, c = encG EC j ∨ c = encNG EC j := by
  have e : anyG EC c = Bool.rec (motive := fun _ => Bool) true false (allN 12 (fun j =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false
        (Nat.beq c (encNG EC j))) false (Nat.beq c (encG EC j)))) := rfl
  rw [e]
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have hall : allN 12 (fun j => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true false (Nat.beq c (encNG EC j))) false
          (Nat.beq c (encG EC j))) = true := by
      rw [allN_iff]
      intro j hj
      rw [beq_false fun h1 => hn ⟨j, hj, Or.inl h1⟩, beq_false fun h2 => hn ⟨j, hj, Or.inr h2⟩]
    rw [hall] at h
    exact absurd h (by decide)
  · rintro ⟨j, hj, hc⟩
    cases hall : allN 12 (fun j => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) true false (Nat.beq c (encNG EC j))) false
          (Nat.beq c (encG EC j)))
    · rfl
    · have h := allN_iff.1 hall j hj
      rcases hc with hc | hc
      · rw [hc, Nat.beq_refl] at h
        exact (Bool.false_ne_true h).elim
      · cases h1 : Nat.beq c (encG EC j)
        · rw [h1, hc, Nat.beq_refl] at h
          exact (Bool.false_ne_true h).elim
        · rw [h1] at h
          exact (Bool.false_ne_true h).elim

noncomputable def clAux (CE : List (List (List Nat))) (L : List Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => Bool.rec (motive := fun _ => Bool) false ih
    (allN (nat_lit 3) (fun i => memL' (actC CE i c) L))) l

theorem clAux_spec (CE : List (List (List Nat))) (L : List Nat) : ∀ l : List Nat,
    clAux CE L l = true → ∀ c ∈ l, ∀ i < 3, actC CE i c ∈ L
  | [], _ => by simp
  | c :: l, h => by
    have e : clAux CE L (c :: l) = Bool.rec (motive := fun _ => Bool) false (clAux CE L l)
        (allN 3 (fun i => memL' (actC CE i c) L)) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    intro d hd i hi
    rcases List.mem_cons.1 hd with rfl | hd
    · exact (memL'_iff _ L).1 (allN_iff.1 h.1 i hi)
    · exact clAux_spec CE L l h.2 d hd i hi

theorem chainK_spec (CE : List (List (List Nat))) (C : List Nat) :
    ∀ (T : List (Nat × Nat × Nat)) (m0 : Nat), chainK CE C T m0 = true → ∀ m < T.length,
      m0 + m = 0 ∨ ((T.getD m (0, 0, 0)).2.1 < m0 + m ∧ (T.getD m (0, 0, 0)).2.2 < 3 ∧
        (T.getD m (0, 0, 0)).1 = actC CE (T.getD m (0, 0, 0)).2.2 (nget C (T.getD m (0, 0, 0)).2.1))
  | [], _, _, m, hm => absurd hm (by simp)
  | t :: T, m0, h, m, hm => by
    have e : chainK CE C (t :: T) m0 = Bool.rec (motive := fun _ => Bool) false
        (chainK CE C T (Nat.succ m0))
        (Bool.rec (motive := fun _ => Bool) (strictB (pOf t) (fun p => strictB (gOf t) (fun g =>
          Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false (Nat.beq (cOf t) (actC CE g (nget C p)))
              (Nat.blt g 3)) (Nat.blt p m0)))) true (Nat.beq m0 0)) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    cases m with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero]
      by_cases h0 : m0 = 0
      · exact Or.inl h0
      · right
        have h1 := h.1
        rw [beq_false h0, strictB_eq, strictB_eq, pOf_eq, gOf_eq, cOf_eq] at h1
        simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
        exact ⟨h1.1, h1.2.1, h1.2.2⟩
    | succ m =>
      rw [List.getD_cons_succ]
      have := chainK_spec CE C T (m0 + 1) h.2 m (by simpa using hm)
      rw [show m0 + 1 + m = m0 + (m + 1) by omega] at this
      exact Or.inr (this.resolve_left (by omega))

theorem treeK_spec {CE : List (List (List Nat))} {T : List (Nat × Nat × Nat)} {r n : Nat}
    (h : treeK CE T r n = true) :
    T.length = n ∧ (T.map (·.1)).Nodup ∧ (∀ x ∈ T.map (·.1), x < 729) ∧
      (T.map (·.1)).getD 0 0 = r ∧
      (∀ m < T.length, m = 0 ∨ ((T.getD m (0, 0, 0)).2.1 < m ∧ (T.getD m (0, 0, 0)).2.2 < 3 ∧
        (T.getD m (0, 0, 0)).1 = actC CE (T.getD m (0, 0, 0)).2.2
          (T.getD (T.getD m (0, 0, 0)).2.1 (0, 0, 0)).1)) ∧
      (∀ c ∈ T.map (·.1), ∀ i < 3, actC CE i c ∈ T.map (·.1)) := by
  have e : treeK CE T r n = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (clAux CE (codes T) (codes T))
            (chainK CE (codes T) T 0))
          (Nat.beq (nget (codes T) 0) r))
        (distinctL 729 (codes T) 0))
      (Nat.beq (lenT T) n) := by
    unfold treeK
    rw [strictB_eq]
    rfl
  rw [e] at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hl, hd, hh, hc, hcl⟩ := h
  obtain ⟨hnd, hlt⟩ := distinctL_sound hd
  rw [codes_eq] at hnd hlt hh hcl hc
  rw [lenT_eq] at hl
  refine ⟨hl, hnd, fun x hx => (hlt x hx).1, by rwa [nget_eq] at hh, fun m hm => ?_,
    clAux_spec CE _ _ hcl⟩
  have := chainK_spec CE _ T 0 hc m hm
  rw [Nat.zero_add, nget_eq, getD_codes] at this
  exact this

theorem tree_facts {CE : List (List (List Nat))} {T : List (Nat × Nat × Nat)} {r n : Nat}
    {rep : Fin 6 → ZMod 3} (h : treeK CE T r n = true) (hr : r = encodeF rep) :
    ((T.length == n && ((T.map (·.1)).map decodeF).Nodup && (T.map (·.1)).headD 0 == encodeF rep &&
      (List.range T.length).all fun m => m == 0 ||
        (decide ((T.getD m (0, 0, 0)).2.1 < m) && decide ((T.getD m (0, 0, 0)).2.2 < 3) &&
          (T.getD m (0, 0, 0)).1 == encodeF (actTP CE (Fin.ofNat 3 (T.getD m (0, 0, 0)).2.2)
            (decodeF (T.getD (T.getD m (0, 0, 0)).2.1 (0, 0, 0)).1)))) = true) ∧
    ((T.map (·.1)).all fun c => (List.finRange 3).all fun i =>
      (T.map (·.1)).contains (encodeF (actTP CE i (decodeF c)))) = true ∧
    ∀ c ∈ T.map (·.1), encodeF (decodeF c) = c := by
  obtain ⟨hl, hnd, hlt, hh, hc, hcl⟩ := treeK_spec h
  refine ⟨?_, ?_, fun c hc => encodeF_decodeF (hlt c hc)⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true]
    refine ⟨⟨⟨hl, ?_⟩, by rw [headD_eq_getD, hh, hr]⟩, fun m hm => ?_⟩
    · exact hnd.map_on fun x hx y hy hxy => by
        rw [← encodeF_decodeF (hlt x hx), hxy, encodeF_decodeF (hlt y hy)]
    · rcases hc m hm with h0 | ⟨h1, h2, h3⟩
      · exact Or.inl h0
      · exact Or.inr ⟨⟨h1, h2⟩, by rw [h3, actC_eq' CE h2]⟩
  · simp only [List.all_eq_true, List.contains_iff_mem]
    intro c hc i _
    have := hcl c hc i.val i.isLt
    rwa [actC_eq] at this

public theorem orbK_sound {T₀ T₁ T₂ T₃ : List (ℕ × ℕ × ℕ)} {CE : List (List (List Nat))}
    {EC : List (List Nat)} (h : orbK T₀ T₁ T₂ T₃ CE EC = true) :
    (∀ k, treeOKP CE EC (orbTreeP T₀ T₁ T₂ T₃) k = true ∧
        treeClosedP CE (orbTreeP T₀ T₁ T₂ T₃) k = true ∧
        ∀ c ∈ treeCodesP (orbTreeP T₀ T₁ T₂ T₃) k, encodeF (decodeF c) = c) ∧
      (∀ f, ∃ k, encodeF f ∈ treeCodesP (orbTreeP T₀ T₁ T₂ T₃) k) ∧
      (∀ f, encodeF f ∈ treeCodesP (orbTreeP T₀ T₁ T₂ T₃) 1 ↔ ∃ j, f = γP EC j ∨ f = -γP EC j) := by
  unfold orbK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, hcov, hmem⟩ := h
  refine ⟨fun k => ?_, fun f => ?_, fun f => ?_⟩
  · fin_cases k
    · exact tree_facts h0 (by simp [encodeF, orbRepP])
    · exact tree_facts h1 (encG_eq EC 0)
    · exact tree_facts h2 enc_single5.symm
    · exact tree_facts h3 enc_single4.symm
  · have hc := allN_iff.1 hcov (encodeF f) (encodeF_lt f)
    rw [codes_eq, codes_eq, codes_eq, codes_eq] at hc
    cases e0 : memL' (encodeF f) (T₀.map (·.1))
    · cases e1 : memL' (encodeF f) (T₁.map (·.1))
      · cases e2 : memL' (encodeF f) (T₂.map (·.1))
        · rw [e0, e1, e2] at hc
          exact ⟨3, (memL'_iff _ _).1 hc⟩
        · exact ⟨2, (memL'_iff _ _).1 e2⟩
      · exact ⟨1, (memL'_iff _ _).1 e1⟩
    · exact ⟨0, (memL'_iff _ _).1 e0⟩
  · have hc := allN_iff.1 hmem (encodeF f) (encodeF_lt f)
    rw [codes_eq] at hc
    have hiff : encodeF f ∈ T₁.map (·.1) ↔ anyG EC (encodeF f) = true := by
      rw [← memL'_iff]
      cases e1 : memL' (encodeF f) (T₁.map (·.1)) <;> cases e2 : anyG EC (encodeF f) <;>
        rw [e1, e2] at hc <;> first | rfl | exact absurd hc (by decide)
    change encodeF f ∈ T₁.map (·.1) ↔ _
    rw [hiff, anyG_iff]
    constructor
    · rintro ⟨j, hj, hc | hc⟩
      · exact ⟨⟨j, hj⟩, Or.inl (encodeF_inj (hc.trans (encG_eq EC ⟨j, hj⟩)))⟩
      · exact ⟨⟨j, hj⟩, Or.inr (encodeF_inj (hc.trans (encNG_eq EC ⟨j, hj⟩)))⟩
    · rintro ⟨j, hc | hc⟩
      · exact ⟨j.val, j.isLt, Or.inl (by rw [hc, encG_eq])⟩
      · exact ⟨j.val, j.isLt, Or.inr (by rw [hc, encNG_eq])⟩

end CFSG.KS.SporSch.Orb
