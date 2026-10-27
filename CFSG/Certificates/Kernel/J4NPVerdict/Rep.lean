module

public import CFSG.Certificates.Kernel.J4NPVerdict.Sound
public import CFSG.Sporadic.J4.QTProof

public section

namespace CFSG.KC.J4NPV

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.Native CFSG.KC.J4Q CFSG.KC.Loop

@[expose] def VjRep (M : Nat) (x : J) : Prop :=
  ∃ X : Array V2, WfA X ∧ encR X = M ∧ rowsMatrix X = Mx x

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem vjRep_one (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) : VjRep one 1 :=
  ⟨idRows (), wf_idRows, enc_idRows hK, by rw [rowsMatrix_idRows, map_one]⟩

theorem vjRep_mul (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {a b : Nat} {x y : J}
    (ha : VjRep a x) (hb : VjRep b y) : VjRep (mulJ c rm a b) (x * y) := by
  obtain ⟨X, hX, eX, mX⟩ := ha
  obtain ⟨Y, hY, eY, mY⟩ := hb
  exact ⟨mulRows X Y, wf_mulRows hX hY, by rw [enc_mulRows hK hX hY, eX, eY],
    by rw [rowsMatrix_mulRows, mX, mY, map_mul]⟩

theorem vjRep_eq {M : Nat} {x y : J} (ha : VjRep M x) (hb : VjRep M y) : x = y := by
  obtain ⟨X, hX, eX, mX⟩ := ha
  obtain ⟨Y, hY, eY, mY⟩ := hb
  apply Mx_injective
  rw [← mX, ← mY]
  apply rowsMatrix_eq_of_eqRows
  rw [eqRows_eq hX hY, eX, eY]
  exact Nat.beq_refl M

theorem vjRep_eq_of_eq {a b : Nat} {x y : J} (ha : VjRep a x) (hb : VjRep b y) (h : a = b) :
    x = y :=
  vjRep_eq ha (h ▸ hb)

theorem vjRep_inv (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {g h : Nat} {x : J}
    (hg : VjRep g x) (hc : canonJ pad h = true) (hm : mulJ c rm g h = one) : VjRep h x⁻¹ := by
  obtain ⟨X, hX, eX, mX⟩ := hg
  have hb : Nat.beq (mulJ c rm (encR X) h) one = true := by
    rw [eX, hm]
    exact Nat.beq_refl one
  obtain ⟨hI, eI⟩ := invRows_enc (n := h) hK hX hc hb
  refine ⟨invRows X, hI, eI, ?_⟩
  have h1 : rowsMatrix (mulRows X (invRows X)) = rowsMatrix (idRows ()) := by
    apply rowsMatrix_eq_of_eqRows
    rw [eqRows_eq (wf_mulRows hX hI) wf_idRows, enc_mulRows hK hX hI, eX, eI, hm, enc_idRows hK]
    exact Nat.beq_refl _
  rw [rowsMatrix_mulRows, rowsMatrix_idRows, mX] at h1
  calc rowsMatrix (invRows X) = (Mx x⁻¹ * Mx x) * rowsMatrix (invRows X) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = Mx x⁻¹ * (Mx x * rowsMatrix (invRows X)) := by rw [mul_assoc]
    _ = Mx x⁻¹ := by rw [h1, mul_one]

theorem vjRep_foldl (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {l : List Nat} {xs : List J}
    (hl : List.Forall₂ VjRep l xs) : ∀ {a : Nat} {x : J}, VjRep a x →
      VjRep (l.foldl (fun acc y => mulJ c rm acc y) a) (x * xs.prod) := by
  induction hl with
  | nil =>
    intro a x h
    rw [List.foldl_nil, List.prod_nil, mul_one]
    exact h
  | cons h1 _ ih =>
    intro a x h
    rw [List.foldl_cons, List.prod_cons, ← mul_assoc]
    exact ih (vjRep_mul hK h h1)

theorem vjRep_prodK (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {l : List Nat} {xs : List J}
    (h : List.Forall₂ VjRep l xs) : VjRep (prodK c rm one l) xs.prod := by
  cases h with
  | nil => exact vjRep_one hK
  | cons h1 h2 =>
    rw [prodK_cons, List.prod_cons]
    have := vjRep_foldl hK h2 h1
    exact this

theorem vjRep_letJ {mats invs : List Nat} {gs : Nat → J}
    (hm : ∀ i, VjRep (getN one mats i) (gs i)) (hi : ∀ i, VjRep (getN one invs i) (gs i)⁻¹)
    (l : Int) :
    VjRep (letJ one mats invs l) (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹) := by
  rcases l with (_ | n) | n
  · have e : letJ one mats invs (Int.ofNat 0) = getN one invs 0 := rfl
    rw [e]
    simpa using hi 0
  · have e : letJ one mats invs (Int.ofNat (n + 1)) = getN one mats n := rfl
    rw [e]
    simpa using hm n
  · have e : letJ one mats invs (Int.negSucc n) = getN one invs n := rfl
    rw [e]
    simpa [Int.neg_negSucc] using hi n

theorem vjRep_wordFrom (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats invs : List Nat}
    {gs : Nat → J} (hm : ∀ i, VjRep (getN one mats i) (gs i))
    (hi : ∀ i, VjRep (getN one invs i) (gs i)⁻¹) :
    ∀ (w : List Int) {a : Nat} {x : J}, VjRep a x →
      VjRep (wordFrom c rm one mats invs w a) (x * wordProd gs w)
  | [], a, x, h => by
    change VjRep a (x * wordProd gs [])
    simpa [wordProd] using h
  | l :: w, a, x, h => by
    change VjRep (strictN (mulJ c rm a (letJ one mats invs l)) (wordFrom c rm one mats invs w)) _
    rw [vj_strictN_eq]
    have e : wordProd gs (l :: w) =
        (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹) * wordProd gs w := by
      simp [wordProd]
    rw [e, ← mul_assoc]
    exact vjRep_wordFrom hK hm hi w (vjRep_mul hK h (vjRep_letJ hm hi l))

theorem vjRep_wordJ (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats invs : List Nat}
    {gs : Nat → J} (hm : ∀ i, VjRep (getN one mats i) (gs i))
    (hi : ∀ i, VjRep (getN one invs i) (gs i)⁻¹) (w : List Int) :
    VjRep (wordJ c rm one mats invs w) (wordProd gs w) := by
  have := vjRep_wordFrom hK hm hi w (vjRep_one hK)
  rwa [one_mul] at this

theorem eta_eq_prod (u : Nat → J) (c : Nat) : ∀ n,
    eta u n c = (((List.range n).filter fun j => c.testBit j).map u).prod
  | 0 => rfl
  | n + 1 => by
    unfold eta at *
    rw [List.range_succ, List.foldl_append, List.filter_append, List.map_append, List.prod_append,
      ← eta_eq_prod u c n]
    unfold eta
    by_cases h : c.testBit n <;> simp [h]

theorem vjRep_selFrom {m : Nat} {u : Nat → J} : ∀ (Ts : List Nat) (j : Nat),
    (∀ i < Ts.length, VjRep (Ts.getD i 0) (u (j + i))) →
      List.Forall₂ VjRep (selFrom m Ts j) (((List.range' j Ts.length).filter fun i => m.testBit i).map u)
  | [], _, _ => List.Forall₂.nil
  | T :: Ts, j, h => by
    have ih := vjRep_selFrom (m := m) Ts (j + 1) fun i hi => by
      have := h (i + 1) (by simp only [List.length_cons]; omega)
      rwa [List.getD_cons_succ, show j + (i + 1) = j + 1 + i by omega] at this
    have hT : VjRep T (u j) := by simpa using h 0 (by simp)
    change List.Forall₂ VjRep (Bool.rec (motive := fun _ => List Nat) (selFrom m Ts (j + 1))
      (T :: selFrom m Ts (j + 1)) (bitB m j)) _
    rw [bitB_eq, List.length_cons, List.range'_succ, List.filter_cons]
    cases hb : m.testBit j
    · simpa using ih
    · simpa using List.Forall₂.cons hT ih

theorem vjRep_getsK {one : Nat} {Ms : List Nat} {k : Nat → J}
    (h : ∀ i, VjRep (getN one Ms i) (k i)) :
    ∀ l : List Nat, List.Forall₂ VjRep (getsK one Ms l) (l.map k)
  | [] => List.Forall₂.nil
  | i :: l => List.Forall₂.cons (h i) (vjRep_getsK h l)

theorem vjRep_maskK {T : Tabs} (hK : Consts T.c T.rm T.one pad t0 t1 t2 t3 t4 t5 t6)
    {Vs : List Nat} {v : Nat → J} (h : ∀ i < Vs.length, VjRep (Vs.getD i 0) (v i)) (m : Nat) :
    VjRep (maskK T Vs m) (eta v Vs.length m) := by
  have h1 := vjRep_selFrom (m := m) Vs 0 (fun i hi => by
    rw [Nat.zero_add]
    exact h i hi)
  rw [← List.range_eq_range'] at h1
  rw [eta_eq_prod]
  exact vjRep_prodK hK h1

theorem vjRep_coordK {T : Tabs} (hK : Consts T.c T.rm T.one pad t0 t1 t2 t3 t4 t5 t6) {u k : Nat → J}
    (hu : T.us.length = 11) (hu' : ∀ i < 11, VjRep (T.us.getD i 0) (u i))
    (hk : ∀ i, VjRep (getN T.one T.km i) (k i)) (p : Nat × Nat) :
    VjRep (coordK T p) (eta u 11 p.1 * ((CFSG.J4Tree.Native.pcSeqT p.2).map k).prod) := by
  have h1 := vjRep_selFrom (m := p.1) T.us 0 (fun i hi => by
    rw [Nat.zero_add]
    exact hu' i (hu ▸ hi))
  have h2 := vjRep_getsK hk (pcSeqK p.2)
  rw [hu, ← List.range_eq_range'] at h1
  rw [pcSeqK_eq] at h2
  have := vjRep_prodK hK (List.rel_append h1 h2)
  rw [List.prod_append, ← eta_eq_prod] at this
  have e : coordK T p = prodK T.c T.rm T.one
      (selFrom p.1 T.us 0 ++ getsK T.one T.km (CFSG.J4Tree.Native.pcSeqT p.2)) := by
    rw [← pcSeqK_eq]
    rfl
  rw [e]
  exact this

end CFSG.KC.J4NPV

end
