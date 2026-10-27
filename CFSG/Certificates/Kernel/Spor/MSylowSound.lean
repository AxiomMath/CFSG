module

public import Certificates.Data.Kernel.Spor.MSylow
public import CFSG.Certificates.Kernel.Spor.PCountSound
public import CFSG.Sporadic.Schreier.MathieuSylowAutSpec
public import CFSG.Certificates.Kernel.SporSch.ClassOneSound

public section

namespace CFSG.KS.MSyl

open CFSG.KC.Enum CFSG.KS CFSG.KS.PCnt CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Monster.B.Mathieu CFSG.KS.PK

variable {n : Nat}

theorem strictP_eq (y : Nat) (k : Nat → List Nat × List Nat) : strictP y k = k y := by
  cases y <;> rfl

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem getDN_eq : ∀ (L : List Nat) (i d : Nat), getDN L i d = L.getD i d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: L, i + 1, d => by
    rw [List.getD_cons_succ]
    exact getDN_eq L i d

theorem allL_iff (f : Nat → Bool) : ∀ L : List Nat, allL f L = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [allL]
  | x :: L => by
    have h : allL f (x :: L) = bAnd(f x, allL f L) := rfl
    rw [h, bAnd_eq, Bool.and_eq_true, allL_iff f L, List.forall_mem_cons]

theorem getD_map_inv (vs : List (Equiv.Perm (Fin n))) (k : Nat) :
    (vs.map (·⁻¹)).getD k 1 = (vs.getD k 1)⁻¹ := by
  simpa only [inv_one] using getD_map (fun g : Equiv.Perm (Fin n) => g⁻¹) vs k 1

theorem letP_pk (hn : n ≤ 16) (vs ws : List (Equiv.Perm (Fin n))) (l : Int) :
    letP (pk (1 : Equiv.Perm (Fin n))) (vs.map pk) (ws.map pk) l =
      pk (if 0 < l then vs.getD (l.natAbs - 1) 1 else ws.getD (l.natAbs - 1) 1) := by
  have hg : ∀ (L : List (Equiv.Perm (Fin n))) (k : Nat),
      (L.map pk).getD k (pk 1) = pk (L.getD k 1) := fun L k => getD_map pk L k 1
  rcases l with (_ | j) | k
  · show getDN _ 0 _ = _
    rw [getDN_eq, hg]
    simp
  · show getDN _ j _ = _
    have e : (Int.ofNat (j + 1)).natAbs - 1 = j := rfl
    have e' : (0 : Int) < Int.ofNat (j + 1) := Int.ofNat_succ_pos j
    rw [getDN_eq, hg, if_pos e', e]
  · show getDN _ k _ = _
    rw [getDN_eq, hg]
    simp

theorem wordV_cons (w m I : Nat) (vs vis : List Nat) (l : Int) (ws : List Int) :
    wordV n w m I vs vis (l :: ws) =
      strictN (wordV n w m I vs vis ws) (fun R => pcomp n w m (letP I vs vis l) R) := rfl

theorem wordI_cons (w m I : Nat) (vs vis : List Nat) (l : Int) (ws : List Int) :
    wordI n w m I vs vis (l :: ws) =
      strictN (wordI n w m I vs vis ws) (fun R => pcomp n w m R (letIP I vs vis l)) := rfl

theorem wordValue_nil' (vs : List (Equiv.Perm (Fin n))) : wordValue vs [] = 1 := by
  simp [wordValue]

theorem wordV_pk (hn : n ≤ 16) (vs : List (Equiv.Perm (Fin n))) : ∀ w : List Int,
    wordV n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (vs.map pk) ((vs.map (·⁻¹)).map pk) w =
      pk (wordValue vs w)
  | [] => by rw [wordValue_nil']; rfl
  | l :: w => by
    rw [wordV_cons, strictN_eq, wordV_pk hn vs w, letP_pk hn, pk_mul hn, wordValue_cons',
      letterValue_eq, getD_map_inv]

theorem wordI_pk (hn : n ≤ 16) (vs : List (Equiv.Perm (Fin n))) : ∀ w : List Int,
    wordI n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (vs.map pk) ((vs.map (·⁻¹)).map pk) w =
      pk (wordValue vs w)⁻¹
  | [] => by rw [wordValue_nil', inv_one]; rfl
  | l :: w => by
    rw [wordI_cons, strictN_eq, wordI_pk hn vs w]
    show pcomp n 4 (mask 4) _ (letP _ ((vs.map (·⁻¹)).map pk) (vs.map pk) l) = _
    rw [letP_pk hn, pk_mul hn, wordValue_cons', letterValue_eq, mul_inv_rev, getD_map_inv]
    split_ifs <;> simp

theorem slpRun_cons (w m I : Nat) (d : List Int) (ds : List (List Int)) (vs vis : List Nat) :
    slpRun n w m I (d :: ds) vs vis = strictP (wordV n w m I vs vis d) (fun v =>
      strictP (wordI n w m I vs vis d) (fun vi => slpRun n w m I ds (vs ++ [v]) (vis ++ [vi]))) :=
  rfl

theorem slpRun_pk (hn : n ≤ 16) : ∀ (ds : List (List Int)) (vs : List (Equiv.Perm (Fin n))),
    slpRun n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) ds (vs.map pk) ((vs.map (·⁻¹)).map pk) =
      ((ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map pk,
        ((ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map (·⁻¹)).map pk)
  | [], _ => rfl
  | d :: ds, vs => by
    have e := slpRun_pk hn ds (vs ++ [wordValue vs d])
    simp only [List.map_append, List.map_cons, List.map_nil] at e
    rw [slpRun_cons, strictP_eq, strictP_eq, wordV_pk hn, wordI_pk hn, e]
    rfl

theorem slpP_pk (hn : n ≤ 16) (x y : Equiv.Perm (Fin n)) (ds : List (List Int)) :
    slpP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) (pk x⁻¹) (pk y) (pk y⁻¹) ds =
      ((slpVals x y ds).map pk, ((slpVals x y ds).map (·⁻¹)).map pk) :=
  slpRun_pk hn ds [x, y]

theorem exprsV_pk (hn : n ≤ 16) (L : List (Equiv.Perm (Fin n))) : ∀ es : List (List Int),
    exprsV n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (L.map pk, (L.map (·⁻¹)).map pk) es =
      es.map fun e => pk (wordValue L e)
  | [] => rfl
  | e :: es => by
    show wordV n 4 (mask 4) _ (L.map pk) ((L.map (·⁻¹)).map pk) e :: exprsV n 4 (mask 4) _ _ es = _
    rw [wordV_pk hn, exprsV_pk hn L es]
    rfl

theorem exprsI_pk (hn : n ≤ 16) (L : List (Equiv.Perm (Fin n))) : ∀ es : List (List Int),
    exprsI n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (L.map pk, (L.map (·⁻¹)).map pk) es =
      es.map fun e => pk (wordValue L e)⁻¹
  | [] => rfl
  | e :: es => by
    show wordI n 4 (mask 4) _ (L.map pk) ((L.map (·⁻¹)).map pk) e :: exprsI n 4 (mask 4) _ _ es = _
    rw [wordI_pk hn, exprsI_pk hn L es]
    rfl

theorem powP_pk (hn : n ≤ 16) (x : Equiv.Perm (Fin n)) : ∀ e : Nat,
    powP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) e = pk (x ^ e)
  | 0 => by rw [pow_zero]; rfl
  | e + 1 => by
    show strictN (powP n 4 (mask 4) _ (pk x) e) _ = _
    rw [strictN_eq, powP_pk hn x e, pk_mul hn, ← pow_succ']

theorem ordLoop_pk (hn : n ≤ 16) (x : Equiv.Perm (Fin n)) (o : Nat) :
    ∀ (k f d : Nat), d + k = o → k < f →
      (ordLoop n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) o f (pk (x ^ d)) d = true ↔
        x ^ o = 1 ∧ ∀ e, d ≤ e → e < o → e ∣ o → x ^ e ≠ 1)
  | _, 0, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | 0, f + 1, d, hd, _ => by
    have h : ordLoop n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) o (f + 1) (pk (x ^ d)) d =
        bIf(Nat.beq d o, Nat.beq (pk (x ^ d)) (pk 1),
          bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq (pk (x ^ d)) (pk 1), false, true),
            true), strictB (pcomp n 4 (mask 4) (pk (x ^ d)) (pk x)) (fun q =>
              ordLoop n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) o f q (Nat.succ d)))) := rfl
    have hdo : d = o := by omega
    subst hdo
    rw [h, bIf_eq]
    simp only [Nat.beq_refl, ↓reduceIte, beq_pk_iff hn]
    exact ⟨fun h => ⟨h, fun e h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩
  | k + 1, f + 1, d, hd, hf => by
    have h : ordLoop n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) o (f + 1) (pk (x ^ d)) d =
        bIf(Nat.beq d o, Nat.beq (pk (x ^ d)) (pk 1),
          bAnd(bIf(Nat.beq (Nat.mod o d) (nat_lit 0), bIf(Nat.beq (pk (x ^ d)) (pk 1), false, true),
            true), strictB (pcomp n 4 (mask 4) (pk (x ^ d)) (pk x)) (fun q =>
              ordLoop n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) o f q (Nat.succ d)))) := rfl
    have hdo : (Nat.beq d o = true) = False := by rw [Nat.beq_eq]; exact eq_false (by omega)
    rw [h, bIf_eq]
    simp only [hdo, ↓reduceIte]
    rw [bAnd_eq, strictB_eq, pk_mul hn, ← pow_succ, Bool.and_eq_true,
      ordLoop_pk hn x o k f (d + 1) (by omega) (by omega), bIf_eq, bIf_eq]
    simp only [Nat.beq_eq, beq_pk_iff hn]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, fun e he1 he2 he3 => ?_⟩
      rcases Nat.eq_or_lt_of_le he1 with hde | he1
      · subst hde
        have hm : Nat.mod o d = 0 := Nat.mod_eq_zero_of_dvd he3
        simp only [hm, ↓reduceIte] at h1
        intro hx
        simp [hx] at h1
      · exact h3 e he1 he2 he3
    · rintro ⟨h2, h3⟩
      refine ⟨?_, h2, fun e he1 he2 he3 => h3 e (by omega) he2 he3⟩
      split_ifs with hm hx
      · exact absurd hx (h3 d le_rfl (by omega) (Nat.dvd_of_mod_eq_zero (n := o) hm))
      · rfl
      · rfl

theorem ordExP_pk (hn : n ≤ 16) (x : Equiv.Perm (Fin n)) {o : Nat} (ho : 0 < o) :
    ordExP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk x) o = true ↔ orderOf x = o := by
  have h := ordLoop_pk hn x o (o - 1) o 1 (by omega) (by omega)
  rw [pow_one] at h
  rw [ordExP, h]
  constructor
  · rintro ⟨h1, h2⟩
    have hpos : 0 < orderOf x := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨o, ho, h1⟩)
    have hd := orderOf_dvd_of_pow_eq_one h1
    rcases Nat.lt_or_ge (orderOf x) o with hl | hl
    · exact absurd (pow_orderOf_eq_one x) (h2 _ hpos hl hd)
    · exact le_antisymm (Nat.le_of_dvd ho hd) hl
  · rintro rfl
    refine ⟨pow_orderOf_eq_one x, fun e he1 he2 _ hx => ?_⟩
    have := Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hx)
    omega

theorem tblWord_flag (hn : n < 2 ^ 32) {Ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) Ts gs) : ∀ w : List Int, (tblWord n Ts w).2 = true
  | [] => rfl
  | l :: w => by
    have hT := rep_getD_tables hn h (l.natAbs - 1)
    by_cases hl : 0 < l
    · simp only [tblWord, hl, ↓reduceIte]
      exact tblWord_flag hn h w
    · simp only [tblWord, hl, ↓reduceIte, Bool.and_eq_true]
      exact ⟨tblWord_flag hn h w, CFSG.KS.Tbl.invOK_invT hn hT⟩

theorem tblSlp_aux (hn : n < 2 ^ 32) (ds : List (List Int)) :
    ∀ (acc : List Table × Bool) (vs : List (Equiv.Perm (Fin n))),
      List.Forall₂ (Rep n) acc.1 vs → acc.2 = true →
      (ds.foldl (fun acc w => (acc.1 ++ [(tblWord n acc.1 w).1], acc.2 && (tblWord n acc.1 w).2))
        acc).2 = true := by
  induction ds with
  | nil => intro acc vs _ h; exact h
  | cons w ds ih =>
    intro acc vs hacc h
    rw [List.foldl_cons]
    refine ih _ (vs ++ [wordValue vs w])
      (forall₂_append hacc (.cons (rep_tblWord hn hacc w (tblWord_flag hn hacc w)) .nil)) ?_
    simp [h, tblWord_flag hn hacc w]

theorem tblSlp_ok (hn : n < 2 ^ 32) {xT yT : Table} {x y : Equiv.Perm (Fin n)}
    (hx : Rep n xT x) (hy : Rep n yT y) (ds : List (List Int)) : (tblSlp n xT yT ds).2 = true :=
  tblSlp_aux hn ds _ [x, y] (.cons hx (.cons hy .nil)) rfl

theorem rep_tblSlp' (hn : n < 2 ^ 32) {xT yT : Table} {x y : Equiv.Perm (Fin n)}
    (hx : Rep n xT x) (hy : Rep n yT y) (ds : List (List Int)) :
    List.Forall₂ (Rep n) (tblSlp n xT yT ds).1 (slpVals x y ds) :=
  rep_tblSlp hn hx hy ds (tblSlp_ok hn hx hy ds)

theorem rep_tblWord' (hn : n < 2 ^ 32) {Ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) Ts gs) (w : List Int) : Rep n (tblWord n Ts w).1 (wordValue gs w) :=
  rep_tblWord hn h w (tblWord_flag hn h w)

theorem exists_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ x ∈ l₁, ∃ y ∈ l₂, R x y
  | _, _, .nil, _, hx => absurd hx List.not_mem_nil
  | _, _, .cons hab h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨y, hy, hr⟩ := exists_of_forall₂ h x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem allEqP_map (f g : List Int → Nat) : ∀ es : List (List Int), (∀ e ∈ es, f e = g e) →
    allEqP (es.map f) (es.map g) = true
  | [], _ => rfl
  | e :: es, h => by
    show bAnd(Nat.beq (f e) (g e), allEqP (es.map f) (es.map g)) = true
    rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq]
    exact ⟨h e List.mem_cons_self, allEqP_map f g es fun e he => h e (List.mem_cons_of_mem _ he)⟩

theorem all_zip_map {α β : Type*} (F : List Int → α) (H : List Int → β) (p : α → β → Bool) :
    ∀ es : List (List Int), ((es.map F).zip (es.map H)).all (fun q => p q.1 q.2) = true →
      ∀ e ∈ es, p (F e) (H e) = true
  | [], _ => by simp
  | e :: es, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact all_zip_map F H p es h.2 e' he'

theorem pow_pred_eq_inv {g : Equiv.Perm (Fin n)} {m : Nat} (hg : orderOf g = m) (hm : 0 < m) :
    g ^ (m - 1) = g⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel hm, ← hg, pow_orderOf_eq_one]

theorem clAdd_cons' (w m y g : Nat) (gs E : List Nat) :
    clAdd n w m y (g :: gs) E =
      clAdd n w m y gs (if memB (pcomp n w m y g) E = true then E else E ++ [pcomp n w m y g]) := by
  show strictL (pcomp n w m y g) (fun z => Bool.rec (motive := fun _ => List Nat)
    (clAdd n w m y gs (E ++ [z])) (clAdd n w m y gs E) (memB z E)) = _
  rw [strictL_eq]
  cases memB (pcomp n w m y g) E <;> rfl

theorem clAdd_append (w m y : Nat) : ∀ (A B E : List Nat),
    clAdd n w m y (A ++ B) E = clAdd n w m y B (clAdd n w m y A E)
  | [], _, _ => rfl
  | g :: A, B, E => by rw [List.cons_append, clAdd_cons', clAdd_cons', clAdd_append w m y A B]

theorem clRun_succ (w m : Nat) (gs : List Nat) (f h : Nat) (E : List Nat) :
    clRun n w m gs (f + 1) h E = if h < E.length then
      clRun n w m gs f (h + 1) (clAdd n w m (getN E h) gs E) else clRun n w m gs f (h + 1) E := by
  show Bool.rec (motive := fun _ => List Nat) (clRun n w m gs f (Nat.succ h) E)
    (clRun n w m gs f (Nat.succ h) (clAdd n w m (getN E h) gs E)) (Nat.blt h E.length) = _
  by_cases hh : h < E.length
  · rw [if_pos hh, show Nat.blt h E.length = true by rw [Nat.blt_eq]; exact hh]
  · rw [if_neg hh, show Nat.blt h E.length = false from
      Bool.eq_false_iff.2 fun e => hh (by rw [Nat.blt_eq] at e; exact e)]

theorem clRun_ge (w m : Nat) (gs : List Nat) : ∀ (f h : Nat) (E : List Nat), E.length ≤ h →
    clRun n w m gs f h E = E
  | 0, _, _, _ => rfl
  | f + 1, h, E, hE => by
    rw [clRun_succ, if_neg (by omega), clRun_ge w m gs f (h + 1) E (by omega)]

theorem getD_eq_getElem' {L : List Nat} {i : Nat} (hi : i < L.length) : L.getD i 0 = L[i] := by
  simp [hi]

@[expose] def SimA (n : Nat) (A : Array Table) (E : List Nat) : Prop :=
  E.length = A.size ∧ ∀ i < A.size, ∀ σ : Equiv.Perm (Fin n), Rep n A[i]! σ → E.getD i 0 = pk σ

section

open CFSG.KS.KeyBfs

variable {G : Array Table} {gg : Nat → Equiv.Perm (Fin n)} {Gp : List Nat}

theorem good_step (hG : ∀ l < G.size, Rep n G[l]! (gg l)) :
    ∀ l < G.size, ∀ T : Table, (∃ σ : Equiv.Perm (Fin n), Rep n T σ) →
      ∃ σ : Equiv.Perm (Fin n), Rep n ((fun l y => compT n y G[l]!) l T) σ :=
  fun l hl _ ⟨σ, hσ⟩ => ⟨σ * gg l, Rep.compT hσ (hG l hl)⟩

theorem sim_inner_step (hn : n ≤ 16) (hG : ∀ l < G.size, Rep n G[l]! (gg l)) {h j : Nat} {s : St}
    {E : List Nat} {τ : Equiv.Perm (Fin n)} (hj : j < G.size)
    (hI : CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h j s)
    (hh : h < s.2.1.size) (hτ : Rep n s.2.1[h]! τ) (hS : SimA n s.2.1 E) :
    ∃ s', innerBody n (fun l y => compT n y G[l]!) s.2.1[h]! h j s = pure (ForInStep.yield s') ∧
      CInv n G.size (fun l y => compT n y G[l]!) (idT n)
        (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h (j + 1) s' ∧
      s.2.1.size ≤ s'.2.1.size ∧ s'.2.1[h]! = s.2.1[h]! ∧
      SimA n s'.2.1 (if memB (pk (τ * gg j)) E = true then E else E ++ [pk (τ * gg j)]) := by
  obtain ⟨s', e, hI', hle, hh'⟩ := cinv_inner_step (good_step hG) hj hI hh
  refine ⟨s', e, hI', hle, hh', ?_⟩
  obtain ⟨-, -, -, -, hg, -, hK, -, -⟩ := hI
  have hTr : Rep n (compT n s.2.1[h]! G[j]!) (τ * gg j) := Rep.compT hτ (hG j hj)
  have hmem : memB (pk (τ * gg j)) E = s.1.contains (key n (compT n s.2.1[h]! G[j]!)) := by
    rw [Bool.eq_iff_iff, memB_iff, hK]
    constructor
    · intro hm
      obtain ⟨i, hi, hiE⟩ := List.getElem_of_mem hm
      have hi' : i < s.2.1.size := hS.1 ▸ hi
      obtain ⟨σ, hσ⟩ := hg i hi'
      have := hS.2 i hi' σ hσ
      rw [getD_eq_getElem' hi, hiE] at this
      refine ⟨i, hi', ?_⟩
      rw [← pk_inj hn this] at hσ
      exact CFSG.KS.ClassOne.key_eq_of_rep hσ hTr
    · rintro ⟨i, hi, hk⟩
      obtain ⟨σ, hσ⟩ := hg i hi
      have hσe : σ = τ * gg j := CFSG.KS.Tbl.key_inj hσ hTr hk
      have := hS.2 i hi σ hσ
      rw [← hS.1] at hi
      rw [getD_eq_getElem' hi] at this
      rw [← hσe, ← this]
      exact List.getElem_mem hi
  simp only [innerBody] at e
  by_cases hc : s.1.contains (key n (compT n s.2.1[h]! G[j]!)) = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at e
    have e' : s' = (s.1, s.2.1, s.2.2.1, s.2.2.2) := (ForInStep.yield.inj e).symm
    rw [e', if_pos (hmem.trans hc)]
    exact hS
  · have hc' : s.1.contains (key n (compT n s.2.1[h]! G[j]!)) = false := Bool.eq_false_iff.2 hc
    simp only [hc', Bool.not_false, ↓reduceIte] at e
    have e' := (ForInStep.yield.inj e).symm
    rw [e', if_neg (by rw [hmem]; exact hc)]
    refine ⟨by simp [hS.1], fun i hi σ hσ => ?_⟩
    change i < (s.2.1.push (compT n s.2.1[h]! G[j]!)).size at hi
    change Rep n (s.2.1.push (compT n s.2.1[h]! G[j]!))[i]! σ at hσ
    rw [Array.size_push] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with a | rfl
    · rw [push_lt a] at hσ
      have hi' : i < E.length := hS.1 ▸ a
      rw [getD_eq_getElem' (by simp; omega), List.getElem_append_left hi', ← getD_eq_getElem' hi']
      exact hS.2 i a σ hσ
    · rw [push_eq] at hσ
      have hσe : σ = τ * gg j := CFSG.KS.Tbl.key_inj hσ hTr rfl
      rw [← hS.1, hσe]
      simp

theorem sim_inner (hn : n ≤ 16) (hG : ∀ l < G.size, Rep n G[l]! (gg l)) (hGp : Gp.length = G.size)
    (hGv : ∀ l < G.size, Gp.getD l 0 = pk (gg l)) {h : Nat} {s : St} {E : List Nat}
    (hI : CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h 0 s)
    (hh : h < s.2.1.size) (hS : SimA n s.2.1 E) :
    let s' := Id.run (forIn (List.range' 0 G.size) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerBody n (fun l y => compT n y G[l]!) s.2.1[h]! h))
    SimA n s'.2.1 (clAdd n 4 (mask 4) (getN E h) Gp E) ∧ s.2.1.size ≤ s'.2.1.size := by
  obtain ⟨τ, hτ⟩ := hI.2.2.2.2.1 h hh
  have hy : getN E h = pk τ := by rw [getN_eq]; exact hS.2 h hh τ hτ
  have := forIn_range'_yield G.size 0 (s.1, s.2.1, s.2.2.1, s.2.2.2)
    (innerBody n (fun l y => compT n y G[l]!) s.2.1[h]! h)
    (fun j s' => CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h j s' ∧ s.2.1.size ≤ s'.2.1.size ∧
      s'.2.1[h]! = s.2.1[h]! ∧ SimA n s'.2.1 (clAdd n 4 (mask 4) (pk τ) (Gp.take j) E))
    (fun j hj s' hP => by
      rw [Nat.zero_add]
      obtain ⟨hI', hle, he, hS'⟩ := hP
      have hτ' : Rep n s'.2.1[h]! τ := he ▸ hτ
      obtain ⟨s'', e, hI'', hle', he', hS''⟩ := sim_inner_step hn hG hj hI' (by omega) hτ' hS'
      rw [he] at e
      refine ⟨s'', e, hI'', by omega, he'.trans he, ?_⟩
      have ht : Gp.take (j + 1) = Gp.take j ++ [Gp.getD j 0] := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega),
          getD_eq_getElem' (show j < Gp.length by omega)]
        rfl
      rw [ht, clAdd_append, clAdd_cons', hGv j hj, pk_mul hn]
      exact hS'')
    ⟨hI, le_rfl, rfl, hS⟩
  obtain ⟨-, hle, -, hS'⟩ := this
  rw [List.take_of_length_le (by omega), ← hy] at hS'
  exact ⟨hS', hle⟩

theorem sim_outer (hn : n ≤ 16) (hG : ∀ l < G.size, Rep n G[l]! (gg l)) (hGp : Gp.length = G.size)
    (hGv : ∀ l < G.size, Gp.getD l 0 = pk (gg l)) (cap : Nat) :
    let s := Id.run (forIn (List.range' 0 cap) (initSt n (idT n))
      (outerBody n (fun l y => compT n y G[l]!) G.size))
    (∃ h', CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h' 0 s) ∧
      SimA n s.2.1 (clRun n 4 (mask 4) Gp cap 0 [pk (1 : Equiv.Perm (Fin n))]) := by
  have hn32 : n < 2 ^ 32 := by omega
  have hroot : ∃ σ : Equiv.Perm (Fin n), Rep n (idT n) σ := ⟨1, Rep.idT hn32⟩
  have hinit : SimA n (initSt n (idT n)).2.1 [pk (1 : Equiv.Perm (Fin n))] := by
    refine ⟨by simp [initSt], fun i hi σ hσ => ?_⟩
    have hi0 : i = 0 := by simp [initSt] at hi; omega
    subst hi0
    have h1 : σ = 1 := CFSG.KS.ClassOne.rep_unique hσ (by simpa [initSt] using Rep.idT (G := Equiv.Perm (Fin n)) hn32)
    rw [h1]
    rfl
  refine forIn_range'_done cap 0 (initSt n (idT n)) (outerBody n (fun l y => compT n y G[l]!) G.size)
    (fun j s => j ≤ s.2.1.size ∧ CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) j 0 s ∧ ∃ E, SimA n s.2.1 E ∧
        clRun n 4 (mask 4) Gp (cap - j) j E =
          clRun n 4 (mask 4) Gp cap 0 [pk (1 : Equiv.Perm (Fin n))])
    (fun s => (∃ h', CInv n G.size (fun l y => compT n y G[l]!) (idT n)
      (fun T => ∃ σ : Equiv.Perm (Fin n), Rep n T σ) h' 0 s) ∧
      SimA n s.2.1 (clRun n 4 (mask 4) Gp cap 0 [pk (1 : Equiv.Perm (Fin n))]))
    (fun j hj s hP => ?_) (fun s hP => ?_)
    ⟨Nat.zero_le _, cinv_init hroot, _, hinit, rfl⟩
  · obtain ⟨hjs, hI, E, hS, hE⟩ := hP
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge j s.2.1.size with a | a
    · have hin := cinv_inner (good_step hG) hI a
      have hsim := sim_inner hn hG hGp hGv hI a hS
      refine Or.inl ⟨_, by simp [outerBody, a], by omega, hin.1, _, hsim.1, ?_⟩
      rw [← hE, show cap - j = cap - (j + 1) + 1 by omega, clRun_succ, if_pos (hS.1 ▸ a)]
    · refine Or.inr ⟨s, by simp [outerBody, show ¬ j < s.2.1.size by omega], ⟨j, hI⟩, ?_⟩
      rw [← hE, clRun_ge _ _ _ _ _ _ (by rw [hS.1]; exact a)]
      exact hS
  · obtain ⟨-, hI, E, hS, hE⟩ := hP
    refine ⟨⟨cap, hI⟩, ?_⟩
    rw [← hE, Nat.sub_self]
    exact hS

theorem mulClosure_sim (hn : n ≤ 16) (hG : ∀ l < G.size, Rep n G[l]! (gg l))
    (hGp : Gp.length = G.size) (hGv : ∀ l < G.size, Gp.getD l 0 = pk (gg l)) (cap : Nat) :
    mulTreeOK n G (mulClosure n G cap).1 (mulClosure n G cap).2.1 (mulClosure n G cap).2.2 = true ∧
      keysDistinct n (mulClosure n G cap).1.toList = true ∧
      SimA n (mulClosure n G cap).1 (closP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) Gp cap) ∧
      ∀ i < (mulClosure n G cap).1.size, ∃ σ : Equiv.Perm (Fin n), Rep n (mulClosure n G cap).1[i]! σ := by
  have hO := sim_outer hn hG hGp hGv cap
  rw [mulClosure_eq]
  unfold keyBfs
  generalize Id.run (forIn (List.range' 0 cap) (initSt n (idT n))
    (outerBody n (fun l y => compT n y G[l]!) G.size)) = s at hO
  obtain ⟨⟨h', a1, a2, a3, a4, a5, a6, -, a8, -⟩, hS⟩ := hO
  refine ⟨?_, ?_, hS, a5⟩
  · unfold mulTreeOK
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨a1, by rw [a4]; exact CFSG.KS.ClassOne.tblEq_refl _⟩, allIn_eq_true.2 fun k hk1 hk2 => ?_⟩
    obtain ⟨t1, t2, t3⟩ := a8 k (by omega) hk2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨t1, t2⟩, ?_⟩
    have t3' : s.2.1[k]! = compT n s.2.1[s.2.2.1[k]!]! G[s.2.2.2[k]!]! := t3
    rw [← t3']
    exact CFSG.KS.ClassOne.tblEq_refl _
  · apply CFSG.KS.Tbl.keysDistinct_of_nodup
    rw [List.nodup_iff_injective_get]
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at hij
    have hi : (i : Nat) < s.2.1.size := by simpa using i.2
    have hj : (j : Nat) < s.2.1.size := by simpa using j.2
    exact Fin.ext (a6 i hi j hj (by simpa [getElem!_pos, hi, hj] using hij))

end

theorem sylowAutP_sound (hn : n ≤ 16) (a b z : Equiv.Perm (Fin n)) (ds es : List (List Int))
    (cap N k : Nat)
    (h : sylowAutP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk a) (pk a⁻¹) (pk b) (pk b⁻¹) ds es
      (pk z) (pk z⁻¹) cap N k = true) :
    sylowAutOK n (toTable a) (toTable b) ds es (toTable z) cap N k = true := by
  have hn32 : n < 2 ^ 32 := by omega
  have ha := rep_toTable hn32 a
  have hb := rep_toTable hn32 b
  have hz := rep_toTable hn32 z
  have hVr := rep_tblSlp' hn32 ha hb ds
  obtain ⟨gg, hgg⟩ : ∃ gg : Nat → Equiv.Perm (Fin n),
      ∀ l, gg l = wordValue (slpVals a b ds) (es.getD l []) := ⟨_, fun _ => rfl⟩
  have hGsize : (sylowGens n (toTable a) (toTable b) ds es).size = es.length := by
    simp [sylowGens]
  have hG : ∀ l < (sylowGens n (toTable a) (toTable b) ds es).size,
      Rep n (sylowGens n (toTable a) (toTable b) ds es)[l]! (gg l) := by
    intro l hl
    rw [hGsize] at hl
    have e : (sylowGens n (toTable a) (toTable b) ds es)[l]! =
        (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 es[l]).1 := by
      simp [sylowGens, hl]
    rw [e, hgg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    exact rep_tblWord' hn32 hVr _
  have hGp : (es.map fun e => pk (wordValue (slpVals a b ds) e)).length =
      (sylowGens n (toTable a) (toTable b) ds es).size := by simp [hGsize]
  have hGv : ∀ l < (sylowGens n (toTable a) (toTable b) ds es).size,
      (es.map fun e => pk (wordValue (slpVals a b ds) e)).getD l 0 = pk (gg l) := by
    intro l hl
    rw [hGsize] at hl
    rw [getD_eq_getElem' (by simpa using hl), List.getElem_map, hgg, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
  have hGi : ∀ l < (sylowGens n (toTable a) (toTable b) ds es).size,
      (es.map fun e => pk (wordValue (slpVals a b ds) e)⁻¹).getD l 0 = pk (gg l)⁻¹ := by
    intro l hl
    rw [hGsize] at hl
    rw [getD_eq_getElem' (by simpa using hl), List.getElem_map, hgg, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
  obtain ⟨htree, hkeys, hsim, hgood⟩ := mulClosure_sim hn hG hGp hGv cap
  unfold sylowAutP at h
  simp only [strictB_eq, slpP_pk hn, exprsV_pk hn, exprsI_pk hn, bAnd_eq, Bool.and_eq_true,
    Nat.beq_eq] at h
  obtain ⟨-, -, -, hcl1, hcl2, -, hlen, hN1, hN2, hma, hmz, hcomm⟩ := h
  simp only [sylowAutOK, Bool.and_eq_true, beq_iff_eq, and_assoc]
  set G := sylowGens n (toTable a) (toTable b) ds es with hGdef
  set C := mulClosure n G cap with hCdef
  set Gp := es.map fun e => pk (wordValue (slpVals a b ds) e) with hGpdef
  set E := closP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) Gp cap with hEdef
  have hK : Nat.shiftLeft 1 k = 2 ^ k := (Nat.shiftLeft_eq 1 k).trans (one_mul _)
  have memE : ∀ σ : Equiv.Perm (Fin n), pk σ ∈ E → ∃ j, ∃ hj : j < C.1.size, Rep n C.1[j] σ := by
    intro σ hm
    obtain ⟨j, hj, hjE⟩ := List.getElem_of_mem hm
    have hj' : j < C.1.size := hsim.1 ▸ hj
    obtain ⟨τ, hτ⟩ := hgood j hj'
    have := hsim.2 j hj' τ hτ
    rw [getD_eq_getElem' hj, hjE] at this
    rw [getElem!_pos C.1 j hj', ← pk_inj hn this] at hτ
    exact ⟨j, hj', hτ⟩
  have inE : ∀ i < C.1.size, ∀ σ : Equiv.Perm (Fin n), Rep n C.1[i]! σ → pk σ ∈ E := by
    intro i hi σ hσ
    have := hsim.2 i hi σ hσ
    rw [getD_eq_getElem' (hsim.1 ▸ hi)] at this
    rw [← this]
    exact List.getElem_mem _
  have hGpm : ∀ l < G.size, pk (gg l) ∈ Gp := by
    intro l hl
    rw [← hGv l hl, getD_eq_getElem' (hGp ▸ hl)]
    exact List.getElem_mem _
  have hGim : ∀ l < G.size, pk (gg l)⁻¹ ∈ es.map fun e => pk (wordValue (slpVals a b ds) e)⁻¹ := by
    intro l hl
    rw [← hGi l hl, getD_eq_getElem' (by simpa [hGsize] using hl)]
    exact List.getElem_mem _
  have hInvG : ∀ l < G.size, (G.map (invT n))[l]! = invT n G[l]! := by
    intro l hl
    rw [getElem!_pos (G.map (invT n)) l (by simpa using hl), getElem!_pos G l hl, Array.getElem_map]
  refine ⟨tblSlp_ok hn32 ha hb ds, List.all_eq_true.2 fun e _ => tblWord_flag hn32 hVr e,
    List.all_eq_true.2 fun i hi => ?_, htree, ?_, hkeys, ?_, ?_, ?_, ?_, ?_, ?_,
    CFSG.KS.Tbl.invOK_invT hn32 hz⟩
  · rw [List.mem_range] at hi
    rw [hInvG i hi]
    exact CFSG.KS.Tbl.invOK_invT hn32 (hG i hi)
  · unfold mulClosedOK
    rw [Array.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro l hl
    rw [List.mem_range] at hl
    obtain ⟨σ, hσ⟩ := hgood i hi
    have hσE := inE i hi σ hσ
    rw [getElem!_pos C.1 i hi] at hσ
    rw [Bool.and_eq_true, Array.any_eq_true, Array.any_eq_true]
    constructor
    · have := (allL_iff _ _).1 ((allL_iff _ _).1 hcl1 _ hσE) _ (hGpm l hl)
      rw [memB_iff, pk_mul hn] at this
      obtain ⟨j, hj, hjr⟩ := memE _ this
      exact ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hjr (Rep.compT hσ (hG l hl))).2 rfl⟩
    · have := (allL_iff _ _).1 ((allL_iff _ _).1 hcl2 _ hσE) _ (hGim l hl)
      rw [memB_iff, pk_mul hn] at this
      obtain ⟨j, hj, hjr⟩ := memE _ this
      refine ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hjr (Rep.compT hσ ?_)).2 rfl⟩
      rw [hInvG l hl]
      exact CFSG.KS.Tbl.invT_rep hn32 (hG l hl)
  · rw [← hsim.1, hlen, hK]
  · rw [← hK]
    exact hN1
  · rw [← hK]
    exact hN2
  · obtain ⟨j, hj, hjr⟩ := memE a ((memB_iff _ _).1 hma)
    exact Array.any_eq_true.2 ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hjr ha).2 rfl⟩
  · obtain ⟨j, hj, hjr⟩ := memE z ((memB_iff _ _).1 hmz)
    exact Array.any_eq_true.2 ⟨j, hj, (CFSG.KS.Tbl.tblEq_iff_eq hz hjr).2 rfl⟩
  · refine Array.all_eq_true.2 fun i hi => ?_
    have hGi' : Rep n G[i] (gg i) := by
      have := hG i hi
      rwa [getElem!_pos G i hi] at this
    have := (allL_iff _ _).1 hcomm _ (hGpm i hi)
    rw [Nat.beq_eq, pk_mul hn, pk_mul hn] at this
    rw [commT, CFSG.KS.Tbl.tblEq_iff_eq (Rep.compT hz hGi') (Rep.compT hGi' hz)]
    exact pk_inj hn this

theorem survF_sound (hn : n ≤ 16) (Q : RawSchreierDatum n) (a b z : Equiv.Perm (Fin n))
    (ds es : List (List Int)) {r s mb : Nat} (hr : 0 < r) (hs : 0 < s) (hmb : 0 < mb)
    (h : ∀ g ∈ enumeration Q, survF n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk a) (pk a⁻¹)
      (pk b) (pk (z * b * z⁻¹)) ds es
      (exprsV n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n)))
        (slpP n 4 (mask 4) (pk (1 : Equiv.Perm (Fin n))) (pk a) (pk a⁻¹) (pk b) (pk b⁻¹) ds) es)
      r s mb (pk g) = 0) :
    survivorsOK n (toTable a) (toTable b) (toTable z) ds es r s mb (orderTables Q mb) = true := by
  have hn32 : n < 2 ^ 32 := by omega
  have ha := rep_toTable hn32 a
  have hb := rep_toTable hn32 b
  have hz := rep_toTable hn32 z
  simp only [survivorsOK, List.all_eq_true]
  intro y hy
  obtain ⟨g, hg, hyg⟩ := exists_of_forall₂ (forall₂_orderTables hn32 Q hmb) y hy
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hg
  obtain ⟨hgQ, hgo⟩ := hg
  have hV := rep_tblSlp' hn32 ha hyg ds
  have hVb := rep_tblSlp' hn32 ha hb ds
  have hgi := pow_pred_eq_inv hgo hmb
  by_cases hp : pairTest n r s 2 mb (toTable a) y = true
  swap
  · simp [hp]
  have hcw : List.Forall₂ (Rep n) (commWord (toTable a) y 2 mb)
      (a :: g :: (List.replicate (2 - 1) a ++ List.replicate (mb - 1) g)) :=
    .cons ha (.cons hyg (forall₂_append (forall₂_replicate ha _) (forall₂_replicate hyg _)))
  have hpo := hp
  rw [pairTest, Bool.and_eq_true, ordW_iff perm_faithful (.cons ha (.cons hyg .nil)) hr,
    ordW_iff perm_faithful hcw hs] at hpo
  simp only [List.prod_cons, List.prod_nil, mul_one, Nat.reduceSub, List.replicate_one,
    List.singleton_append, List.prod_replicate, hgi] at hpo
  have hF := h g hgQ
  unfold survF at hF
  have hgi' : g ^ (Nat.sub mb 1) = g⁻¹ := hgi
  rw [powP_pk hn, hgi'] at hF
  simp only [pk_mul hn, slpP_pk hn, exprsV_pk hn, nIf_eq, bAnd_eq, bIf_eq, Bool.and_eq_true,
    ordExP_pk hn _ hmb, ordExP_pk hn _ hr, ordExP_pk hn _ hs, beq_pk_iff hn] at hF
  have hall : ∀ q : Bool, q = true ∨ q = false := fun q => by cases q <;> simp
  simp only [hp, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨tblSlp_ok hn32 ha hyg ds, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro q hq
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hq
    exact tblWord_flag hn32 hV e
  by_cases hall2 : (((es.map (tblWord n (tblSlp n (toTable a) y ds).1)).zip
      (sylowGens n (toTable a) (toTable b) ds es).toList).all fun q => tblEq n q.1.1 q.2) = true
  swap
  · exact Or.inl (Or.inl (Bool.eq_false_iff.2 hall2))
  rw [show (sylowGens n (toTable a) (toTable b) ds es).toList =
      es.map (fun e => (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 e).1) by
    simp [sylowGens]] at hall2
  have heq : ∀ e ∈ es, wordValue (slpVals a g ds) e = wordValue (slpVals a b ds) e := by
    have := all_zip_map (tblWord n (tblSlp n (toTable a) y ds).1)
      (fun e => (tblWord n (tblSlp n (toTable a) (toTable b) ds).1 e).1)
      (fun q p => tblEq n q.1 p) es hall2
    intro e he
    exact (CFSG.KS.Tbl.tblEq_iff_eq (rep_tblWord' hn32 hV e) (rep_tblWord' hn32 hVb e)).1
      (this e he)
  have hA := allEqP_map (fun e => pk (wordValue (slpVals a g ds) e))
    (fun e => pk (wordValue (slpVals a b ds) e)) es fun e he => by rw [heq e he]
  have hgb : g = b ∨ g = z * b * z⁻¹ := by
    by_contra hc
    push Not at hc
    simp [hgo, hpo.1, hpo.2, hA, hc.1, hc.2] at hF
  rcases hgb with rfl | rfl
  · exact Or.inl (Or.inr ((CFSG.KS.Tbl.tblEq_iff_eq hyg hb).2 rfl))
  · exact Or.inr ((CFSG.KS.Tbl.tblEq_iff_eq hyg
      (rep_conjT hz (CFSG.KS.Tbl.invT_rep hn32 hz) hb)).2 rfl)

end CFSG.KS.MSyl

end
