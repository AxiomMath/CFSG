module

public import Certificates.Data.Kernel.Spor.ONNQK
public import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ONNQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words

@[expose] def wd (v : Nat) : List Int := decW (Nat.shiftRight v 8) (Nat.land v 255)

@[expose] def winv (w : List Int) : List Int := w.reverse.map fun z => -z

@[expose] noncomputable def ev (TT UU : Nat → Nat → Nat) (b : Nat) (w : List Int) (x : Nat) :
    Nat :=
  w.foldr (fun z y => GZ (actT TT b) (actT UU b) z y) x

@[expose] def codesFrom (W k : Nat) : Nat → List Nat
  | 0 => []
  | L + 1 => (W >>> (4 * (k + L))) % 16 :: codesFrom W k L

@[expose] def wlw (D : Nat → Nat) (a i c : Nat) : List Int :=
  if c / 2 < 4 then (if c % 2 = 0 then wd (D (36 + c / 2)) else winv (wd (D (36 + c / 2))))
  else if c % 2 = 0 then wd (D (a + 1)) ++ wd (D (40 + i))
  else winv (wd (D (40 + i))) ++ winv (wd (D (a + 1)))

@[expose] def wcodes (D : Nat → Nat) (a i : Nat) : List Nat :=
  codesFrom (Nat.shiftRight (D (496 + (a * 456 + i))) 8) 0 (Nat.land (D (496 + (a * 456 + i))) 255)

@[expose] def wit (D : Nat → Nat) (a i : Nat) : List Int := (wcodes D a i).flatMap (wlw D a i)

variable {TT UU : Nat → Nat → Nat}

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem rN (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by cases c <;> rfl

private theorem land1 (c : Nat) : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c

private theorem shr1 (c : Nat) : Nat.shiftRight c 1 = c / 2 := by
  simp [Nat.shiftRight_eq_div_pow]

private theorem fld15 (W k : Nat) : Nat.land (Nat.shiftRight W (Nat.mul 4 k)) 15 = (W >>> (4 * k)) % 16 := by
  have h15 : (15 : Nat) = 2 ^ 4 - 1 := rfl
  rw [h15]
  exact Nat.and_two_pow_sub_one_eq_mod _ 4

theorem ev_append (b : Nat) (u w : List Int) (x : Nat) :
    ev TT UU b (u ++ w) x = ev TT UU b u (ev TT UU b w x) := by
  unfold ev
  rw [List.foldr_append]

theorem trV_eq (b v x : Nat) : trV TT UU b v x = ev TT UU b (wd v) x :=
  trace_eq _ _ _ _ _

private theorem stepR (T U : Nat → Nat → Nat) (c v : Nat) :
    nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), U (Nat.shiftRight c (nat_lit 1)) v,
      T (Nat.shiftRight c (nat_lit 1)) v) = GZ T U (-letterOfCode c) v := by
  unfold GZ letterOfCode
  rw [land1, shr1]
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [h]
    have hn : ¬ (0 : Int) < -((c / 2 + 1 : Nat) : Int) := by omega
    have e : (-(-((c / 2 + 1 : Nat) : Int))).toNat - 1 = c / 2 := by omega
    simp only [ite_true, hn, e]
    rfl
  · rw [h]
    have hp : (0 : Int) < -(-((c / 2 + 1 : Nat) : Int)) := by omega
    have e : (-(-((c / 2 + 1 : Nat) : Int))).toNat - 1 = c / 2 := by omega
    simp only [Nat.one_ne_zero, ite_false, hp, e]
    rfl

theorem traceR_eq (T U : Nat → Nat → Nat) (W : Nat) :
    ∀ L x, traceR T U W L x = (winv (decW W L)).foldr (fun z y => GZ T U z y) x
  | 0, x => rfl
  | L + 1, x => by
    change strictN (fld(W, Nat.mul (nat_lit 4) L, nat_lit 15)) (fun c =>
      strictN (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), U (Nat.shiftRight c (nat_lit 1)) x,
        T (Nat.shiftRight c (nat_lit 1)) x)) (traceR T U W L)) = _
    rw [sN, sN, stepR, traceR_eq T U W L, fld15]
    simp only [decW, winv, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.foldr_append, List.foldr_cons, List.foldr_nil]

theorem trVR_eq (b v x : Nat) : trVR TT UU b v x = ev TT UU b (winv (wd v)) x :=
  traceR_eq _ _ _ _ _

theorem codesFrom_succ (W : Nat) : ∀ (L k : Nat),
    codesFrom W k (L + 1) = codesFrom W (k + 1) L ++ [(W >>> (4 * k)) % 16]
  | 0, k => by simp [codesFrom]
  | L + 1, k => by
    rw [codesFrom, codesFrom_succ W L k, codesFrom]
    simp only [List.cons_append]
    rw [show k + 1 + L = k + (L + 1) by omega]

private theorem nSel_lt (D : Nat → Nat) {k : Nat} (hk : k < 4) :
    nSel (D 36) (D 37) (D 38) (D 39) k = D (36 + k) := by
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem wLet_eq (D : Nat → Nat) (a i b c x : Nat) :
    wLet TT UU (nSel (D 36) (D 37) (D 38) (D 39)) (D (a + 1)) (D (40 + i)) b c x =
      ev TT UU b (wlw D a i c) x := by
  unfold wLet wlw
  simp only [sN, rN, shr1, land1, Nat.blt_eq, Nat.beq_eq, trV_eq, trVR_eq]
  by_cases h4 : c / 2 < 4
  · rw [nSel_lt D h4]
    by_cases h2 : c % 2 = 0 <;> simp [h4, h2]
  · by_cases h2 : c % 2 = 0 <;> simp [h4, h2, ev_append]

theorem wTr_gen (D : Nat → Nat) (a i b W : Nat) : ∀ (L k v : Nat),
    Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
      (fun _ ih k v => strictN (fld(W, Nat.mul (nat_lit 4) k, nat_lit 15)) fun c =>
        strictN (wLet TT UU (nSel (D 36) (D 37) (D 38) (D 39)) (D (a + 1)) (D (40 + i)) b c v)
          fun v' => ih (Nat.succ k) v') L k v =
      ev TT UU b ((codesFrom W k L).flatMap (wlw D a i)) v
  | 0, k, v => rfl
  | L + 1, k, v => by
    simp only []
    rw [sN, sN, wTr_gen D a i b W L (k + 1), codesFrom_succ, List.flatMap_append,
      ev_append, wLet_eq, fld15]
    simp

theorem wTr_eq (D : Nat → Nat) (a i b W L x : Nat) :
    wTr TT UU (nSel (D 36) (D 37) (D 38) (D 39)) (D (a + 1)) (D (40 + i)) b W L x =
      ev TT UU b ((codesFrom W 0 L).flatMap (wlw D a i)) x :=
  wTr_gen D a i b W L 0 x

theorem headOK_sound {D : Nat → Nat} {l2 : Nat} (h : headOK TT UU D l2 = true) :
    ev TT UU 0 (wd (D 18740)) 0 = l2 ∧ ev TT UU 0 (wd (D 0)) 0 = 0 ∧
      (∀ k < 4, ev TT UU 1 (wd (D (36 + k))) l2 = l2) ∧ ev TT UU 1 (wd (D 40)) l2 = l2 ∧
      ev TT UU 1 (wd (D 41)) l2 ≠ l2 := by
  unfold headOK at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  refine ⟨?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [← trV_eq]
    exact Nat.eq_of_beq_eq_true h1
  · rw [← trV_eq]
    exact Nat.eq_of_beq_eq_true h2
  · have := allBlk_spec h3 k hk
    rw [show Nat.add 0 k = k from Nat.zero_add k] at this
    rw [← trV_eq]
    exact Nat.eq_of_beq_eq_true this
  · rw [← trV_eq]
    exact Nat.eq_of_beq_eq_true h4
  · rw [← trV_eq]
    intro e
    change (!Nat.beq (trV TT UU 1 (D 41) l2) l2) = true at h5
    rw [e] at h5
    simp at h5

@[expose] noncomputable def dep (FR : Nat → Nat) (y : Nat) : Nat := fld(FR y, nat_lit 17, nat_lit 15)

theorem fstAt_sound {D FR : Nat → Nat} {n : Nat} (h : ∀ y < n, fstAt TT UU D FR n y = true) :
    ∀ y < n, ∃ ks : List Nat, (∀ k ∈ ks, k < 4) ∧ ∃ a < 36,
      y = ks.foldr (fun k z => ev TT UU 0 (wd (D (36 + k))) z) (ev TT UU 0 (wd (D a)) 0) := by
  suffices H : ∀ d, ∀ y < n, dep FR y = d → ∃ ks : List Nat, (∀ k ∈ ks, k < 4) ∧ ∃ a < 36,
      y = ks.foldr (fun k z => ev TT UU 0 (wd (D (36 + k))) z) (ev TT UU 0 (wd (D a)) 0) from
    fun y hy => H _ y hy rfl
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro y hy hd
    have hf := h y hy
    unfold fstAt at hf
    simp only [sB] at hf
    change Bool.rec (motive := fun _ => Bool)
      (bAnd(Nat.blt (Nat.shiftRight (FR y) 21) 4, bAnd(Nat.blt (Nat.land (FR y) 131071) n,
        bAnd(Nat.blt (dep FR (Nat.land (FR y) 131071)) (dep FR y),
          Nat.beq (trV TT UU 0 (D (36 + Nat.shiftRight (FR y) 21)) (Nat.land (FR y) 131071)) y))))
      (bAnd(Nat.blt (Nat.shiftRight (FR y) 21) 36,
        Nat.beq (trV TT UU 0 (D (Nat.shiftRight (FR y) 21)) 0) y))
      (Nat.beq (dep FR y) 0) = true at hf
    cases hb : Nat.beq (dep FR y) 0 <;> rw [hb] at hf <;> dsimp only at hf
    · obtain ⟨hl, hf⟩ := (bAnd_iff _ _).1 hf
      obtain ⟨hp, hf⟩ := (bAnd_iff _ _).1 hf
      obtain ⟨hdp, hf⟩ := (bAnd_iff _ _).1 hf
      have e := Nat.eq_of_beq_eq_true hf
      rw [trV_eq] at e
      obtain ⟨ks, hks, a, ha, ep⟩ := ih _ (by rw [← hd]; exact Nat.blt_eq.mp hdp) _ (Nat.blt_eq.mp hp) rfl
      refine ⟨Nat.shiftRight (FR y) 21 :: ks, ?_, a, ha, ?_⟩
      · intro k hk
        rcases List.mem_cons.1 hk with e' | e'
        · rw [e']
          exact Nat.blt_eq.mp hl
        · exact hks k e'
      · rw [List.foldr_cons, ← ep]
        exact e.symm
    · obtain ⟨hl, hf⟩ := (bAnd_iff _ _).1 hf
      have e := Nat.eq_of_beq_eq_true hf
      rw [trV_eq] at e
      exact ⟨[], fun k hk => absurd hk (List.not_mem_nil), _, Nat.blt_eq.mp hl, e.symm⟩

theorem cosAt_sound {D : Nat → Nat} {l2 : Nat} (h : ∀ i < 456, cosAt TT UU D l2 i = true) :
    ∀ i < 456, ∀ q < 4, ∃ j < 456,
      ev TT UU 1 (wd (D (18736 + q))) (ev TT UU 1 (wd (D (40 + i))) l2) =
        ev TT UU 1 (wd (D (40 + j))) l2 := by
  have ht : ∀ i < 456, ev TT UU 1 (wd (D (40 + i))) l2 = D (16456 + i) ∧
      ∀ q < 4, D (16912 + (4 * i + q)) < 456 ∧
        ev TT UU 1 (wd (D (18736 + q))) (D (16456 + i)) = D (16456 + D (16912 + (4 * i + q))) := by
    intro i hi
    have hc := h i hi
    unfold cosAt at hc
    rw [sB] at hc
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hc
    rw [sB, trV_eq] at h1
    refine ⟨Nat.eq_of_beq_eq_true h1, fun q hq => ?_⟩
    have h3 := allBlk_spec h2 q hq
    rw [show Nat.add 0 q = q from Nat.zero_add q, sB] at h3
    obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h3
    rw [sB, trV_eq] at h5
    exact ⟨Nat.blt_eq.mp h4, Nat.eq_of_beq_eq_true h5⟩
  intro i hi q hq
  obtain ⟨e1, hq'⟩ := ht i hi
  obtain ⟨hj, e2⟩ := hq' q hq
  refine ⟨_, hj, ?_⟩
  rw [e1, e2, (ht _ hj).1]

theorem witAt_sound {D : Nat → Nat} {l2 : Nat} (h : ∀ j < 15960, witAt TT UU D l2 j = true) :
    ∀ a < 35, ∀ i < 456,
      (ev TT UU 0 (wit D a i) 0 = 0 ∧ ev TT UU 1 (wit D a i) l2 ≠ l2) ∨
        (ev TT UU 1 (wit D a i) l2 = l2 ∧ ev TT UU 0 (wit D a i) 0 ≠ 0) := by
  intro a ha i hi
  have hw := h (a * 456 + i) (by omega)
  have e1 : (a * 456 + i) / 456 = a := by omega
  have e2 : (a * 456 + i) % 456 = i := by omega
  unfold witAt at hw
  simp only [sB] at hw
  change Bool.rec (motive := fun _ => Bool)
    (Nat.beq (wTr TT UU (nSel (D 36) (D 37) (D 38) (D 39)) (D ((a * 456 + i) / 456 + 1))
      (D (40 + (a * 456 + i) % 456)) 1 (Nat.shiftRight (D (496 + (a * 456 + i))) 8)
      (Nat.land (D (496 + (a * 456 + i))) 255) l2) l2)
    (Bool.not (Nat.beq (wTr TT UU (nSel (D 36) (D 37) (D 38) (D 39)) (D ((a * 456 + i) / 456 + 1))
      (D (40 + (a * 456 + i) % 456)) 1 (Nat.shiftRight (D (496 + (a * 456 + i))) 8)
      (Nat.land (D (496 + (a * 456 + i))) 255) l2) l2))
    (Nat.beq (wTr TT UU (nSel (D 36) (D 37) (D 38) (D 39)) (D ((a * 456 + i) / 456 + 1))
      (D (40 + (a * 456 + i) % 456)) 0 (Nat.shiftRight (D (496 + (a * 456 + i))) 8)
      (Nat.land (D (496 + (a * 456 + i))) 255) 0) 0) = true at hw
  rw [e1, e2, wTr_eq, wTr_eq] at hw
  change Bool.rec (motive := fun _ => Bool) (Nat.beq (ev TT UU 1 (wit D a i) l2) l2)
    (Bool.not (Nat.beq (ev TT UU 1 (wit D a i) l2) l2))
    (Nat.beq (ev TT UU 0 (wit D a i) 0) 0) = true at hw
  cases hb : Nat.beq (ev TT UU 0 (wit D a i) 0) 0 <;> rw [hb] at hw <;> dsimp only at hw
  · refine Or.inr ⟨Nat.eq_of_beq_eq_true hw, fun e => ?_⟩
    rw [e] at hb
    exact absurd hb (by decide)
  · refine Or.inl ⟨Nat.eq_of_beq_eq_true hb, fun e => ?_⟩
    rw [e] at hw
    exact absurd hw (by simp)

end CFSG.KS.ONNQ

end
