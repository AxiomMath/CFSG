module

public import Certificates.Data.Kernel.Misc.HexDrop

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text

@[expose] noncomputable def runBody (d n w N : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v acc : Nat) : Bool :=
  bIf(Nat.beq j N, true,
      strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
        strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) d,
          bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
            strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
              bIf(Nat.beq (Nat.succ e) n,
                bAnd(Nat.beq acc' (F j),
                  ih (Nat.succ j) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
                ih j (Nat.succ e) (nat_lit 0) (nat_lit 0) acc')),
            false),
          ih j e (Nat.succ t) v' acc)),
        false)))

theorem run_cons (d n w N : Nat) (F : Nat → Nat) (ch : Char) (cs : List Char) :
    run d n w N F (ch :: cs) = runBody d n w N F ch (run d n w N F cs) := rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem runBody_mono {d n w N : Nat} {F : Nat → Nat} {ch : Char}
    {f g : Nat → Nat → Nat → Nat → Nat → Bool}
    (hfg : ∀ j e t v acc, f j e t v acc = true → g j e t v acc = true) {j e t v acc : Nat}
    (h : runBody d n w N F ch f j e t v acc = true) : runBody d n w N F ch g j e t v acc = true := by
  unfold runBody at h ⊢
  simp only [strictB_eq'] at h ⊢
  revert h
  cases Nat.beq j N
  · cases Nat.blt (hexV (Char.toNat ch)) 16
    · exact id
    · cases Nat.beq (Nat.succ t) d
      · exact hfg _ _ _ _ _
      · cases Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w)
        · exact id
        · cases Nat.beq (Nat.succ e) n
          · exact hfg _ _ _ _ _
          · cases Nat.beq (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16)
              (hexV (Char.toNat ch))) (Nat.mul w e))) (F j)
            · exact id
            · exact hfg _ _ _ _ _
  · exact id

@[expose] noncomputable def runTo (d n w N : Nat) (F : Nat → Nat) (J E T V A : Nat) :
    Nat → List Char → Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => List Char → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ j e t v acc => bAnd(Nat.beq j J, bAnd(Nat.beq e E, bAnd(Nat.beq t T,
      bAnd(Nat.beq v V, Nat.beq acc A)))))
    (fun _ ih cs => List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
      (fun _ _ _ _ _ => false) (fun ch cs' _ => runBody d n w N F ch (ih cs')) cs)

theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem bAnd_true_iff {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem run_split {d n w N : Nat} {F : Nat → Nat} {J E T V A : Nat} :
    ∀ (m : Nat) (cs : List Char) (j e t v acc : Nat),
      runTo d n w N F J E T V A m cs j e t v acc = true →
      run d n w N F (dropL m cs) J E T V A = true → run d n w N F cs j e t v acc = true
  | 0, cs, j, e, t, v, acc, h, hr => by
    have h' : bAnd(Nat.beq j J, bAnd(Nat.beq e E, bAnd(Nat.beq t T,
      bAnd(Nat.beq v V, Nat.beq acc A)))) = true := h
    obtain ⟨h1, h'⟩ := bAnd_true h'
    obtain ⟨h2, h'⟩ := bAnd_true h'
    obtain ⟨h3, h'⟩ := bAnd_true h'
    obtain ⟨h4, h5⟩ := bAnd_true h'
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
      Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5]
    have e0 : dropL 0 cs = cs := by cases cs <;> rfl
    rw [e0] at hr
    exact hr
  | m + 1, [], _, _, _, _, _, h, _ => Bool.noConfusion h
  | m + 1, ch :: cs, j, e, t, v, acc, h, hr => by
    rw [run_cons]
    have h' : runBody d n w N F ch (runTo d n w N F J E T V A m cs) j e t v acc = true := h
    have hr' : run d n w N F (dropL m cs) J E T V A = true := hr
    exact runBody_mono (fun j e t v acc hp => run_split m cs j e t v acc hp hr') h'

theorem run_split' {d n w N : Nat} {F : Nat → Nat} {J E T V A m : Nat} {cs cs' : List Char}
    {j e t v acc : Nat} (h : runTo d n w N F J E T V A m cs j e t v acc = true)
    (hd : dropL m cs = cs') (hr : run d n w N F cs' J E T V A = true) :
    run d n w N F cs j e t v acc = true :=
  run_split m cs j e t v acc h (hd ▸ hr)

theorem hexFlat_of_run {cs : List Char} {d n w N : Nat} {F : Nat → Nat}
    (hd : Nat.blt (nat_lit 0) d = true) (hn : Nat.blt (nat_lit 0) n = true)
    (h : run d n w N F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) = true) :
    hexFlat cs d n w N F = true := by
  unfold hexFlat
  rw [hd, hn, h]

end CFSG.KC.Misc.HexFlat

namespace CFSG.KS.Text

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.HexFlat

@[expose] noncomputable def runBody (wd n w _lines start cnt : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (L e t v acc : Nat) : Bool :=
  strictB (Char.toNat ch) (fun c =>
      bIf(Nat.blt e n,
        strictB (hexV c) (fun h => bIf(Nat.blt h (nat_lit 16),
          strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
          bIf(Nat.beq (Nat.succ t) wd,
            bIf(Nat.blt v' (Nat.shiftLeft (nat_lit 1) w),
              strictB (Nat.lor acc (Nat.shiftLeft v' (Nat.mul w e))) (fun acc' =>
                ih L (Nat.succ e) (nat_lit 0) (nat_lit 0) acc'),
              false),
            ih L e (Nat.succ t) v' acc)),
          false)),
        bIf(Nat.beq c (nat_lit 10),
          bAnd(bIf(Nat.ble start L, bIf(Nat.blt L (Nat.add start cnt),
              Nat.beq acc (F (Nat.sub L start)), true), true),
            ih (Nat.succ L) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
          false)))

theorem run_cons (wd n w lines start cnt : Nat) (F : Nat → Nat) (ch : Char) (cs : List Char) :
    run wd n w lines start cnt F (ch :: cs) = runBody wd n w lines start cnt F ch
      (run wd n w lines start cnt F cs) := rfl

theorem runBody_mono {wd n w lines start cnt : Nat} {F : Nat → Nat} {ch : Char}
    {f g : Nat → Nat → Nat → Nat → Nat → Bool}
    (hfg : ∀ L e t v acc, f L e t v acc = true → g L e t v acc = true) {L e t v acc : Nat}
    (h : runBody wd n w lines start cnt F ch f L e t v acc = true) :
    runBody wd n w lines start cnt F ch g L e t v acc = true := by
  unfold runBody at h ⊢
  simp only [strictB_eq'] at h ⊢
  revert h
  cases Nat.blt e n
  · cases Nat.beq (Char.toNat ch) 10
    · exact id
    · cases Nat.ble start L
      · dsimp only
        first
        | exact hfg _ _ _ _ _
        | intro h
          obtain ⟨h1, h2⟩ := bAnd_true h
          exact bAnd_true_iff.2 ⟨h1, hfg _ _ _ _ _ h2⟩
      · cases Nat.blt L (Nat.add start cnt)
        · dsimp only
          first
          | exact hfg _ _ _ _ _
          | intro h
            obtain ⟨h1, h2⟩ := bAnd_true h
            exact bAnd_true_iff.2 ⟨h1, hfg _ _ _ _ _ h2⟩
        · dsimp only
          first
          | exact hfg _ _ _ _ _
          | intro h
            obtain ⟨h1, h2⟩ := bAnd_true h
            exact bAnd_true_iff.2 ⟨h1, hfg _ _ _ _ _ h2⟩
  · cases Nat.blt (hexV (Char.toNat ch)) 16
    · exact id
    · cases Nat.beq (Nat.succ t) wd
      · exact hfg _ _ _ _ _
      · cases Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w)
        · exact id
        · exact hfg _ _ _ _ _

@[expose] noncomputable def runTo (wd n w lines start cnt : Nat) (F : Nat → Nat) (L' E T V A : Nat) :
    Nat → List Char → Nat → Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => List Char → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ L e t v acc => bAnd(Nat.beq L L', bAnd(Nat.beq e E, bAnd(Nat.beq t T,
      bAnd(Nat.beq v V, Nat.beq acc A)))))
    (fun _ ih cs => List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
      (fun _ _ _ _ _ => false) (fun ch cs' _ => runBody wd n w lines start cnt F ch (ih cs')) cs)

theorem run_split {wd n w lines start cnt : Nat} {F : Nat → Nat} {L' E T V A : Nat} :
    ∀ (m : Nat) (cs : List Char) (L e t v acc : Nat),
      runTo wd n w lines start cnt F L' E T V A m cs L e t v acc = true →
      run wd n w lines start cnt F (dropL m cs) L' E T V A = true →
      run wd n w lines start cnt F cs L e t v acc = true
  | 0, cs, L, e, t, v, acc, h, hr => by
    have h' : bAnd(Nat.beq L L', bAnd(Nat.beq e E, bAnd(Nat.beq t T,
      bAnd(Nat.beq v V, Nat.beq acc A)))) = true := h
    obtain ⟨h1, h'⟩ := bAnd_true h'
    obtain ⟨h2, h'⟩ := bAnd_true h'
    obtain ⟨h3, h'⟩ := bAnd_true h'
    obtain ⟨h4, h5⟩ := bAnd_true h'
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
      Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5]
    have e0 : dropL 0 cs = cs := by cases cs <;> rfl
    rw [e0] at hr
    exact hr
  | m + 1, [], _, _, _, _, _, h, _ => Bool.noConfusion h
  | m + 1, ch :: cs, L, e, t, v, acc, h, hr => by
    rw [run_cons]
    have h' : runBody wd n w lines start cnt F ch
      (runTo wd n w lines start cnt F L' E T V A m cs) L e t v acc = true := h
    have hr' : run wd n w lines start cnt F (dropL m cs) L' E T V A = true := hr
    exact runBody_mono (fun L e t v acc hp => run_split m cs L e t v acc hp hr') h'

theorem run_split' {wd n w lines start cnt : Nat} {F : Nat → Nat} {L' E T V A m : Nat}
    {cs cs' : List Char} {L e t v acc : Nat}
    (h : runTo wd n w lines start cnt F L' E T V A m cs L e t v acc = true)
    (hd : dropL m cs = cs') (hr : run wd n w lines start cnt F cs' L' E T V A = true) :
    run wd n w lines start cnt F cs L e t v acc = true :=
  run_split m cs L e t v acc h (hd ▸ hr)

theorem hexBind_of_run {cs : List Char} {wd n w lines start cnt : Nat} {F : Nat → Nat}
    (hd : Nat.blt (nat_lit 0) wd = true) (hc : Nat.ble (Nat.add start cnt) lines = true)
    (h : run wd n w lines start cnt F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)
      (nat_lit 0) = true) :
    hexBind cs wd n w lines start cnt F = true := by
  unfold hexBind
  rw [hd, hc, h]

end CFSG.KS.Text

end
