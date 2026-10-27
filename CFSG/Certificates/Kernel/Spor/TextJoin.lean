module

public import Certificates.Data.Kernel.Spor.Text
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.Text

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def nilC (lines : Nat) : Nat → Nat → Nat → Nat → Nat → Bool :=
  fun L e t _ _ => bAnd(Nat.beq L lines, bAnd(Nat.beq e (nat_lit 0), Nat.beq t (nat_lit 0)))

@[expose] noncomputable def cmpC (start cnt : Nat) (F : Nat → Nat) (L acc : Nat) : Bool :=
  bIf(Nat.ble start L, bIf(Nat.blt L (Nat.add start cnt), Nat.beq acc (F (Nat.sub L start)), true),
    true)

@[expose] noncomputable def stepC (wd n w start cnt : Nat) (F : Nat → Nat) (ch : Char)
    (_ : List Char) (ih : Nat → Nat → Nat → Nat → Nat → Bool) (L e t v acc : Nat) : Bool :=
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
        bAnd(cmpC start cnt F L acc,
          ih (Nat.succ L) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)),
        false)))

theorem run_eq (wd n w lines start cnt : Nat) (F : Nat → Nat) (cs : List Char) :
    run wd n w lines start cnt F cs =
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (nilC lines)
        (stepC wd n w start cnt F) cs := rfl

theorem rec_append {k : Nat → Nat → Nat → Nat → Nat → Bool}
    {s : Char → List Char → (Nat → Nat → Nat → Nat → Nat → Bool) →
      Nat → Nat → Nat → Nat → Nat → Bool}
    (hs : ∀ ch l l' ih, s ch l ih = s ch l' ih) :
    ∀ A B : List Char, List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) k s (A ++ B) =
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
        (List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) k s B) s A
  | [], _ => rfl
  | ch :: A, B => by
    change s ch (A ++ B) (List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) k s
      (A ++ B)) = s ch A _
    rw [rec_append hs A B, hs ch (A ++ B) A]

theorem false_ne {P : Prop} (h : false = true) : P := absurd h (by decide)

section Steps

variable {wd n w start cnt : Nat} {F : Nat → Nat} {ch : Char} {tl : List Char}
  {ih : Nat → Nat → Nat → Nat → Nat → Bool} {L e t v acc : Nat}

theorem stepC_nl (hb : Nat.blt e n = false) (hn : Nat.beq (Char.toNat ch) 10 = true) :
    stepC wd n w start cnt F ch tl ih L e t v acc =
      bAnd(cmpC start cnt F L acc, ih (Nat.succ L) 0 0 0 0) := by
  unfold stepC
  rw [strictB_eq]
  try dsimp only
  rw [hb, hn]

theorem stepC_bad1 (hb : Nat.blt e n = false) (hn : Nat.beq (Char.toNat ch) 10 = false) :
    stepC wd n w start cnt F ch tl ih L e t v acc = false := by
  unfold stepC
  rw [strictB_eq]
  try dsimp only
  rw [hb, hn]

theorem stepC_bad2 (hb : Nat.blt e n = true) (hh : Nat.blt (hexV (Char.toNat ch)) 16 = false) :
    stepC wd n w start cnt F ch tl ih L e t v acc = false := by
  unfold stepC
  rw [strictB_eq]
  try dsimp only
  rw [hb]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [hh]

theorem stepC_dig (hb : Nat.blt e n = true) (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true)
    (ht : Nat.beq (Nat.succ t) wd = false) :
    stepC wd n w start cnt F ch tl ih L e t v acc =
      ih L e (Nat.succ t) (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) acc := by
  unfold stepC
  rw [strictB_eq]
  try dsimp only
  rw [hb]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [ht]

theorem stepC_bad3 (hb : Nat.blt e n = true) (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true)
    (ht : Nat.beq (Nat.succ t) wd = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = false) :
    stepC wd n w start cnt F ch tl ih L e t v acc = false := by
  unfold stepC
  rw [strictB_eq]
  try dsimp only
  rw [hb]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]

theorem stepC_ent (hb : Nat.blt e n = true) (hh : Nat.blt (hexV (Char.toNat ch)) 16 = true)
    (ht : Nat.beq (Nat.succ t) wd = true)
    (hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w) = true) :
    stepC wd n w start cnt F ch tl ih L e t v acc =
      ih L (Nat.succ e) 0 0
        (Nat.lor acc (Nat.shiftLeft (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.mul w e))) := by
  unfold stepC
  rw [strictB_eq]
  try dsimp only
  rw [hb]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [hh]
  try dsimp only
  rw [strictB_eq]
  try dsimp only
  rw [ht]
  try dsimp only
  rw [hv]
  try dsimp only
  rw [strictB_eq]

end Steps

theorem run_le (wd n w la start cnt : Nat) (F : Nat → Nat) :
    ∀ (A : List Char) (L e t v acc : Nat),
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (nilC la)
        (stepC wd n w start cnt F) A L e t v acc = true → L ≤ la
  | [], L, e, t, v, acc, h => by
    change nilC la L e t v acc = true at h
    unfold nilC at h
    exact Nat.le_of_eq (Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h).1)
  | ch :: A, L, e, t, v, acc, h => by
    change stepC wd n w start cnt F ch A _ L e t v acc = true at h
    cases hb : Nat.blt e n
    · cases hn : Nat.beq (Char.toNat ch) 10
      · rw [stepC_bad1 hb hn] at h
        exact false_ne h
      · rw [stepC_nl hb hn] at h
        have := run_le wd n w la start cnt F A _ _ _ _ _ ((bAnd_iff _ _).1 h).2
        omega
    · cases hh : Nat.blt (hexV (Char.toNat ch)) 16
      · rw [stepC_bad2 hb hh] at h
        exact false_ne h
      · cases ht : Nat.beq (Nat.succ t) wd
        · rw [stepC_dig hb hh ht] at h
          exact run_le wd n w la start cnt F A _ _ _ _ _ h
        · cases hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w)
          · rw [stepC_bad3 hb hh ht hv] at h
            exact false_ne h
          · rw [stepC_ent hb hh ht hv] at h
            exact run_le wd n w la start cnt F A _ _ _ _ _ h

theorem sim (wd n w la s1 c1 s2 c2 d : Nat) (F1 F2 : Nat → Nat)
    (K : Nat → Nat → Nat → Nat → Nat → Bool) :
    ∀ (A : List Char) (L e t v acc : Nat),
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (nilC la)
        (stepC wd n w s1 c1 F1) A L e t v acc = true →
      (t = 0 → v = 0) → (e = 0 → acc = 0) →
      (∀ L' a, L ≤ L' → L' < la → cmpC s1 c1 F1 L' a = cmpC s2 c2 F2 (L' + d) a) →
      List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) K
        (stepC wd n w s2 c2 F2) A (L + d) e t v acc = K (la + d) 0 0 0 0
  | [], L, e, t, v, acc, h, hv, ha, _ => by
    change nilC la L e t v acc = true at h
    unfold nilC at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
    have eL := Nat.eq_of_beq_eq_true h1
    have ee := Nat.eq_of_beq_eq_true h2
    have et := Nat.eq_of_beq_eq_true h3
    change K (L + d) e t v acc = K (la + d) 0 0 0 0
    rw [eL, ee, et, hv et, ha ee]
  | ch :: A, L, e, t, v, acc, h, hvI, haI, hc => by
    change stepC wd n w s1 c1 F1 ch A _ L e t v acc = true at h
    change stepC wd n w s2 c2 F2 ch A _ (L + d) e t v acc = _
    cases hb : Nat.blt e n
    · cases hn : Nat.beq (Char.toNat ch) 10
      · rw [stepC_bad1 hb hn] at h
        exact false_ne h
      · rw [stepC_nl hb hn] at h
        rw [stepC_nl hb hn]
        obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
        have hle := run_le wd n w la s1 c1 F1 A _ _ _ _ _ h2
        rw [← hc L acc (Nat.le_refl L) (by omega), h1]
        try dsimp only
        have e1 : Nat.succ (L + d) = Nat.succ L + d := (Nat.succ_add L d).symm
        rw [e1]
        exact sim wd n w la s1 c1 s2 c2 d F1 F2 K A _ _ _ _ _ h2 (fun _ => rfl) (fun _ => rfl)
          (fun L' a h1' h2' => hc L' a (by omega) h2')
    · cases hh : Nat.blt (hexV (Char.toNat ch)) 16
      · rw [stepC_bad2 hb hh] at h
        exact false_ne h
      · cases ht : Nat.beq (Nat.succ t) wd
        · rw [stepC_dig hb hh ht] at h
          rw [stepC_dig hb hh ht]
          exact sim wd n w la s1 c1 s2 c2 d F1 F2 K A _ _ _ _ _ h (fun h' => absurd h' (by omega))
            haI hc
        · cases hv : Nat.blt (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) (Nat.shiftLeft 1 w)
          · rw [stepC_bad3 hb hh ht hv] at h
            exact false_ne h
          · rw [stepC_ent hb hh ht hv] at h
            rw [stepC_ent hb hh ht hv]
            exact sim wd n w la s1 c1 s2 c2 d F1 F2 K A _ _ _ _ _ h (fun _ => rfl)
              (fun h' => absurd h' (by omega)) hc

theorem cmp_lo {cnt la : Nat} {F G : Nat → Nat} {L a : Nat} (hL : L < la) (hc : la ≤ cnt)
    (hFG : G L = F L) : cmpC 0 la F L a = cmpC 0 cnt G L a := by
  have h0 : Nat.ble 0 L = true := Nat.ble_eq.mpr (Nat.zero_le L)
  have h1 : Nat.blt L (Nat.add 0 la) = true := Nat.blt_eq.mpr (by change L < 0 + la; omega)
  have h2 : Nat.blt L (Nat.add 0 cnt) = true := Nat.blt_eq.mpr (by change L < 0 + cnt; omega)
  unfold cmpC
  rw [h0, h1, h2]
  change Nat.beq a (F (L - 0)) = Nat.beq a (G (L - 0))
  rw [Nat.sub_zero, hFG]

theorem hexBind_append {A B : List Char} {wd n w la lb : Nat} {F G : Nat → Nat}
    (hA : hexBind A wd n w la 0 la F = true) (hB : hexBind B wd n w lb 0 lb G = true) :
    hexBind (A ++ B) wd n w (la + lb) 0 (la + lb)
      (fun j => nIf(Nat.blt j la, F j, G (Nat.sub j la))) = true := by
  unfold hexBind at hA hB ⊢
  obtain ⟨hw, hA2⟩ := (bAnd_iff _ _).1 hA
  obtain ⟨-, hA⟩ := (bAnd_iff _ _).1 hA2
  obtain ⟨-, hB2⟩ := (bAnd_iff _ _).1 hB
  obtain ⟨-, hB⟩ := (bAnd_iff _ _).1 hB2
  rw [hw]
  try dsimp only
  have hle : Nat.ble (Nat.add 0 (la + lb)) (la + lb) = true :=
    Nat.ble_eq.mpr (by change 0 + (la + lb) ≤ la + lb; omega)
  rw [hle]
  try dsimp only
  rw [run_eq] at hA hB ⊢
  rw [rec_append (fun _ _ _ _ => rfl)]
  have sA := sim wd n w la 0 la 0 (la + lb) 0 F
    (fun j => nIf(Nat.blt j la, F j, G (Nat.sub j la)))
    (List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (nilC (la + lb))
      (stepC wd n w 0 (la + lb) (fun j => nIf(Nat.blt j la, F j, G (Nat.sub j la)))) B)
    A 0 0 0 0 0 hA (fun _ => rfl) (fun _ => rfl) (fun L' a _ hL => by
      rw [Nat.add_zero]
      refine cmp_lo hL (by omega) ?_
      have hb : Nat.blt L' la = true := Nat.blt_eq.mpr hL
      try dsimp only
      rw [hb])
  rw [Nat.add_zero, Nat.add_zero] at sA
  rw [sA]
  have sB := sim wd n w lb 0 lb 0 (la + lb) la G
    (fun j => nIf(Nat.blt j la, F j, G (Nat.sub j la))) (nilC (la + lb))
    B 0 0 0 0 0 hB (fun _ => rfl) (fun _ => rfl) (fun L' a _ hL => by
      have h0 : Nat.ble 0 L' = true := Nat.ble_eq.mpr (Nat.zero_le L')
      have h0' : Nat.ble 0 (L' + la) = true := Nat.ble_eq.mpr (Nat.zero_le _)
      have h1 : Nat.blt L' (Nat.add 0 lb) = true := Nat.blt_eq.mpr (by change L' < 0 + lb; omega)
      have h2 : Nat.blt (L' + la) (Nat.add 0 (la + lb)) = true :=
        Nat.blt_eq.mpr (by change L' + la < 0 + (la + lb); omega)
      have h3 : Nat.blt (Nat.sub (L' + la) 0) la = false := by
        rw [Nat.sub_eq, Nat.sub_zero]
        cases h : Nat.blt (L' + la) la
        · rfl
        · have := Nat.blt_eq.mp h
          omega
      unfold cmpC
      rw [h0, h0', h1, h2]
      try dsimp only
      rw [h3]
      try dsimp only
      have e : Nat.sub (Nat.sub (L' + la) 0) la = Nat.sub L' 0 := by
        change L' + la - 0 - la = L' - 0
        omega
      rw [e])
  rw [Nat.zero_add] at sB
  rw [sB]
  unfold nilC
  have e : Nat.beq (lb + la) (la + lb) = true := Nat.beq_eq.mpr (Nat.add_comm lb la)
  rw [e]
  rfl

end CFSG.KS.Text

end
