module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.Spor.Mathieu
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import Std.Tactic.BVDecide.Normalize.Prop

open Lean Elab Command

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.Monster.B.Co2.Native

theorem canonK_pcomp {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    canonK n w (mask w) (n * w) (pcomp n w (mask w) p q) = true := by
  unfold canonK at hp hq ⊢
  simp only [bAnd_iff] at hp hq ⊢
  obtain ⟨hs, -, hp4⟩ := hp
  obtain ⟨-, -, hq4⟩ := hq
  have hs' := hs
  unfold szOK at hs'
  simp only [bAnd_iff] at hs'
  have hn : n < 2 ^ 32 := by
    have := Nat.blt_eq.mp hs'.1
    omega
  have hw : 0 < w := by
    have h2 := Nat.blt_eq.mp hs'.2
    rw [PackFld.shl_eq, Nat.one_mul] at h2
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · subst h0
      simp at h2
    · exact h0
  refine ⟨hs, Nat.beq_eq.mpr (PackFld.pcomp_shr (p := p) (q := q) hn hw),
    PackFld.allN_of_forall (fun i hi => ?_)⟩
  rw [PackFld.pg_pcomp hn hi]
  exact allN_spec hp4 _ (Nat.blt_eq.mp (allN_spec hq4 i hi))

theorem compA_unpack {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) := by
  refine compEqK_sound ?_
  unfold compEqK
  rw [hp, hq, Nat.beq_refl]

end CFSG.KC.BfsPin

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.PSL3Four.Native

@[expose] noncomputable def wordTabK (n w m idn : Nat) (S : Nat → Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn
    (fun j _ ih => strictN ih (fun acc => pcomp n w m (S j) acc)) wd

theorem strictN_app' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem wordTabK_eq {n w idn : Nat} {S : Nat → Nat} {gs : Array Tab}
    (hid : idTab n = unpack n w idn) (hidc : canonK n w (mask w) (n * w) idn = true) :
    ∀ wd : List Nat, (∀ j ∈ wd, gs[j]! = unpack n w (S j) ∧ canonK n w (mask w) (n * w) (S j) = true) →
      wd.foldr (fun j acc => comp n gs[j]! acc) (idTab n) =
          unpack n w (wordTabK n w (mask w) idn S wd) ∧
        canonK n w (mask w) (n * w) (wordTabK n w (mask w) idn S wd) = true
  | [], _ => ⟨hid, hidc⟩
  | j :: rest, h => by
    obtain ⟨ih1, ih2⟩ := wordTabK_eq hid hidc rest (fun j' hj' => h j' (List.mem_cons_of_mem j hj'))
    obtain ⟨hj1, hj2⟩ := h j List.mem_cons_self
    have e : wordTabK n w (mask w) idn S (j :: rest) =
        pcomp n w (mask w) (S j) (wordTabK n w (mask w) idn S rest) := by
      change strictN (wordTabK n w (mask w) idn S rest) (fun acc => pcomp n w (mask w) (S j) acc) = _
      rw [strictN_app']
    have e2 : (j :: rest).foldr (fun j acc => comp n gs[j]! acc) (idTab n) =
        comp n gs[j]! (rest.foldr (fun j acc => comp n gs[j]! acc) (idTab n)) := rfl
    rw [e, e2, ih1, hj1]
    exact ⟨compA_unpack hj2 ih2, canonK_pcomp hj2 ih2⟩

theorem nget_get (l : List Nat) {i : Nat} (hi : i < l.length) : CFSG.KS.Mathieu.nget l i = l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by simpa using hi)

@[expose] noncomputable def selFrom (q : Nat → Bool) (r : Nat) : Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ S => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) S)
    (fun _ ih i S => bIf(q i,
      List.rec (motive := fun _ => Bool) false (fun x xs _ => bAnd(Nat.beq x i, ih (Nat.succ i) xs)) S,
      ih (Nat.succ i) S)) r

theorem selFrom_spec (q : Nat → Bool) :
    ∀ (r i : Nat) (S : List Nat), selFrom q r i S = true → (List.range' i r).filter q = S
  | 0, i, S, h => by
    cases S with
    | nil => rfl
    | cons x xs => exact absurd h (by simp [selFrom])
  | r + 1, i, S, h => by
    change bIf(q i, List.rec (motive := fun _ => Bool) false
      (fun x xs _ => bAnd(Nat.beq x i, selFrom q r (Nat.succ i) xs)) S,
      selFrom q r (Nat.succ i) S) = true at h
    rw [List.range'_succ]
    cases hq : q i
    · rw [hq] at h
      rw [List.filter_cons_of_neg (by simp [hq])]
      exact selFrom_spec q r (i + 1) S h
    · rw [hq] at h
      rw [List.filter_cons_of_pos hq]
      cases S with
      | nil => exact absurd h (by simp)
      | cons x xs =>
        obtain ⟨hx, hr⟩ := (bAnd_iff _ _).1 h
        rw [Nat.eq_of_beq_eq_true hx, selFrom_spec q r (i + 1) xs hr]

theorem sel_spec {q : Nat → Bool} {m : Nat} {S : List Nat} (h : selFrom q m 0 S = true) :
    (List.range m).filter q = S := by
  rw [List.range_eq_range']
  exact selFrom_spec q m 0 S h

end CFSG.KS.PEnum

elab "#knatlist " pre:ident sId:ident : command => do
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let l ← liftTermElabM <| unsafe evalConst (List Nat) sN
  let natE := mkConst ``Nat
  let lst := l.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) natE (mkRawNatLit x) acc)
    (mkApp (mkConst ``List.nil [0]) natE)
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KC.Tab.addDef pre.getId (mkApp (mkConst ``List [0]) natE) lst

end
