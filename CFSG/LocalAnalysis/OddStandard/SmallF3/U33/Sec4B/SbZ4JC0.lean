module

public import Aesop.BuiltinRules
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive
import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC0K

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFin

@[expose] def col (m i : Nat) : Nat := (m >>> (4 * i)) &&& 15

@[expose] def app (m v : Nat) : Nat :=
  (if v &&& 1 != 0 then col m 0 else 0) ^^^ (if v &&& 2 != 0 then col m 1 else 0) ^^^
  (if v &&& 4 != 0 then col m 2 else 0) ^^^ (if v &&& 8 != 0 then col m 3 else 0)

@[expose] def mmul (a b : Nat) : Nat :=
  app a (col b 0) ||| (app a (col b 1) <<< 4) ||| (app a (col b 2) <<< 8) |||
    (app a (col b 3) <<< 12)

@[expose] def one : Nat := 33825

@[expose] def T : Nat := 46369

@[expose] def L : Nat := 23331

@[expose] def R : Nat := 51219

@[expose] def R2 : Nat := 19506

@[expose] def isP (x : Nat) : Bool :=
  x < 65536 && (1 ≤ col x 0 && col x 0 ≤ 3) && (1 ≤ col x 1 && col x 1 ≤ 3) &&
    col x 0 != col x 1 && 4 ≤ col x 2 && 4 ≤ col x 3 && 4 ≤ (col x 2 ^^^ col x 3)

@[expose] def Plist : List Nat := (List.range 65536).filter isP

@[expose] def stepAux (gens : List Nat) (x : Nat) (st : List Nat × Nat) : List Nat × Nat :=
  gens.foldl (fun (acc : List Nat × Nat) g =>
    let y := mmul g x
    if acc.2.testBit y then acc else (y :: acc.1, acc.2 ||| (1 <<< y))) st

@[expose] def closAux (gens : List Nat) : Nat → List Nat → List Nat → Nat → List Nat
  | 0, _, all, _ => all
  | fuel + 1, frontier, all, seen =>
    match frontier with
    | [] => all
    | _ =>
      let r := frontier.foldl (fun st x => stepAux gens x st) ([], seen)
      closAux gens fuel r.1 (r.1 ++ all) r.2

@[expose] def clos (gens : List Nat) : List Nat := closAux gens 64 [one] [one] (1 <<< one)

@[expose] def closSet (S : List Nat) : Nat := S.foldl (fun c x => c ||| (1 <<< x)) 0

@[expose] def Clist : List Nat :=
  [19475, 19489, 19506, 24083, 24097, 24114, 28435, 28449,
  28466, 32019, 32033, 32050, 33811, 33825, 33842, 38419,
  38433, 38450, 42771, 42785, 42802, 46355, 46369, 46386,
  51219, 51233, 51250, 55827, 55841, 55858, 60179, 60193,
  60210, 63763, 63777, 63794]

@[expose] def isInv (a : Nat) : Bool := a != one && mmul a a == one

@[expose] def witness (cl : List Nat) : Bool :=
  let cs := closSet cl
  let C := Clist.filter fun x => cs.testBit x
  C.any (fun a => a != one && mmul a a != one && mmul (mmul a a) (mmul a a) == one) ||
  (let I := C.filter isInv
   I.any fun a => I.any fun b => a != b && mmul a b == mmul b a)

@[expose] def Witness (S : Set Nat) : Prop :=
  (∃ a ∈ S, a ∈ Clist ∧ a ≠ one ∧ mmul a a ≠ one ∧ mmul (mmul a a) (mmul a a) = one) ∨
  (∃ a ∈ S, ∃ b ∈ S, a ∈ Clist ∧ b ∈ Clist ∧ a ≠ one ∧ b ≠ one ∧ mmul a a = one ∧
    mmul b b = one ∧ a ≠ b ∧ mmul a b = mmul b a)

@[expose] def H0 : List Nat :=
  [18467, 19506, 23331, 24114, 33825, 35858, 46369, 48658, 50225, 51219, 58673, 60179]

@[expose] def g48 : Nat := 46625

@[expose] def S48 : List Nat :=
  [18467, 18723, 19506, 19762, 23075, 23331, 24114, 24370,
  27171, 27427, 27698, 27954, 30755, 31011, 32306, 32562,
  33825, 34593, 35858, 36626, 37921, 38689, 40210, 40466,
  42273, 42529, 44050, 44818, 46369, 46625, 48402, 48658,
  50225, 50737, 51219, 51731, 54321, 54833, 55571, 56083,
  58673, 59185, 59667, 60179, 62769, 63281, 63507, 64019]

@[expose] def repsNT : List Nat :=
  [18450, 18451, 18465, 18481, 18482, 18706, 18707, 18721,
  18723, 18737, 18738, 18962, 18963, 18977, 18979, 18993,
  18994, 19218, 19219, 19233, 19235, 19249, 19250, 22546,
  22547, 22561, 22577, 22802, 22803, 22817, 22833, 23058,
  23059, 23073, 23089, 23314, 23315, 23329, 23345, 26659,
  26674, 26915, 26930, 27171, 27186, 27427, 27442]

@[expose] def Mlist : List Nat := [33825, 38689, 42273, 46625]

theorem Plist_length : Plist.length = 576 := by
  have hP : Plist = ZJFinK.plistK := ZJFinK.plist_eq
  rw [hP]
  decide +kernel

theorem Clist_eq : Clist = Plist.filter fun x => mmul x R == mmul R x := by
  have hP : Plist = ZJFinK.plistK := ZJFinK.plist_eq
  rw [hP]
  exact beq_iff_eq.1 (by decide +kernel)

theorem R_cube : mmul R (mmul R R) = one ∧ mmul R R = R2 := by decide +kernel

theorem R2_sq : mmul R2 R2 = R ∧ mmul R2 R = one := by decide +kernel

theorem Clist_comm : ∀ a ∈ Clist, mmul a R = mmul R a ∧ mmul a R2 = mmul R2 a := by
  decide +kernel

theorem H0_sub_clos : ∀ x ∈ H0, x ∈ clos [T, L, R] := by decide +kernel

theorem S48_sub_clos : ∀ x ∈ S48, x ∈ clos [T, L, R, g48] := by decide +kernel

theorem H0_sub_S48 : ∀ x ∈ H0, x ∈ S48 := by decide +kernel

theorem H0_card : H0.length = 12 ∧ H0.Nodup := by decide +kernel

theorem S48_card : S48.length = 48 ∧ S48.Nodup := by decide +kernel

theorem S48_sub_P : ∀ x ∈ S48, x ∈ Plist := by
  have hP : Plist = ZJFinK.plistK := ZJFinK.plist_eq
  have hb : ZJFinK.allF S48 (fun x => ZJFinK.elemF x ZJFinK.plistK) = true := by decide +kernel
  intro x hx
  rw [hP, ← ZJFinK.elemF_iff]
  exact (ZJFinK.allF_iff _ _).1 hb x hx

theorem gens_mem_H0 : T ∈ H0 ∧ L ∈ H0 ∧ R ∈ H0 ∧ one ∈ H0 := by decide +kernel

theorem coset_ok : ∀ g ∈ Plist, g ∈ H0 ∨ ∃ h ∈ H0, mmul g h ∈ repsNT := by
  have hP : Plist = ZJFinK.plistK := ZJFinK.plist_eq
  have hb : ZJFinK.allF ZJFinK.plistK (fun g => ZJFinK.elemF g H0 ||
      ZJFinK.anyF H0 (fun h => ZJFinK.elemF (ZJFinK.mmulF g h) repsNT)) = true := by
    decide +kernel
  intro g hg
  rw [hP] at hg
  have h1 : (ZJFinK.elemF g H0 ||
      ZJFinK.anyF H0 (fun h => ZJFinK.elemF (ZJFinK.mmulF g h) repsNT)) = true :=
    (ZJFinK.allF_iff _ _).1 hb g hg
  rw [Bool.or_eq_true, ZJFinK.elemF_iff, ZJFinK.anyF_iff] at h1
  rcases h1 with h | ⟨h, hh, hm⟩
  · exact Or.inl h
  · have hmm : mmul g h = ZJFinK.mmulF g h := ZJFinK.mmulC_eq g h
    refine Or.inr ⟨h, hh, ?_⟩
    rw [hmm, ← ZJFinK.elemF_iff]
    exact hm

theorem reps_ok : ∀ r ∈ repsNT,
    (r ∈ S48 ∧ g48 ∈ clos [T, L, R, r]) ∨ witness (clos [T, L, R, r]) = true := by
  have hs : ∀ gens x st, stepAux gens x st = ZJFinK.stepF gens x st := fun gens x st =>
    ZJFinK.stepG_eq mmul (fun a b => ZJFinK.mmulC_eq a b) gens x st
  have ha : ∀ gens fuel f a s, closAux gens fuel f a s = ZJFinK.closAuxF gens fuel f a s := by
    intro gens fuel
    induction fuel with
    | zero => intro f a s; rfl
    | succ n ih =>
      intro f a s
      cases f with
      | nil => rfl
      | cons x xs =>
        have e : closAux gens (n + 1) (x :: xs) a s = closAux gens n
            ((x :: xs).foldl (fun st x => stepAux gens x st) ([], s)).1
            (((x :: xs).foldl (fun st x => stepAux gens x st) ([], s)).1 ++ a)
            ((x :: xs).foldl (fun st x => stepAux gens x st) ([], s)).2 := rfl
        rw [e, ZJFinK.closAuxF_succ_cons, ZJFinK.frF_eq gens _ (fun st x => hs gens x st)]
        exact ih _ _ _
  have h0 : Nat.xor ((1 <<< one) <<< 64) 12345 >>> 64 = 1 <<< one := by
    rw [ZJFinK.shr_xor_low _ _ (by decide), Nat.shiftLeft_shiftRight]
  have hc : ∀ gens, clos gens =
      ZJFinK.closAuxS gens 64 [one] [one] (Nat.xor ((1 <<< one) <<< 64) 12345) := fun gens => by
    rw [ZJFinK.closAuxS_eq, h0]
    exact ha gens 64 [one] [one] (1 <<< one)
  have hb : ZJFinK.allF repsNT (fun r =>
      (ZJFinK.elemF r S48 && ZJFinK.elemF g48
        (ZJFinK.closAuxS [T, L, R, r] 64 [one] [one] (Nat.xor ((1 <<< one) <<< 64) 12345))) ||
      witness (ZJFinK.closAuxS [T, L, R, r] 64 [one] [one]
        (Nat.xor ((1 <<< one) <<< 64) 12345))) = true := by
    decide +kernel
  intro r hr
  have h1 := (ZJFinK.allF_iff _ _).1 hb r hr
  rw [Bool.or_eq_true, Bool.and_eq_true, ZJFinK.elemF_iff, ZJFinK.elemF_iff] at h1
  rw [hc]
  exact h1

theorem S48_cosets : ∀ g ∈ Plist, ∀ h ∈ H0, mmul g h ∈ S48 → g ∈ S48 := by
  have hP : Plist = ZJFinK.plistK := ZJFinK.plist_eq
  have hb : ZJFinK.allF ZJFinK.plistK (fun g => ZJFinK.allF H0 (fun h =>
      !ZJFinK.elemF (ZJFinK.mmulF g h) S48 || ZJFinK.elemF g S48)) = true := by
    decide +kernel
  intro g hg h hh hm
  rw [hP] at hg
  have h1 : (!ZJFinK.elemF (ZJFinK.mmulF g h) S48 || ZJFinK.elemF g S48) = true :=
    (ZJFinK.allF_iff _ _).1 ((ZJFinK.allF_iff _ _).1 hb g hg) h hh
  have hmm : mmul g h = ZJFinK.mmulF g h := ZJFinK.mmulC_eq g h
  rw [hmm, ← ZJFinK.elemF_iff] at hm
  rw [hm, Bool.not_true, Bool.false_or, ZJFinK.elemF_iff] at h1
  exact h1

theorem mem_Plist_iff (x : Nat) : x ∈ Plist ↔ x < 65536 ∧ isP x = true := by
  simp [Plist, List.mem_filter, List.mem_range]

theorem rho_cases : ∀ r ∈ Plist, mmul T r = mmul r T → mmul r (mmul r r) = one →
    mmul L r = mmul (mmul r r) L → (∀ n ∈ List.range 16, n ≠ 0 → app r n ≠ n) →
    (∀ n ∈ [4, 8, 12], app r n &&& 3 = 0) → r = R ∨ r = R2 := by
  have hP : Plist = ZJFinK.plistK := ZJFinK.plist_eq
  rw [hP]
  decide +kernel

theorem M_sub : ∀ m ∈ Mlist, m ∈ S48 := by decide +kernel

theorem M_mul : ∀ a ∈ Mlist, ∀ b ∈ Mlist, mmul a b ∈ Mlist := by decide +kernel

theorem M_elem : (∀ a ∈ Mlist, ∀ b ∈ Mlist, mmul a b = mmul b a) ∧
    ∀ a ∈ Mlist, mmul a a = one := by decide +kernel

theorem M_card : Mlist.length = 4 ∧ Mlist.Nodup := by decide +kernel

theorem M_normal : ∀ s ∈ S48, ∀ m ∈ Mlist, ∃ m' ∈ Mlist, mmul s m = mmul m' s := by
  decide +kernel

theorem M_triv_V : ∀ m ∈ Mlist, app m 1 = 1 ∧ app m 2 = 2 := by decide +kernel

theorem M_triv_YV : ∀ m ∈ Mlist, ∀ n ∈ List.range 16, app m n ^^^ n < 4 := by decide +kernel

theorem M_cent_Y : ∀ m ∈ Mlist, m ≠ one → ∀ n ∈ List.range 16, app m n = n → n < 4 := by
  decide +kernel

theorem T_not_M : T ∉ Mlist := by decide +kernel

theorem T_central : ∀ s ∈ S48, mmul T s = mmul s T := by decide +kernel

theorem M_fpf : ∀ m ∈ Mlist, mmul m R = mmul R m → m = one := by decide +kernel

theorem cent_V : ∀ s ∈ S48, app s 1 = 1 → app s 2 = 2 → s ∈ Mlist ∨ mmul T s ∈ Mlist := by
  decide +kernel

end CFSG.OddStandard.SmallF3.HarrisU33.S4B.ZJFin
