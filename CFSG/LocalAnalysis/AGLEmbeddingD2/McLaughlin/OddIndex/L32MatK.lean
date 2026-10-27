module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.L32K

open Matrix

abbrev M3K := Matrix (Fin 3) (Fin 3) (ZMod 2)

structure B9 where
  a0 : Bool
  a1 : Bool
  a2 : Bool
  a3 : Bool
  a4 : Bool
  a5 : Bool
  a6 : Bool
  a7 : Bool
  a8 : Bool

@[expose] def e (x : Bool) : ZMod 2 := if x then 1 else 0

theorem e_xor (x y : Bool) : e (x ^^ y) = e x + e y := by cases x <;> cases y <;> decide

theorem e_and (x y : Bool) : e (x && y) = e x * e y := by cases x <;> cases y <;> decide

theorem e_beq (z : ZMod 2) : e (z == 1) = z := by revert z; decide

theorem beq_e (x : Bool) : (e x == 1) = x := by cases x <;> decide

@[expose] def toM (x : B9) : M3K :=
  !![e x.a0, e x.a1, e x.a2; e x.a3, e x.a4, e x.a5; e x.a6, e x.a7, e x.a8]

@[expose] def ofM (m : M3K) : B9 :=
  ⟨m 0 0 == 1, m 0 1 == 1, m 0 2 == 1, m 1 0 == 1, m 1 1 == 1, m 1 2 == 1,
    m 2 0 == 1, m 2 1 == 1, m 2 2 == 1⟩

theorem ofM_toM (x : B9) : ofM (toM x) = x := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := x
  simp [ofM, toM, beq_e]

theorem toM_ofM (m : M3K) : toM (ofM m) = m := by
  rw [Matrix.eta_fin_three m]
  simp [ofM, toM, e_beq]

theorem toM_injective : Function.Injective toM := fun x y h => by
  rw [← ofM_toM x, ← ofM_toM y, h]

@[expose] def mulB (x y : B9) : B9 :=
  ⟨(x.a0 && y.a0) ^^ (x.a1 && y.a3) ^^ (x.a2 && y.a6),
   (x.a0 && y.a1) ^^ (x.a1 && y.a4) ^^ (x.a2 && y.a7),
   (x.a0 && y.a2) ^^ (x.a1 && y.a5) ^^ (x.a2 && y.a8),
   (x.a3 && y.a0) ^^ (x.a4 && y.a3) ^^ (x.a5 && y.a6),
   (x.a3 && y.a1) ^^ (x.a4 && y.a4) ^^ (x.a5 && y.a7),
   (x.a3 && y.a2) ^^ (x.a4 && y.a5) ^^ (x.a5 && y.a8),
   (x.a6 && y.a0) ^^ (x.a7 && y.a3) ^^ (x.a8 && y.a6),
   (x.a6 && y.a1) ^^ (x.a7 && y.a4) ^^ (x.a8 && y.a7),
   (x.a6 && y.a2) ^^ (x.a7 && y.a5) ^^ (x.a8 && y.a8)⟩

theorem toM_mulB (x y : B9) : toM (mulB x y) = toM x * toM y := by
  simp only [toM, mulB, Matrix.mul_fin_three, e_xor, e_and]

@[expose] def detB (x : B9) : Bool :=
  (x.a0 && x.a4 && x.a8) ^^ (x.a0 && x.a5 && x.a7) ^^ (x.a1 && x.a3 && x.a8) ^^
    (x.a1 && x.a5 && x.a6) ^^ (x.a2 && x.a3 && x.a7) ^^ (x.a2 && x.a4 && x.a6)

theorem neg_two (z : ZMod 2) : -z = z := by revert z; decide

theorem det_toM (x : B9) : (toM x).det = e (detB x) := by
  rw [Matrix.det_fin_three]
  simp [toM, detB, e_xor, e_and, sub_eq_add_neg, neg_two, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem det_toM_ne_zero (x : B9) : (toM x).det ≠ 0 ↔ detB x = true := by
  rw [det_toM]
  cases detB x <;> decide

@[expose] def eqB (x y : B9) : Bool :=
  (x.a0 == y.a0) && (x.a1 == y.a1) && (x.a2 == y.a2) && (x.a3 == y.a3) && (x.a4 == y.a4) &&
    (x.a5 == y.a5) && (x.a6 == y.a6) && (x.a7 == y.a7) && (x.a8 == y.a8)

theorem eqB_iff (x y : B9) : eqB x y = true ↔ toM x = toM y := by
  rw [toM_injective.eq_iff]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := x
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := y
  simp [eqB, and_assoc]

@[expose] def oneB : B9 := ⟨true, false, false, false, true, false, false, false, true⟩

theorem toM_oneB : toM oneB = 1 := by
  rw [← toM_ofM 1]
  rfl

@[expose] def bools : List Bool := [false, true]

theorem mem_bools (x : Bool) : x ∈ bools := by cases x <;> decide

@[expose] def all512 : List B9 :=
  bools.flatMap fun a0 => bools.flatMap fun a1 => bools.flatMap fun a2 =>
  bools.flatMap fun a3 => bools.flatMap fun a4 => bools.flatMap fun a5 =>
  bools.flatMap fun a6 => bools.flatMap fun a7 => bools.flatMap fun a8 =>
  [⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩]

theorem mem_all512 (x : B9) : x ∈ all512 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := x
  simp only [all512, List.mem_flatMap, List.mem_singleton]
  exact ⟨a0, mem_bools _, a1, mem_bools _, a2, mem_bools _, a3, mem_bools _, a4, mem_bools _,
    a5, mem_bools _, a6, mem_bools _, a7, mem_bools _, a8, mem_bools _, rfl⟩

@[expose] def idxB (x : B9) : ℕ :=
  x.a8.toNat + 2 * (x.a7.toNat + 2 * (x.a6.toNat + 2 * (x.a5.toNat + 2 * (x.a4.toNat +
    2 * (x.a3.toNat + 2 * (x.a2.toNat + 2 * (x.a1.toNat + 2 * x.a0.toNat)))))))

theorem all512_idx : (all512.map idxB == List.range 512) = true := by decide +kernel

theorem all512_nodup : all512.Nodup := by
  refine List.Nodup.of_map idxB ?_
  rw [beq_iff_eq.1 all512_idx]
  exact List.nodup_range

theorem forall_toM (p : M3K → Prop) : (∀ t : M3K, p t) ↔ ∀ x : B9, p (toM x) :=
  ⟨fun h x => h _, fun h t => toM_ofM t ▸ h (ofM t)⟩

theorem exists_toM (p : M3K → Prop) : (∃ t : M3K, p t) ↔ ∃ x : B9, p (toM x) :=
  ⟨fun ⟨t, ht⟩ => ⟨ofM t, (toM_ofM t).symm ▸ ht⟩, fun ⟨x, hx⟩ => ⟨_, hx⟩⟩

theorem card_filter_toM (p : M3K → Prop) [DecidablePred p] (q : B9 → Bool)
    (h : ∀ x, p (toM x) ↔ q x = true) :
    (Finset.univ.filter p).card = (all512.filter q).length := by
  have hs : Finset.univ.filter p = ((all512.filter q).map toM).toFinset := by
    ext t
    rw [← toM_ofM t]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map,
      List.mem_filter]
    constructor
    · intro ht
      exact ⟨ofM t, ⟨mem_all512 _, (h _).1 ht⟩, rfl⟩
    · rintro ⟨x, ⟨-, hx⟩, hxt⟩
      rw [← hxt]
      exact (h x).2 hx
  rw [hs, List.toFinset_card_of_nodup ((all512_nodup.filter q).map toM_injective), List.length_map]

theorem of_all {f : B9 → Bool} (h : all512.all f = true) (x : B9) : f x = true :=
  List.all_eq_true.1 h x (mem_all512 x)

@[expose] def invB (x : B9) : Bool := eqB (mulB x x) oneB && !eqB x oneB

theorem invB_iff (x : B9) : invB x = true ↔ toM x * toM x = 1 ∧ toM x ≠ 1 := by
  have h1 := eqB_iff (mulB x x) oneB
  have h2 := eqB_iff x oneB
  rw [toM_mulB, toM_oneB] at h1
  rw [toM_oneB] at h2
  rw [invB]
  cases hb : eqB x oneB <;> cases hc : eqB (mulB x x) oneB <;> simp_all

@[expose] def ord3B (x : B9) : Bool := eqB (mulB (mulB x x) x) oneB && !eqB x oneB

theorem ord3B_iff (x : B9) : ord3B x = true ↔ toM x * toM x * toM x = 1 ∧ toM x ≠ 1 := by
  have h1 := eqB_iff (mulB (mulB x x) x) oneB
  have h2 := eqB_iff x oneB
  rw [toM_mulB, toM_mulB, toM_oneB] at h1
  rw [toM_oneB] at h2
  rw [ord3B]
  cases hb : eqB x oneB <;> cases hc : eqB (mulB (mulB x x) x) oneB <;> simp_all

@[expose] def centB (t x : B9) : Bool := eqB (mulB x t) (mulB t x) && detB x

theorem centB_iff (t x : B9) :
    centB t x = true ↔ toM x * toM t = toM t * toM x ∧ (toM x).det ≠ 0 := by
  rw [centB, Bool.and_eq_true, eqB_iff, toM_mulB, toM_mulB, det_toM_ne_zero]

@[expose] def normB (c x : B9) : Bool :=
  (eqB (mulB x c) (mulB c x) || eqB (mulB x c) (mulB (mulB c c) x)) && detB x

theorem normB_iff (c x : B9) : normB c x = true ↔
    (toM x * toM c = toM c * toM x ∨ toM x * toM c = toM c * toM c * toM x) ∧ (toM x).det ≠ 0 := by
  rw [normB, Bool.and_eq_true, Bool.or_eq_true, eqB_iff, eqB_iff, toM_mulB, toM_mulB, toM_mulB,
    toM_mulB, det_toM_ne_zero]

@[expose] def chkCent : Bool :=
  all512.all fun t => !invB t || (all512.filter (centB t)).length == 8

theorem chkCent_ok : chkCent = true := by decide +kernel

@[expose] def chkCenter : Bool :=
  all512.all fun t => !invB t || all512.all fun x => !centB t x ||
    !(all512.all fun y => !centB t y || eqB (mulB x y) (mulB y x)) || eqB x oneB || eqB x t

theorem chkCenter_ok : chkCenter = true := by decide +kernel

@[expose] def chkNorm : Bool :=
  all512.all fun c => !ord3B c || (all512.filter (normB c)).length == 6

theorem chkNorm_ok : chkNorm = true := by decide +kernel

@[expose] def chkInv : Bool :=
  all512.all fun c => !ord3B c ||
    all512.any fun y => invB y && eqB (mulB y c) (mulB (mulB c c) y)

theorem chkInv_ok : chkInv = true := by decide +kernel

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.L32K
