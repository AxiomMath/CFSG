module

public import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C4aInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4aInputs
public import Certificates.Certificate5062

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

theorem x16_comm (a b : Fin 16) : xor16 a b = xor16 b a := Fin.ext (Nat.xor_comm _ _)

theorem x16_assoc (a b c : Fin 16) : xor16 (xor16 a b) c = xor16 a (xor16 b c) :=
  Fin.ext (Nat.xor_assoc _ _ _)

theorem x16_zero (a : Fin 16) : xor16 a 0 = a := Fin.ext (by simp [xor16])

theorem x16_zero_left (a : Fin 16) : xor16 0 a = a := Fin.ext (by simp [xor16])

theorem x16_self (a : Fin 16) : xor16 a a = 0 := Fin.ext (by simp [xor16])

theorem x16_cancel (a b : Fin 16) : xor16 (xor16 a b) b = a := by
  rw [x16_assoc, x16_self, x16_zero]

theorem x16_val (a b : Fin 16) : (xor16 a b).val = a.val ^^^ b.val := rfl

theorem x16_testBit (a b : Fin 16) (i : Nat) :
    (xor16 a b).val.testBit i = xor (a.val.testBit i) (b.val.testBit i) := by
  rw [x16_val, Nat.testBit_xor]

theorem x16_ext {a b : Fin 16} (h : ∀ i : Fin 4, a.val.testBit i = b.val.testBit i) : a = b := by
  have h1 : ∀ a b : Fin 16, (∀ i : Fin 4, a.val.testBit i = b.val.testBit i) → a = b := by decide
  exact h1 a b h

theorem bool_key (a1 a2 a3 a4 a5 a6 a7 : Bool) (h : xor a4 a5 = xor a2 (xor a6 a7)) :
    xor (xor a1 (xor a3 a4)) a7 = xor (xor a1 a2) (xor (xor a3 a6) a5) := by
  revert a1 a2 a3 a4 a5 a6 a7
  decide

theorem key_alg (v X Ac Bc bj Y bjk : Fin 16)
    (hb : xor16 Ac Bc = xor16 bj (xor16 Y bjk)) :
    xor16 (xor16 v (xor16 X Ac)) bjk = xor16 (xor16 v bj) (xor16 (xor16 X Y) Bc) := by
  apply x16_ext
  intro i
  have h := congrArg (fun a : Fin 16 => a.val.testBit i) hb
  simp only [x16_testBit] at h ⊢
  exact bool_key _ _ _ _ _ _ _ h

theorem Dg_zero : Dg 0 = 1 :=
  Certificates.certificate5062.2.1

theorem Dg_one : Dg 1 = yHat :=
  Certificates.certificate5062.2.2.1

theorem Dg_mul_chk :
    (List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    decide (Dg j * Dg k = Dg (mulIdx j k))) = true :=
  Certificates.certificate5062.2.2.2.1

theorem Dg_mul (j k : Fin 8) : Dg j * Dg k = Dg (mulIdx j k) := by
  have h := Dg_mul_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h j trivial k trivial

theorem Dg_inj_chk :
    (List.finRange 8).all (fun j => (List.finRange 8).all fun k =>
    imp (decide (Dg j = Dg k)) (decide (j = k))) = true :=
  Certificates.certificate5062.2.2.2.2.1

theorem Dg_inj {j k : Fin 8} (h : Dg j = Dg k) : j = k := by
  have h1 := Dg_inj_chk
  simp only [List.all_eq_true, List.mem_finRange, imp_eq_true, decide_eq_true_eq] at h1
  exact h1 j trivial k trivial h

theorem Dg_lin_chk :
    (List.finRange 8).all (fun j => (List.finRange 16).all fun a =>
    (List.finRange 16).all fun b =>
      decide (Dg j (xor16 a b) = xor16 (Dg j a) (Dg j b))) = true :=
  Certificates.certificate5062.2.2.2.2.2.1

theorem Dg_lin
    (j : Fin 8) (a b : Fin 16) : Dg j (xor16 a b) = xor16 (Dg j a) (Dg j b) := by
  have h := Dg_lin_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h j trivial a trivial b trivial

theorem Dg_mem_chk :
    (List.finRange 8).all (fun k => decide (Dg k ∈ d8L)) = true :=
  Certificates.certificate5062.2.2.2.2.2.2.1

theorem Dg_mem (k : Fin 8) : Dg k ∈ d8L := by
  have h := Dg_mem_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h k trivial

theorem Dg_exists_chk :
    d8L.all (fun d => (List.finRange 8).any fun k => decide (d = Dg k)) =
    true :=
  Certificates.certificate5062.2.2.2.2.2.2.2.1

theorem Dg_exists
    {d : Perm (Fin 16)} (hd : d ∈ d8L) : ∃ k : Fin 8, d = Dg k := by
  have h := Dg_exists_chk
  simp only [List.all_eq_true, List.any_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  obtain ⟨k, -, hk⟩ := h d hd
  exact ⟨k, hk⟩

theorem mulIdx_zero_left_chk :
    (List.finRange 8).all (fun k => decide (mulIdx 0 k = k)) = true :=
  Certificates.certificate5062.2.2.2.2.2.2.2.2.1

theorem mulIdx_zero_left (k : Fin 8) : mulIdx 0 k = k := by
  have h := mulIdx_zero_left_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h k trivial

theorem mulIdx_zero_right_chk :
    (List.finRange 8).all (fun k => decide (mulIdx k 0 = k)) = true :=
  Certificates.certificate5062.2.2.2.2.2.2.2.2.2.1

theorem mulIdx_zero_right (k : Fin 8) : mulIdx k 0 = k := by
  have h := mulIdx_zero_right_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h k trivial

theorem mulIdx_one_one : mulIdx 1 1 = 0 :=
  Certificates.certificate5062.2.2.2.2.2.2.2.2.2.2.1

theorem mulIdx_zero_zero : mulIdx 0 0 = 0 :=
  Certificates.certificate5062.2.2.2.2.2.2.2.2.2.2.2.1

theorem Dg_tr16_chk :
    (List.finRange 8).all (fun j => (List.finRange 16).all fun w =>
    decide (Dg j * tr16 w = tr16 (Dg j w) * Dg j)) = true :=
  Certificates.certificate5062.2.2.2.2.2.2.2.2.2.2.2.2

theorem Dg_tr16
    (j : Fin 8) (w : Fin 16) : Dg j * tr16 w = tr16 (Dg j w) * Dg j := by
  have h := Dg_tr16_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h j trivial w trivial

structure ExtDat (G : Type*) [Group G] where
  tr : Fin 16 → G
  sec : Fin 8 → G
  coc : Fin 8 → Fin 8 → Fin 16
  tr_xor : ∀ u v, tr (xor16 u v) = tr u * tr v
  sec_zero : sec 0 = 1
  conj : ∀ (j : Fin 8) (w : Fin 16), sec j * tr w = tr (Dg j w) * sec j
  sec_mul : ∀ j k, sec j * sec k = tr (coc j k) * sec (mulIdx j k)
  decomp : ∀ g : G, ∃ (v : Fin 16) (k : Fin 8), g = tr v * sec k
  uniq : ∀ (v : Fin 16) (k : Fin 8) (v' : Fin 16) (k' : Fin 8),
    tr v * sec k = tr v' * sec k' → v = v' ∧ k = k'

@[expose] def IsCocyc (f : Fin 8 → Fin 8 → Fin 16) : Prop :=
  (∀ k, f 0 k = 0) ∧ (∀ j, f j 0 = 0) ∧
    ∀ j k l, xor16 (f j k) (f (mulIdx j k) l) = xor16 (Dg j (f k l)) (f j (mulIdx k l))

namespace ExtDat

variable {G : Type*} [Group G] (A : ExtDat G)

theorem tr_zero : A.tr 0 = 1 := by
  have h := A.tr_xor 0 0
  rw [x16_self] at h
  have h2 : A.tr 0 * A.tr 0 = A.tr 0 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem tr_inj {u v : Fin 16} (h : A.tr u = A.tr v) : u = v := by
  have := A.uniq u 0 v 0 (by rw [A.sec_zero, mul_one, mul_one]; exact h)
  exact this.1

theorem mul_formula (v w : Fin 16) (j k : Fin 8) :
    (A.tr v * A.sec j) * (A.tr w * A.sec k) =
      A.tr (xor16 v (xor16 (Dg j w) (A.coc j k))) * A.sec (mulIdx j k) := by
  calc (A.tr v * A.sec j) * (A.tr w * A.sec k)
      = A.tr v * ((A.sec j * A.tr w) * A.sec k) := by simp only [mul_assoc]
    _ = A.tr v * ((A.tr (Dg j w) * A.sec j) * A.sec k) := by rw [A.conj]
    _ = A.tr v * (A.tr (Dg j w) * (A.sec j * A.sec k)) := by simp only [mul_assoc]
    _ = A.tr v * (A.tr (Dg j w) * (A.tr (A.coc j k) * A.sec (mulIdx j k))) := by
        rw [A.sec_mul]
    _ = (A.tr v * (A.tr (Dg j w) * A.tr (A.coc j k))) * A.sec (mulIdx j k) := by
        simp only [mul_assoc]
    _ = A.tr (xor16 v (xor16 (Dg j w) (A.coc j k))) * A.sec (mulIdx j k) := by
        rw [A.tr_xor, A.tr_xor]

theorem cocycle (j k l : Fin 8) :
    xor16 (A.coc j k) (A.coc (mulIdx j k) l) =
      xor16 (Dg j (A.coc k l)) (A.coc j (mulIdx k l)) := by
  have h1 : (A.sec j * A.sec k) * A.sec l =
      A.tr (xor16 (A.coc j k) (A.coc (mulIdx j k) l)) * A.sec (mulIdx (mulIdx j k) l) := by
    calc (A.sec j * A.sec k) * A.sec l
        = (A.tr (A.coc j k) * A.sec (mulIdx j k)) * A.sec l := by rw [A.sec_mul j k]
      _ = A.tr (A.coc j k) * (A.sec (mulIdx j k) * A.sec l) := by simp only [mul_assoc]
      _ = A.tr (A.coc j k) * (A.tr (A.coc (mulIdx j k) l) * A.sec (mulIdx (mulIdx j k) l)) := by
          rw [A.sec_mul (mulIdx j k) l]
      _ = (A.tr (A.coc j k) * A.tr (A.coc (mulIdx j k) l)) * A.sec (mulIdx (mulIdx j k) l) := by
          simp only [mul_assoc]
      _ = A.tr (xor16 (A.coc j k) (A.coc (mulIdx j k) l)) * A.sec (mulIdx (mulIdx j k) l) := by
          rw [A.tr_xor]
  have h2 : A.sec j * (A.sec k * A.sec l) =
      A.tr (xor16 (Dg j (A.coc k l)) (A.coc j (mulIdx k l))) * A.sec (mulIdx j (mulIdx k l)) := by
    calc A.sec j * (A.sec k * A.sec l)
        = A.sec j * (A.tr (A.coc k l) * A.sec (mulIdx k l)) := by rw [A.sec_mul k l]
      _ = (A.sec j * A.tr (A.coc k l)) * A.sec (mulIdx k l) := by simp only [mul_assoc]
      _ = (A.tr (Dg j (A.coc k l)) * A.sec j) * A.sec (mulIdx k l) := by rw [A.conj]
      _ = A.tr (Dg j (A.coc k l)) * (A.sec j * A.sec (mulIdx k l)) := by simp only [mul_assoc]
      _ = A.tr (Dg j (A.coc k l)) * (A.tr (A.coc j (mulIdx k l)) * A.sec (mulIdx j (mulIdx k l))) := by
          rw [A.sec_mul j (mulIdx k l)]
      _ = (A.tr (Dg j (A.coc k l)) * A.tr (A.coc j (mulIdx k l))) * A.sec (mulIdx j (mulIdx k l)) := by
          simp only [mul_assoc]
      _ = A.tr (xor16 (Dg j (A.coc k l)) (A.coc j (mulIdx k l))) * A.sec (mulIdx j (mulIdx k l)) := by
          rw [A.tr_xor]
  have h3 := (mul_assoc (A.sec j) (A.sec k) (A.sec l))
  exact (A.uniq _ _ _ _ (h1.symm.trans (h3.trans h2))).1

theorem coc_zero_left (k : Fin 8) : A.coc 0 k = 0 := by
  have h := A.sec_mul 0 k
  rw [A.sec_zero, one_mul, mulIdx_zero_left] at h
  have h2 : A.tr (A.coc 0 k) * A.sec k = A.tr 0 * A.sec k := by rw [A.tr_zero, one_mul]; exact h.symm
  exact (A.uniq _ _ _ _ h2).1

theorem coc_zero_right (j : Fin 8) : A.coc j 0 = 0 := by
  have h := A.sec_mul j 0
  rw [A.sec_zero, mul_one, mulIdx_zero_right] at h
  have h2 : A.tr (A.coc j 0) * A.sec j = A.tr 0 * A.sec j := by rw [A.tr_zero, one_mul]; exact h.symm
  exact (A.uniq _ _ _ _ h2).1

theorem isCocyc :
    IsCocyc A.coc := ⟨A.coc_zero_left, A.coc_zero_right, A.cocycle⟩

theorem invol {v : Fin 16} {k : Fin 8} (hk : mulIdx k k = 0)
    (h : (A.tr v * A.sec k) * (A.tr v * A.sec k) = 1) :
    xor16 v (xor16 (Dg k v) (A.coc k k)) = 0 := by
  rw [A.mul_formula, hk, A.sec_zero, mul_one] at h
  have h2 : A.tr (xor16 v (xor16 (Dg k v) (A.coc k k))) = A.tr 0 := by rw [A.tr_zero]; exact h
  exact A.tr_inj h2

end ExtDat

section Iso

variable {G H : Type*} [Group G] [Group H] (A : ExtDat G) (B : ExtDat H)

noncomputable def ExtDat.dv (A : ExtDat G) (g : G) : Fin 16 := (A.decomp g).choose

noncomputable def ExtDat.dk (A : ExtDat G) (g : G) : Fin 8 := (A.decomp g).choose_spec.choose

theorem ExtDat.dvk_spec (A : ExtDat G) (g : G) : g = A.tr (A.dv g) * A.sec (A.dk g) :=
  (A.decomp g).choose_spec.choose_spec

theorem ExtDat.dvk_eq (A : ExtDat G) (v : Fin 16) (k : Fin 8) :
    A.dv (A.tr v * A.sec k) = v ∧ A.dk (A.tr v * A.sec k) = k :=
  A.uniq _ _ _ _ (A.dvk_spec (A.tr v * A.sec k)).symm

noncomputable def ExtDat.isoFun (b : Fin 8 → Fin 16) (g : G) : H :=
  B.tr (xor16 (A.dv g) (b (A.dk g))) * B.sec (A.dk g)

theorem ExtDat.isoFun_apply (b : Fin 8 → Fin 16) (v : Fin 16) (k : Fin 8) :
    ExtDat.isoFun A B b (A.tr v * A.sec k) = B.tr (xor16 v (b k)) * B.sec k := by
  unfold ExtDat.isoFun
  rw [(A.dvk_eq v k).1, (A.dvk_eq v k).2]

theorem ExtDat.isoFun_mul (b : Fin 8 → Fin 16)
    (hb : ∀ j k, xor16 (A.coc j k) (B.coc j k) = xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k))))
    (g g' : G) :
    ExtDat.isoFun A B b (g * g') = ExtDat.isoFun A B b g * ExtDat.isoFun A B b g' := by
  obtain ⟨v, j, rfl⟩ := A.decomp g
  obtain ⟨w, k, rfl⟩ := A.decomp g'
  rw [A.mul_formula, ExtDat.isoFun_apply, ExtDat.isoFun_apply, ExtDat.isoFun_apply, B.mul_formula,
    Dg_lin, key_alg v (Dg j w) (A.coc j k) (B.coc j k) (b j) (Dg j (b k)) (b (mulIdx j k)) (hb j k)]

theorem ExtDat.isoFun_injective (b : Fin 8 → Fin 16) : Function.Injective (ExtDat.isoFun A B b) := by
  intro g g' h
  unfold ExtDat.isoFun at h
  obtain ⟨h1, h2⟩ := B.uniq _ _ _ _ h
  rw [h2] at h1
  have h3 : A.dv g = A.dv g' := by
    have := congrArg (fun a => xor16 a (b (A.dk g'))) h1
    simpa only [x16_cancel] using this
  calc g = A.tr (A.dv g) * A.sec (A.dk g) := A.dvk_spec g
    _ = A.tr (A.dv g') * A.sec (A.dk g') := by rw [h3, h2]
    _ = g' := (A.dvk_spec g').symm

theorem ExtDat.isoFun_surjective (b : Fin 8 → Fin 16) : Function.Surjective (ExtDat.isoFun A B b) := by
  intro h
  obtain ⟨u, k, rfl⟩ := B.decomp h
  refine ⟨A.tr (xor16 u (b k)) * A.sec k, ?_⟩
  rw [ExtDat.isoFun_apply, x16_cancel]

theorem ExtDat.iso (b : Fin 8 → Fin 16)
    (hb : ∀ j k, xor16 (A.coc j k) (B.coc j k) = xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) :
    ∃ ψ : G ≃* H, ∀ v k, ψ (A.tr v * A.sec k) = B.tr (xor16 v (b k)) * B.sec k := by
  have h1 : ExtDat.isoFun A B b 1 = 1 := by
    have h := ExtDat.isoFun_mul A B b hb 1 1
    rw [mul_one] at h
    have h2 : ExtDat.isoFun A B b 1 * ExtDat.isoFun A B b 1 = ExtDat.isoFun A B b 1 * 1 := by
      rw [mul_one]
      exact h.symm
    exact mul_left_cancel h2
  let φ : G →* H :=
    { toFun := ExtDat.isoFun A B b
      map_one' := h1
      map_mul' := ExtDat.isoFun_mul A B b hb }
  refine ⟨MulEquiv.ofBijective φ ⟨ExtDat.isoFun_injective A B b, ExtDat.isoFun_surjective A B b⟩,
    fun v k => ?_⟩
  exact ExtDat.isoFun_apply A B b v k

end Iso

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1
