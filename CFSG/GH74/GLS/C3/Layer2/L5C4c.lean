module

public import CFSG.GH74.GLS.C3.Layer2.L5C4b
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
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4b
public import CFSG.GH74.GLS.C3.Layer2.L5C4cInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C4cInputs
public import Certificates.Certificate5064

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Rec1

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def evalF (x : Nat → Bool) (m : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (evalF x m n) (m.testBit n && x n)

theorem evalF_xor (x : Nat → Bool) (a b : Nat) :
    ∀ n, evalF x (a ^^^ b) n = xor (evalF x a n) (evalF x b n)
  | 0 => rfl
  | n + 1 => by
      simp only [evalF, Nat.testBit_xor, evalF_xor x a b n]
      generalize evalF x a n = e1
      generalize evalF x b n = e2
      generalize a.testBit n = t1
      generalize b.testBit n = t2
      generalize x n = x0
      revert e1 e2 t1 t2 x0
      decide

theorem evalF_zero (x : Nat → Bool) : ∀ n, evalF x 0 n = false
  | 0 => rfl
  | n + 1 => by simp [evalF, evalF_zero x n]

theorem evalF_pow (x : Nat → Bool) (p : Nat) :
    ∀ n, evalF x (2 ^ p) n = (decide (p < n) && x p)
  | 0 => by simp [evalF]
  | n + 1 => by
      rw [evalF, evalF_pow x p n, Nat.testBit_two_pow]
      rcases lt_trichotomy p n with h | h | h
      · have h1 : p < n + 1 := by omega
        have h2 : ¬ p = n := by omega
        simp [h, h1, h2]
      · subst h
        simp
      · have h1 : ¬ p < n + 1 := by omega
        have h2 : ¬ p < n := by omega
        have h3 : ¬ p = n := by omega
        simp [h1, h2, h3]

theorem evalF_tm (x : Nat → Bool) (b : Bool) (m n : Nat) :
    evalF x (tm b m) n = (b && evalF x m n) := by
  cases b <;> simp [tm, evalF_zero]

@[expose] def Entails (E : List Nat) (m : Nat) : Prop :=
  ∀ x : Nat → Bool, (∀ e ∈ E, evalF x e 256 = false) → evalF x m 256 = false

theorem Entails.xor' {E : List Nat} {a b : Nat} (ha : Entails E a) (hb : Entails E b) :
    Entails E (a ^^^ b) := by
  intro x hx
  rw [evalF_xor, ha x hx, hb x hx]
  rfl

theorem Entails.of_mem {E : List Nat} {e : Nat} (h : e ∈ E) : Entails E e :=
  fun _ hx => hx e h

theorem Entails.zero (E : List Nat) : Entails E 0 := fun x _ => evalF_zero x 256

theorem nxor_aux1 (a b c : Nat) : b ^^^ ((a ^^^ b) ^^^ c) = a ^^^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  generalize a.testBit i = x
  generalize b.testBit i = y
  generalize c.testBit i = z
  revert x y z
  decide

theorem nxor_aux2 (a b : Nat) : a ^^^ (a ^^^ b) = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  generalize a.testBit i = x
  generalize b.testBit i = y
  revert x y
  decide

theorem redF_spec (E : List Nat) :
    ∀ (B : List (Nat × Nat)), (∀ pr ∈ B, Entails E pr.2) → ∀ m, Entails E (m ^^^ redF B m)
  | [], _, m => by
      have : m ^^^ redF [] m = 0 := by simp [redF]
      rw [this]
      exact Entails.zero E
  | pr :: B, hB, m => by
      have hrest := redF_spec E B (fun q hq => hB q (List.mem_cons_of_mem _ hq))
      have hpr := hB pr (List.mem_cons_self ..)
      show Entails E (m ^^^ redF B (cond (m.testBit pr.1) (m ^^^ pr.2) m))
      cases h : m.testBit pr.1
      · simp only [Bool.cond_false]
        exact hrest m
      · simp only [Bool.cond_true]
        have h1 := hrest (m ^^^ pr.2)
        rw [← nxor_aux1 m pr.2 (redF B (m ^^^ pr.2))]
        exact hpr.xor' h1

theorem addRow_sound (E : List Nat) (B : List (Nat × Nat)) (hB : ∀ pr ∈ B, Entails E pr.2)
    (e : Nat) (he : Entails E e) : ∀ pr ∈ addRow B e, Entails E pr.2 := by
  have hr : Entails E (redF B e) := by
    have h1 := redF_spec E B hB e
    have h2 : redF B e = e ^^^ (e ^^^ redF B e) := (nxor_aux2 e (redF B e)).symm
    rw [h2]
    exact he.xor' h1
  intro pr hpr
  unfold addRow at hpr
  cases h : (redF B e == 0)
  · simp only [h, Bool.cond_false] at hpr
    rcases List.mem_cons.1 hpr with rfl | hpr
    · exact hr
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpr
      cases h2 : q.2.testBit (Nat.log2 (redF B e))
      · simp only [Bool.cond_false]
        exact hB q hq
      · simp only [Bool.cond_true]
        exact (hB q hq).xor' hr
  · simp only [h, Bool.cond_true] at hpr
    exact hB pr hpr

theorem foldl_addRow_sound (E₀ : List Nat) :
    ∀ (E : List Nat) (B : List (Nat × Nat)), (∀ pr ∈ B, Entails E₀ pr.2) → (∀ e ∈ E, e ∈ E₀) →
      ∀ pr ∈ E.foldl addRow B, Entails E₀ pr.2
  | [], _, hB, _ => hB
  | e :: E, B, hB, hE =>
      foldl_addRow_sound E₀ E (addRow B e)
        (addRow_sound E₀ B hB e (Entails.of_mem (hE e (List.mem_cons_self ..))))
        (fun e' he' => hE e' (List.mem_cons_of_mem _ he'))

theorem basisOf_sound (E : List Nat) : ∀ pr ∈ basisOf E, Entails E pr.2 :=
  foldl_addRow_sound E E [] (fun pr h => by simp at h) (fun e h => h)

theorem entails_of_redF (E : List Nat) (m : Nat) (h : redF (basisOf E) m = 0) : Entails E m := by
  have h1 := redF_spec E (basisOf E) (basisOf_sound E) m
  rw [h, Nat.xor_zero] at h1
  exact h1

@[expose] def bitOf (f : Fin 8 → Fin 8 → Fin 16) (p : Nat) : Bool :=
  (f ⟨p / 32 % 8, Nat.mod_lt _ (by decide)⟩ ⟨p / 4 % 8, Nat.mod_lt _ (by decide)⟩).val.testBit
    (p % 4)

theorem bitOf_vi (f : Fin 8 → Fin 8 → Fin 16) (j k : Fin 8) (c : Nat) (hc : c < 4) :
    bitOf f (vi j.val k.val c) = (f j k).val.testBit c := by
  have h1 : (vi j.val k.val c) / 32 % 8 = j.val := by unfold vi; omega
  have h2 : (vi j.val k.val c) / 4 % 8 = k.val := by unfold vi; omega
  have h3 : (vi j.val k.val c) % 4 = c := by unfold vi; omega
  have e1 : (⟨(vi j.val k.val c) / 32 % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = j := Fin.ext h1
  have e2 : (⟨(vi j.val k.val c) / 4 % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = k := Fin.ext h2
  unfold bitOf
  rw [e1, e2, h3]

theorem vi_lt (j k : Fin 8) (c : Nat) (hc : c < 4) : vi j.val k.val c < 256 := by
  have := j.isLt
  have := k.isLt
  unfold vi
  omega

theorem Dg_bit_chk :
    (List.finRange 8).all (fun j => (List.finRange 16).all fun v =>
    (List.finRange 4).all fun c =>
      decide ((Dg j v).val.testBit c.val =
        xor (xor (xor (Mj j c.val 0 && v.val.testBit 0) (Mj j c.val 1 && v.val.testBit 1))
          (Mj j c.val 2 && v.val.testBit 2)) (Mj j c.val 3 && v.val.testBit 3))) = true :=
  Certificates.certificate5064.1

theorem Dg_bit (j : Fin 8) (v : Fin 16) (c : Fin 4) :
    (Dg j v).val.testBit c.val =
      xor (xor (xor (Mj j c.val 0 && v.val.testBit 0) (Mj j c.val 1 && v.val.testBit 1))
        (Mj j c.val 2 && v.val.testBit 2)) (Mj j c.val 3 && v.val.testBit 3) := by
  have h := Dg_bit_chk
  simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq] at h
  exact h j trivial v trivial c trivial

theorem bool_aux (a b d e : Bool) (h : xor a b = xor d e) : xor (xor (xor a b) d) e = false := by
  revert a b d e
  decide

theorem evalF_bit (f : Fin 8 → Fin 8 → Fin 16) (a b : Fin 8) (c : Nat) (hc : c < 4) :
    evalF (bitOf f) (2 ^ vi a.val b.val c) 256 = (f a b).val.testBit c := by
  rw [evalF_pow, bitOf_vi f a b c hc]
  simp [vi_lt a b c hc]

theorem evalF_cocEq
    (f : Fin 8 → Fin 8 → Fin 16) (hf : IsCocyc f) (j k l : Fin 8) (c : Fin 4) :
    evalF (bitOf f) (cocEq j k l c.val) 256 = false := by
  have hd := Dg_bit j (f k l) c
  have hid := congrArg (fun a : Fin 16 => a.val.testBit c.val) (hf.2.2 j k l)
  simp only [x16_testBit] at hid
  have hc := c.isLt
  unfold cocEq dF
  simp only [evalF_xor, evalF_tm, evalF_bit f _ _ _ hc, evalF_bit f _ _ 0 (by norm_num),
    evalF_bit f _ _ 1 (by norm_num), evalF_bit f _ _ 2 (by norm_num),
    evalF_bit f _ _ 3 (by norm_num)]
  rw [← hd]
  exact bool_aux _ _ _ _ hid

theorem evalF_cocEqs (f : Fin 8 → Fin 8 → Fin 16) (hf : IsCocyc f) :
    ∀ e ∈ cocEqs, evalF (bitOf f) e 256 = false := by
  intro e he
  simp only [cocEqs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ⟨j, k, l, c, rfl⟩ | ⟨k, c, rfl | rfl⟩
  · exact evalF_cocEq f hf j k l c
  · have h := evalF_bit f (0 : Fin 8) k c.val c.isLt
    have h0 : evalF (bitOf f) (2 ^ vi (0 : Fin 8).val k.val c.val) 256 = false := by
      rw [h, hf.1 k]
      simp
    exact h0
  · have h := evalF_bit f k (0 : Fin 8) c.val c.isLt
    have h0 : evalF (bitOf f) (2 ^ vi k.val (0 : Fin 8).val c.val) 256 = false := by
      rw [h, hf.2.1 k]
      simp
    exact h0

@[expose] def ofBits4 (g : Fin 4 → Bool) : Fin 16 :=
  ⟨(if g 0 then 1 else 0) + (if g 1 then 2 else 0) + (if g 2 then 4 else 0) +
    (if g 3 then 8 else 0), by
    have h : ∀ a b c d : Bool, (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
        (if d then 8 else 0) < 16 := by decide
    exact h _ _ _ _⟩

theorem ofBits4_aux : ∀ a b c d : Bool,
    Nat.testBit ((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
      (if d then 8 else 0)) 0 = a ∧
    Nat.testBit ((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
      (if d then 8 else 0)) 1 = b ∧
    Nat.testBit ((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
      (if d then 8 else 0)) 2 = c ∧
    Nat.testBit ((if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
      (if d then 8 else 0)) 3 = d := by decide

theorem ofBits4_testBit (g : Fin 4 → Bool) (c : Fin 4) : (ofBits4 g).val.testBit c.val = g c := by
  obtain ⟨h0, h1, h2, h3⟩ := ofBits4_aux (g 0) (g 1) (g 2) (g 3)
  fin_cases c
  · exact h0
  · exact h1
  · exact h2
  · exact h3

@[expose] def sel : Bool → Fin 16 → Fin 16
  | true, u => u
  | false, _ => 0

theorem sel_bit (ε : Bool) (u : Fin 16) (c : Nat) :
    (sel ε u).val.testBit c = (ε && u.val.testBit c) := by
  cases ε <;> simp [sel]

theorem bool_fin (a e c bj d bjk : Bool) (h : xor a (xor (xor (xor (c && e) bj) d) bjk) = false) :
    a = xor (e && c) (xor bj (xor d bjk)) := by
  revert a e c bj d bjk
  decide

theorem fs_sound
    (c1 : Fin 8 → Fin 8 → Fin 16) (eF : Nat) (bF : List Nat)
    (h : fsCheck c1 eF bF = true) (f : Fin 8 → Fin 8 → Fin 16) (hf : IsCocyc f) :
    ∃ (ε : Bool) (b : Fin 8 → Fin 16), ∀ j k,
      f j k = xor16 (sel ε (c1 j k))
        (xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) := by
  have hchk : ∀ (j k : Fin 8) (c : Fin 4),
      redF cocBasis (2 ^ vi j.val k.val c.val ^^^ rhsForm c1 eF bF j k c.val) = 0 := by
    intro j k c
    simp only [fsCheck, List.all_eq_true, List.mem_finRange, beq_iff_eq] at h
    exact h j trivial k trivial c trivial
  have hE := evalF_cocEqs f hf
  refine ⟨evalF (bitOf f) eF 256,
    fun k => ofBits4 fun c => evalF (bitOf f) (bF.getD (k.val * 4 + c.val) 0) 256, fun j k => ?_⟩
  have hbb : ∀ (k : Fin 8) (c : Nat), c < 4 →
      (ofBits4 fun c : Fin 4 => evalF (bitOf f) (bF.getD (k.val * 4 + c.val) 0) 256).val.testBit c =
        evalF (bitOf f) (bF.getD (k.val * 4 + c) 0) 256 := fun k c hc =>
    ofBits4_testBit (fun c : Fin 4 => evalF (bitOf f) (bF.getD (k.val * 4 + c.val) 0) 256) ⟨c, hc⟩
  apply x16_ext
  intro c
  have hent : Entails cocEqs (2 ^ vi j.val k.val c.val ^^^ rhsForm c1 eF bF j k c.val) :=
    entails_of_redF cocEqs _ (hchk j k c)
  have h0 := hent (bitOf f) hE
  rw [evalF_xor, evalF_bit f j k c.val c.isLt] at h0
  unfold rhsForm at h0
  simp only [evalF_xor, evalF_tm] at h0
  rw [x16_testBit, x16_testBit, x16_testBit, Dg_bit j _ c, sel_bit]
  simp only [hbb _ _ c.isLt, hbb _ 0 (by norm_num), hbb _ 1 (by norm_num), hbb _ 2 (by norm_num),
    hbb _ 3 (by norm_num)]
  exact bool_fin _ _ _ _ _ _ h0

theorem fsCheck_cc1 :
    fsCheck cc1 eFdata bFdata = true :=
  Certificates.certificate5064.2

theorem fs_cc1 (f : Fin 8 → Fin 8 → Fin 16) (hf : IsCocyc f) :
    ∃ (ε : Bool) (b : Fin 8 → Fin 16), ∀ j k,
      f j k = xor16 (sel ε (cc1 j k))
        (xor16 (b j) (xor16 (Dg j (b k)) (b (mulIdx j k)))) :=
  fs_sound cc1 eFdata bFdata fsCheck_cc1 f hf

end CFSG.GH74.GLS.C3.Layer2.L5.Rec1
