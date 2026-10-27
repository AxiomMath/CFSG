module

public import Certificates.Data.SolMaxNineE32
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.SolMax.NineE32

open Equiv

abbrev W := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

@[expose] def tW : W := (0, 0, 0, 0, 1)

@[expose] def sW : W := (1, 0, 1, 0, 1)

@[expose] def mW : W := (1, 0, 1, 0, 0)

@[expose] def bitOf (n k : ℕ) : ZMod 2 := if n.testBit k then 1 else 0

@[expose] def ofMask (n : ℕ) : W := (bitOf n 0, bitOf n 1, bitOf n 2, bitOf n 3, bitOf n 4)

@[expose] def mask (v : W) : ℕ :=
  v.1.val + 2 * v.2.1.val + 4 * v.2.2.1.val + 8 * v.2.2.2.1.val + 16 * v.2.2.2.2.val

theorem ofMask_mask : ∀ v : W, ofMask (mask v) = v := by decide

theorem mask_add : ∀ v w : W, mask (v + w) = mask v ^^^ mask w := by decide

theorem mask_zero : mask 0 = 0 := by decide

@[expose] def eW (k : ℕ) : W := ofMask (2 ^ k)

theorem eq_sum_bits : ∀ v : W, v = (if (mask v).testBit 0 then eW 0 else 0) +
    (if (mask v).testBit 1 then eW 1 else 0) + (if (mask v).testBit 2 then eW 2 else 0) +
    (if (mask v).testBit 3 then eW 3 else 0) + (if (mask v).testBit 4 then eW 4 else 0) := by
  decide

theorem applyCols_eq (c : ℕ → W) (m : ℕ) :
    applyCols [mask (c 0), mask (c 1), mask (c 2), mask (c 3), mask (c 4)] m =
      mask ((if m.testBit 0 then c 0 else 0) + (if m.testBit 1 then c 1 else 0) +
        (if m.testBit 2 then c 2 else 0) + (if m.testBit 3 then c 3 else 0) +
        (if m.testBit 4 then c 4 else 0)) := by
  simp only [applyCols, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  simp only [mask_add]
  split_ifs <;> simp [mask_zero]

theorem mask_eq_applyCols (f : W → W) (hf : ∀ v w, f (v + w) = f v + f w) (v : W) :
    mask (f v) = applyCols [mask (f (eW 0)), mask (f (eW 1)), mask (f (eW 2)), mask (f (eW 3)),
      mask (f (eW 4))] (mask v) := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero] at h
    have h2 : f 0 + f 0 = f 0 + 0 := by rw [add_zero, ← h]
    exact (add_left_cancel h2)
  have hite : ∀ (b : Bool) (x : W), f (if b then x else 0) = if b then f x else 0 := by
    intro b x
    cases b <;> simp [h0]
  rw [applyCols_eq (fun k => f (eW k))]
  conv_lhs => rw [eq_sum_bits v]
  rw [hf, hf, hf, hf, hite, hite, hite, hite, hite]

@[expose] def pw (x : Perm (Fin 9)) (c : ZMod 2) : Perm (Fin 9) := if c = 1 then x else 1

@[expose] def encPerm (v : W) : Perm (Fin 9) :=
  pw (aPerm 0) v.1 * pw (aPerm 1) v.2.1 * pw (aPerm 2) v.2.2.1 * pw (aPerm 3) v.2.2.2.1

theorem encPerm_add : ∀ v w : W, encPerm (v + w) = encPerm v * encPerm w := by decide

@[expose] def decodeW (p : Perm (Fin 9)) (c : ZMod 2) : W :=
  (bitOf (p 0).val 0, bitOf (p 0).val 1, bitOf ((p 4).val - 4) 0, bitOf ((p 4).val - 4) 1, c)

theorem decodeW_encPerm : ∀ v : W, decodeW (encPerm v) v.2.2.2.2 = v := by decide

theorem aPerm_mem (i : Fin 4) : aPerm i ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases i <;>
    simp [aPerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem pw_mem {x : Perm (Fin 9)} (hx : x ∈ alternatingGroup (Fin 9)) (c : ZMod 2) :
    pw x c ∈ alternatingGroup (Fin 9) := by
  unfold pw
  split_ifs
  · exact hx
  · exact one_mem _

theorem encPerm_mem (v : W) : encPerm v ∈ alternatingGroup (Fin 9) :=
  mul_mem (mul_mem (mul_mem (pw_mem (aPerm_mem 0) _) (pw_mem (aPerm_mem 1) _))
    (pw_mem (aPerm_mem 2) _)) (pw_mem (aPerm_mem 3) _)

@[expose] def enc : Multiplicative W →* alternatingGroup (Fin 9) × Multiplicative (ZMod 2) where
  toFun v := (⟨encPerm (Multiplicative.toAdd v), encPerm_mem _⟩,
    Multiplicative.ofAdd (Multiplicative.toAdd v).2.2.2.2)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) rfl
    show encPerm 0 = 1
    decide
  map_mul' v w := by
    refine Prod.ext (Subtype.ext ?_) rfl
    exact encPerm_add (Multiplicative.toAdd v) (Multiplicative.toAdd w)

theorem enc_apply_fst (v : Multiplicative W) :
    ((enc v).1 : Perm (Fin 9)) = encPerm (Multiplicative.toAdd v) := rfl

theorem enc_apply_snd (v : Multiplicative W) :
    (enc v).2 = Multiplicative.ofAdd (Multiplicative.toAdd v).2.2.2.2 := rfl

theorem enc_injective : Function.Injective enc := by
  intro v w h
  have h1 : encPerm (Multiplicative.toAdd v) = encPerm (Multiplicative.toAdd w) :=
    congrArg (fun p => ((p.1 : alternatingGroup (Fin 9)) : Perm (Fin 9))) h
  have h2 : (Multiplicative.toAdd v).2.2.2.2 = (Multiplicative.toAdd w).2.2.2.2 :=
    congrArg (fun p : alternatingGroup (Fin 9) × Multiplicative (ZMod 2) =>
      Multiplicative.toAdd p.2) h
  have := decodeW_encPerm (Multiplicative.toAdd v)
  rw [h1, h2, decodeW_encPerm] at this
  exact Multiplicative.toAdd.injective this.symm

theorem enc_tW : enc (Multiplicative.ofAdd tW) = (1, Multiplicative.ofAdd 1) := by
  refine Prod.ext (Subtype.ext ?_) rfl
  show encPerm tW = 1
  decide

@[expose] def A₀ : Subgroup (alternatingGroup (Fin 9) × Multiplicative (ZMod 2)) := enc.range

theorem card_A₀ : Nat.card A₀ = 32 := by
  have h := Nat.card_congr (MonoidHom.ofInjective enc_injective).toEquiv
  show Nat.card enc.range = 32
  rw [← h, Nat.card_eq_fintype_card]
  rfl

@[expose] def isM (v : W) : Prop := (encPerm v).support.card = 8 ∧ v.2.2.2.2 = 0

@[expose] def isTM (v : W) : Prop := (encPerm v).support.card = 8 ∧ v.2.2.2.2 = 1

instance (v : W) : Decidable (isM v) := by unfold isM; infer_instance

instance (v : W) : Decidable (isTM v) := by unfold isTM; infer_instance

theorem type_cases : ∀ v : W, v = 0 ∨ v = tW ∨ (encPerm v).support.card = 4 ∨ isM v ∨ isTM v := by
  decide

theorem isM_mW : isM mW := by decide

theorem isTM_sW : isTM sW := by decide

@[expose] def xPerm : Fin 4 → Perm (Fin 9) :=
  ![swap 0 1 * swap 1 2, swap 4 5 * swap 5 6, swap 0 1 * swap 4 5,
    swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7]

theorem xPerm_mem (i : Fin 4) : xPerm i ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  fin_cases i <;>
    simp [xPerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

@[expose] def gW (i : ℕ) (v : W) : W := ofMask (applyCols (gColsN.getD i []) (mask v))

theorem xPerm_conj : ∀ (i : Fin 4) (v : W),
    xPerm i * encPerm v * (xPerm i)⁻¹ = encPerm (gW i v) := by
  decide

theorem gW_snd : ∀ (i : Fin 4) (v : W), (gW i v).2.2.2.2 = v.2.2.2.2 := by decide

@[expose] def gWord (w : List ℕ) (v : W) : W := w.foldr gW v

@[expose] def wordsM : List (ℕ × List ℕ) :=
  [(5, []), (6, [0, 0]), (7, [0]), (9, [1, 1]), (10, [2, 1, 0]), (11, [1, 1, 0]), (13, [1]),
    (14, [1, 0, 0]), (15, [1, 0])]

@[expose] def wordsTM : List (ℕ × List ℕ) :=
  [(21, []), (22, [0, 0]), (23, [0]), (25, [1, 1]), (26, [2, 1, 0]), (27, [1, 1, 0]),
    (29, [1]), (30, [1, 0, 0]), (31, [1, 0])]

@[expose] def wordAt (l : List (ℕ × List ℕ)) (v : W) : List ℕ :=
  ((l.find? fun e => e.1 == mask v).map (·.2)).getD []

theorem gWord_wordsM : ∀ v : W, isM v → gWord (wordAt wordsM v) mW = v := by decide

theorem gWord_wordsTM : ∀ v : W, isTM v → gWord (wordAt wordsTM v) sW = v := by decide

theorem wordAt_lt (l : List (ℕ × List ℕ)) (hl : ∀ e ∈ l, ∀ i ∈ e.2, i < 4) (v : W) :
    ∀ i ∈ wordAt l v, i < 4 := by
  intro i hi
  unfold wordAt at hi
  cases h : l.find? (fun e => e.1 == mask v) with
  | none => simp [h] at hi
  | some e =>
    simp only [h, Option.map_some, Option.getD_some] at hi
    exact hl e (List.mem_of_find?_eq_some h) i hi

theorem wordsM_lt : ∀ e ∈ wordsM, ∀ i ∈ e.2, i < 4 := by decide

theorem wordsTM_lt : ∀ e ∈ wordsTM, ∀ i ∈ e.2, i < 4 := by decide

@[expose] def nO (O : W → Prop) [DecidablePred O] (x : W) : ℕ :=
  (Finset.univ.filter fun y => O y ∧ O (x + y)).card

@[expose] def O₃ (y : W) : Prop := y = tW ∨ isM y ∨ isTM y

@[expose] def Om (y : W) : Prop := y = tW ∨ isM y

instance : DecidablePred O₃ := fun y => by unfold O₃; infer_instance

instance : DecidablePred Om := fun y => by unfold Om; infer_instance

theorem nO₃_tW : nO O₃ tW = 18 := by decide

theorem nO₃_mW : nO O₃ mW = 10 := by decide

theorem nO₃_sW : nO O₃ sW = 10 := by decide

theorem nOm_tW : nO Om tW = 0 := by decide

theorem nOm_mW : nO Om mW = 4 := by decide

theorem nO_eq (O : W → Prop) [DecidablePred O] (ψ : W ≃+ W) (hψ : ∀ y, O (ψ y) ↔ O y) (x : W) :
    nO O (ψ x) = nO O x := by
  unfold nO
  refine Finset.card_bij (fun y _ => ψ.symm y) (fun y hy => ?_) (fun y _ y' _ h => ?_)
    (fun y hy => ⟨ψ y, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨(hψ _).mp (by simpa using hy.1), (hψ _).mp ?_⟩
    simpa [map_add] using hy.2
  · exact ψ.symm.injective h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨(hψ _).mpr hy.1, ?_⟩
    rw [← map_add]
    exact (hψ _).mpr hy.2
  · simp

@[expose] def oddP (j : ℕ) : Perm (Fin 9) := permOf (oddPerm.getD j [])

theorem oddPerm_conj : ∀ (j : Fin 36) (i : Fin 4),
    oddP j * aPerm i * (oddP j)⁻¹ = encPerm (ofMask ((oddColsN.getD j []).getD i 0)) := by
  decide

theorem oddPerm_shape : ∀ j : Fin 36,
    (oddPerm.getD j []).length % 2 = 1 ∧ ∀ p ∈ oddPerm.getD j [], p.1 ≠ p.2 := by
  decide

theorem sign_permOf (l : List (Fin 9 × Fin 9)) (hl : ∀ p ∈ l, p.1 ≠ p.2) :
    Perm.sign (permOf l) = (-1) ^ l.length := by
  induction l with
  | nil => simp [permOf]
  | cons p l ih =>
    have hp := hl p (List.mem_cons_self ..)
    have ih' := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [permOf, List.map_cons, List.prod_cons] at ih' ⊢
    rw [map_mul, Equiv.Perm.sign_swap hp, ih', List.length_cons, pow_succ, mul_comm]

theorem sign_oddP (j : Fin 36) : Perm.sign (oddP j) = -1 := by
  obtain ⟨h1, h2⟩ := oddPerm_shape j
  rw [oddP, sign_permOf _ h2]
  obtain ⟨k, hk⟩ : ∃ k, (oddPerm.getD j []).length = 2 * k + 1 :=
    ⟨_, (Nat.div_add_mod _ 2).symm.trans (by rw [h1])⟩
  rw [hk, pow_succ, pow_mul]
  simp

@[expose] def carry (ω : Fin 9) : Perm (Fin 9) :=
  ![1, aPerm 0, aPerm 1, aPerm 0 * aPerm 1, 1, aPerm 2, aPerm 3, aPerm 2 * aPerm 3, 1] ω

@[expose] def cand (i j : Fin 9) (ω : Fin 9) : Fin 9 :=
  if (ω : ℕ) < 4 then carry ω i else if (ω : ℕ) < 8 then carry ω j else 8

theorem sign_cand : ∀ i j : Fin 9, ∀ h : Function.Bijective (cand i j),
    Perm.sign (Equiv.ofBijective _ h) = 1 := by
  decide

theorem carry_cases : ∀ ω : Fin 9, carry ω = 1 ∨ carry ω = aPerm 0 ∨ carry ω = aPerm 1 ∨
    carry ω = aPerm 0 * aPerm 1 ∨ carry ω = aPerm 2 ∨ carry ω = aPerm 3 ∨
    carry ω = aPerm 2 * aPerm 3 := by
  decide

theorem carry_apply : ∀ ω : Fin 9, ((ω : ℕ) < 4 → carry ω 0 = ω) ∧
    ((4 ≤ (ω : ℕ) ∧ (ω : ℕ) < 8) → carry ω 4 = ω) := by
  decide

theorem fixed_eight : ∀ x : Fin 9, (∀ i : Fin 4, aPerm i x = x) → x = 8 := by decide

theorem sign_eq_one_of_commute (y : Perm (Fin 9)) (hy : ∀ i : Fin 4, y * aPerm i = aPerm i * y) :
    Perm.sign y = 1 := by
  have hc : ∀ ω : Fin 9, y * carry ω = carry ω * y := by
    intro ω
    rcases carry_cases ω with h | h | h | h | h | h | h <;> rw [h]
    · rw [mul_one, one_mul]
    · exact hy 0
    · exact hy 1
    · rw [← mul_assoc, hy 0, mul_assoc, hy 1, mul_assoc]
    · exact hy 2
    · exact hy 3
    · rw [← mul_assoc, hy 2, mul_assoc, hy 3, mul_assoc]
  have h8 : y 8 = 8 := by
    apply fixed_eight
    intro i
    have := congrArg (fun p : Perm (Fin 9) => p 8) (hy i)
    simp only [Perm.mul_apply] at this
    have h8' : aPerm i 8 = 8 := by fin_cases i <;> decide
    rw [h8'] at this
    exact this.symm
  have hfun : ∀ ω, y ω = cand (y 0) (y 4) ω := by
    intro ω
    unfold cand
    split_ifs with h1 h2
    · have := congrArg (fun p : Perm (Fin 9) => p 0) (hc ω)
      simp only [Perm.mul_apply] at this
      rw [(carry_apply ω).1 h1] at this
      exact this
    · have := congrArg (fun p : Perm (Fin 9) => p 4) (hc ω)
      simp only [Perm.mul_apply] at this
      rw [(carry_apply ω).2 ⟨not_lt.mp h1, h2⟩] at this
      exact this
    · have hω : ω = 8 := by
        apply Fin.ext
        have := ω.2
        omega
      rw [hω, h8]
  have hbij : Function.Bijective (cand (y 0) (y 4)) := by
    have : cand (y 0) (y 4) = y := funext fun ω => (hfun ω).symm
    rw [this]
    exact y.bijective
  have hy' : y = Equiv.ofBijective _ hbij := Equiv.ext fun ω => hfun ω
  rw [hy']
  exact sign_cand _ _ hbij

end CFSG.ComponentClassification.SolMax.NineE32
