module

public import Certificates.Data.Kernel.WittFix
public import CFSG.Certificates.Kernel.WittCntSound

public section

namespace CFSG.KC.WCnt

open CFSG.KC.Enum CFSG.KS.PCnt

theorem fixCk_eq (y : Nat) : ∀ k, fixCk y k = ((Finset.range k).filter fun i => pt y i = i).card
  | 0 => rfl
  | k + 1 => by
    have h : fixCk y (k + 1) = Bool.rec (motive := fun _ => Nat) (fixCk y k)
        (Nat.succ (fixCk y k)) (Nat.beq (pt y k) k) := rfl
    rw [h, Finset.range_add_one, Finset.filter_insert, fixCk_eq y k]
    cases hb : Nat.beq (pt y k) k
    · have hne : pt y k ≠ k := fun he => by rw [he, Nat.beq_refl] at hb; exact absurd hb (by decide)
      simp [hne]
    · have he : pt y k = k := Nat.eq_of_beq_eq_true hb
      simp only [he, if_true]
      rw [Finset.card_insert_of_notMem (by simp)]

theorem fixC_pkw (τ : Equiv.Perm (Fin 22)) :
    fixC (pkw 5 τ) = (Finset.univ.filter fun p => τ p = p).card := by
  unfold fixC
  rw [fixCk_eq, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
    have e := pt_pkw τ ⟨i, hi⟩
    simp only at e
    rw [← e, h]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.isLt, ?_⟩
    rw [pt_pkw, hp]

theorem fixL_iff (y : Nat) : ∀ l : List Nat, fixL l y = true ↔ ∀ i ∈ l, pt y i = i
  | [] => by simp [fixL]
  | i :: l => by
    have h : fixL (i :: l) y = (Nat.beq (pt y i) i && fixL l y) := by
      change Bool.rec (motive := fun _ => Bool) false (fixL l y) (Nat.beq (pt y i) i) = _
      cases Nat.beq (pt y i) i <;> rfl
    rw [h, Bool.and_eq_true, fixL_iff y l, List.forall_mem_cons, Nat.beq_eq]

theorem fixL_pkw (τ : Equiv.Perm (Fin 22)) {l : List Nat} (hl : ∀ i ∈ l, i < 22) :
    fixL l (pkw 5 τ) = true ↔ ∀ i ∈ l, ∀ h : i < 22, τ ⟨i, h⟩ = ⟨i, h⟩ := by
  rw [fixL_iff]
  constructor
  · intro H i hi h
    refine Fin.ext ?_
    have e := pt_pkw τ ⟨i, h⟩
    simp only at e
    rw [← e, H i hi]
  · intro H i hi
    have h := hl i hi
    have e := pt_pkw τ ⟨i, h⟩
    simp only at e
    rw [e, H i hi h]

theorem fourB_pkw (τ : Equiv.Perm (Fin 22)) :
    fourB (pkw 5 τ) = decide (∀ p, τ (τ (τ (τ p))) = p) := by
  rw [Bool.eq_iff_iff, fourB, allB_iff, decide_eq_true_iff]
  constructor
  · intro h p
    have h1 := Nat.eq_of_beq_eq_true (h p.val p.isLt)
    rw [pt_pkw, pt_pkw, pt_pkw, pt_pkw] at h1
    exact Fin.ext h1
  · intro h i hi
    have e : pt (pkw 5 τ) i = (τ ⟨i, hi⟩).val := pt_pkw τ ⟨i, hi⟩
    rw [e, pt_pkw, pt_pkw, pt_pkw, h]
    exact Nat.beq_refl _

theorem pwp_pkw {a b : Equiv.Perm (Fin 22)} {A B I : Nat} (hA : pkw 5 a = A) (hB : pkw 5 b = B)
    (hI : pkw 5 (1 : Equiv.Perm (Fin 22)) = I) :
    ∀ w : List Bool, pkw 5 (w.foldr (fun c g => (if c then b else a) * g) 1) = pwp A B I w
  | [] => hI.symm ▸ rfl
  | c :: w => by
    have h : pwp A B I (c :: w) = strictN (pwp A B I w) (fun g =>
        pcomp (nat_lit 22) (nat_lit 5) (nat_lit 31) (Bool.rec (motive := fun _ => Nat) A B c) g) :=
      rfl
    rw [h, strictN_eq', ← pwp_pkw hA hB hI w, List.foldr_cons]
    have hm := pkw_mul (n := 22) (w := 5) (by norm_num) (by norm_num) (if c then b else a)
      (w.foldr (fun c g => (if c then b else a) * g) 1)
    rw [mask_five] at hm
    rw [← hm]
    cases c
    · simp [hA]
    · simp [hB]

end CFSG.KC.WCnt

end
