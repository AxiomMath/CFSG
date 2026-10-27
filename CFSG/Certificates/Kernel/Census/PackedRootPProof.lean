module

public import Certificates.Data.Kernel.Census.PackedRootP
public import CFSG.Certificates.Kernel.Census.PackedLProof

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

theorem encE_val (x : Nat × Nat × Nat × Nat) :
    encE x = x.1 + 2 ^ 32 * (x.2.1 + 2 ^ 32 * (x.2.2.1 + 2 ^ 32 * x.2.2.2)) := by
  have h : encE x = x.1 + (x.2.1 + (x.2.2.1 + x.2.2.2 <<< 32) <<< 32) <<< 32 := rfl
  rw [h]
  simp only [Nat.shiftLeft_eq]
  ring

theorem packB_cons (x : Nat × Nat × Nat × Nat) (l : List (Nat × Nat × Nat × Nat)) :
    packB (x :: l) = encE x + 2 ^ 128 * packB l := by
  have h : packB (x :: l) = encE x + packB l <<< 128 := rfl
  rw [h, Nat.shiftLeft_eq, Nat.mul_comm]

theorem decE_val (P k : Nat) :
    decE P k = (P / 2 ^ (k * 128) % 2 ^ 32, P / 2 ^ (k * 128 + 32) % 2 ^ 32,
      P / 2 ^ (k * 128 + 64) % 2 ^ 32, P / 2 ^ (k * 128 + 96) % 2 ^ 32) := by
  have h : decE P k = ((P >>> (k <<< 7)) &&& 4294967295, (P >>> ((k <<< 7) + 32)) &&& 4294967295,
      (P >>> ((k <<< 7) + 64)) &&& 4294967295, (P >>> ((k <<< 7) + 96)) &&& 4294967295) := rfl
  have hm : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
  have hs : k <<< 7 = k * 128 := by rw [Nat.shiftLeft_eq]
  rw [h, hm, hs]
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

@[expose] def FitsE (x : Nat × Nat × Nat × Nat) : Prop :=
  x.1 < 4294967296 ∧ x.2.1 < 4294967296 ∧ x.2.2.1 < 4294967296 ∧ x.2.2.2 < 4294967296

theorem decE_zero (x : Nat × Nat × Nat × Nat) (R : Nat) (h : FitsE x) :
    decE (encE x + 2 ^ 128 * R) 0 = x := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨ha, hb, hc, hd⟩ := h
  simp only at ha hb hc hd
  rw [decE_val, encE_val]
  norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem encE_lt (x : Nat × Nat × Nat × Nat) (h : FitsE x) : encE x < 2 ^ 128 := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨ha, hb, hc, hd⟩ := h
  simp only at ha hb hc hd
  rw [encE_val]
  norm_num
  omega

theorem decE_succ (P k : Nat) : decE P (k + 1) = decE (P / 2 ^ 128) k := by
  have e : ∀ o, P / 2 ^ ((k + 1) * 128 + o) = P / 2 ^ 128 / 2 ^ (k * 128 + o) := by
    intro o
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    ring
  have e0 := e 0
  simp only [Nat.add_zero] at e0
  rw [decE_val, decE_val, e, e, e, e0]

theorem decE_packB (l : List (Nat × Nat × Nat × Nat)) (h : ∀ x ∈ l, FitsE x) (k : Nat) :
    decE (packB l) k = l.getD k default := by
  induction l generalizing k with
  | nil =>
    have h0 : packB [] = 0 := rfl
    rw [h0, decE_val]
    simp only [Nat.zero_div, Nat.zero_mod, List.getD_nil]
    rfl
  | cons x l ih =>
    have hx := h x (List.mem_cons_self ..)
    have hl : ∀ y ∈ l, FitsE y := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [packB_cons]
    cases k with
    | zero => rw [decE_zero x _ hx, List.getD_cons_zero]
    | succ k =>
      rw [decE_succ, List.getD_cons_succ, ← ih hl k]
      congr 1
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (encE_lt x hx), Nat.zero_add]

theorem fitsB_spec {bs : List (Array (Nat × Nat × Nat × Nat))} (h : fitsB bs = true) :
    ∀ b ∈ bs, ∀ x ∈ b.toList, FitsE x := by
  intro b hb x hx
  simp only [fitsB, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h b hb x hx
  exact ⟨h1, h2, h3, h4⟩

theorem ugetP_eq (bs : List (Array (Nat × Nat × Nat × Nat))) (h : ∀ b ∈ bs, ∀ x ∈ b.toList, FitsE x)
    (k : Nat) : ugetP (bs.map fun b => packB b.toList) (bs.map Array.size) k = uget bs k := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, ugetP, uget]
    cases hk : Nat.blt k b.size
    · exact ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) _
    · simp only [cond_true]
      rw [decE_packB _ (h b (List.mem_cons_self ..)), getElem!_eq_toList_getDL]

theorem withPacked_eq {β : Sort _} (bs : List (Array (Nat × Nat × Nat × Nat)))
    (k : List Nat → List Nat → β) :
    withPacked bs k = k (bs.map fun b => packB b.toList) (bs.map Array.size) := by
  unfold withPacked
  rw [strictLA_eq, strictLA_eq]

section Checks

variable {n w : Nat}

theorem pentryOKB_eqG (inX : Nat → Bool) (bmode : Nat) (skip : List Nat) (pG : Array (Array Nat))
    (k : Nat) (r : RootConjP) (j : Nat) :
    pentryOKB n w inX bmode skip pG k r j =
      pentryOKBG n w r.e (usize r.ukc) inX bmode skip pG k r j := by
  simp only [pentryOKB, pentryOKBG, getElem!_eq_toList_getDL]

theorem ugetP_e {r : RootConjP} (h : fitsB r.ukc = true) :
    ugetP (r.ukc.map fun b => packB b.toList) (r.ukc.map Array.size) = r.e :=
  funext fun k => ugetP_eq _ (fitsB_spec h) k

theorem pordBlkP_eq {r : RootConjP} (h : fitsB r.ukc = true) (a len : Nat) :
    pordBlkP n w r a len =
      (List.range' a len).all fun i => Nat.blt (pkeyU n w r i) (pkeyU n w r (i + 1)) := by
  unfold pordBlkP
  rw [withPacked_eq, ugetP_e h]
  rfl

theorem pentBlkP_eq {r : RootConjP} (h : fitsB r.ukc = true) {U : Nat} (hU : usize r.ukc = U)
    (inX : Nat → Bool) (skip : List Nat) (pG : Array (Array Nat)) (k a len : Nat) :
    pentBlkP n w U inX skip pG k r a len =
      (List.range' a len).all fun j =>
        bAnd(pentryOKB n w inX 2 skip pG k r j, pentryOKB n w inX 1 skip pG k r j) := by
  unfold pentBlkP
  rw [withPacked_eq, ugetP_e h]
  subst hU
  simp only [pentryOKB_eqG]

end Checks

end CFSG.KC.Census
